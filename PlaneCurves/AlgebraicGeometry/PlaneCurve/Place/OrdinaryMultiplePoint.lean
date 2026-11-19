/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.AffineSpace.Place
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.Blowup.Chart
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Place.ChangeOfCoordinates
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Place.SimplePoint
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.GenericLine
public import PlaneCurves.FieldTheory.FunctionField.Place.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Degree

/-!
# The places over an ordinary multiple point

Let `k` be an algebraically closed field and `F` an irreducible affine plane curve, other than the
line `X = 0`, with an ordinary multiple point at the origin at which `X = 0` is not tangent. Let
`K = k(F)` be its function field, `x, y` the coordinate functions, and `F'` the strict transform of
`F` under the blow-up of the origin, with function field `k(F') ≅ K` (`x ↦ x`, `z ↦ y / x`).

For every tangent `Y - α X` of `F` at the origin, the point `(0, α)` of the exceptional line is a
simple point of `F'`, so it has a place of `k(F')`; transported to `K`, it is a place
`blowupPlace` of `K` over the origin. These are all the places of `K` over the origin, one for each
tangent: if the valuation ring of a place `Q` contains `𝒪_0(F)`, then `z = y / x` is integral over
`𝒪_Q` (it is a root of the monic polynomial obtained from `F(x, xz) = x ^ r F'(x, z)`), so `𝒪_Q`
contains the coordinate ring of `F'`, and `Q` lies over a point `(0, α)` of `F'` on the
exceptional line, a simple point; the discrete valuation ring `𝒪_{(0, α)}(F')` is then the
valuation ring of `Q`. At each of these places `x` has order one.

For an irreducible projective plane curve `C : F = 0` with an ordinary multiple point `P`, a
change of coordinates (`exists_map_eq_and_linearSubst_eq_X_zero`) moves `P` to `[0 : 0 : 1]` with
`X = 0` not tangent; there the chart `Z ≠ 0` identifies the places over `P` with the places
`blowupPlace` of the affine curve `F_(2)`, and the orders of forms with the orders of their
dehomogenizations. So exactly `m_P(F)` places lie over `P`, one for each tangent, and the orders
of forms at them are as for affine curves.

## Main definitions

* `PlaneCurves.Affine.blowupPlace hF hX h hα`: the place of `k(F)` over the origin corresponding
  to the tangent `Y - α X`.

## Main results

* `PlaneCurves.Affine.valuation_blowupPlace`, `PlaneCurves.Affine.addValuation_blowupPlace`: the
  valuation and the order of `blowupPlace` are those of the place at `(0, α)` of `F'`.
* `PlaneCurves.Affine.localSubring_le_integers_blowupPlace`: `blowupPlace` lies over the origin.
* `PlaneCurves.Affine.valuation_blowupPlace_div_sub_lt_one`, `eq_of_blowupPlace_eq`: `y / x - α`
  has positive order at the place over `Y - α X`, so distinct tangents give distinct places.
* `PlaneCurves.Affine.div_mem_integers_of_localSubring_le`: `z = y / x` lies in the valuation
  ring of every place over the origin.
* `PlaneCurves.Affine.isTangentAt_of_valuation_div_sub_lt_one`,
  `PlaneCurves.Affine.eq_blowupPlace_of_valuation_div_sub_lt_one`: a place over the origin at
  which `z` takes the value `α` is `blowupPlace` for the tangent `Y - α X`.
* `PlaneCurves.Affine.existsUnique_eq_blowupPlace`: every place over the origin is `blowupPlace`
  for exactly one tangent.
* `PlaneCurves.Affine.addValuation_x_blowupPlace`: `x` has order one at each `blowupPlace`.
* `PlaneCurves.Affine.addValuation_blowupPlace_algebraMap_mk`: a polynomial `G` has order
  `m_0(G) + ord_{(0, α)}(G')` at the place over `Y - α X`, `G'` being its strict transform;
  `natCast_orderAt_le_addValuation_blowupPlace`: so its order is at least `m_0(G)`, and
  `addValuation_blowupPlace_eq_iff`: for `G ≠ 0`, with equality exactly when `Y - α X` is not
  tangent to `G`.
* `PlaneCurves.Affine.le_orderAt_iff_forall_le_addValuation_blowupPlace`: for `s ≤ r`,
  `m_0(G) ≥ s` exactly when `G` has order at least `s` at every place over the origin.
* `PlaneCurves.Affine.addValuation_blowupPlace_pderiv_one`: `∂F/∂Y` has order `r - 1` at every
  place over the origin, in every characteristic.
* `PlaneCurves.Affine.addValuation_blowupPlace_eq_one`: a line through the origin that is not
  tangent to `F` has order one at every place over the origin.
* `PlaneCurves.Projective.ncard_placesOver_of_isOrdinaryMultiplePoint`: exactly `m_P(F)` places
  lie over an ordinary multiple point `P` of a projective plane curve.
* `PlaneCurves.Projective.exists_isTangentAt_and_ordForm_eq_mult`: the places over `P` correspond
  to the tangents at `P`, and `G` has order `m_P(G)` at the place of a tangent not tangent to `G`;
  `natCast_toNat_mult_le_ordForm`: in any case the order is at least `m_P(G)`.
* `PlaneCurves.Projective.le_mult_iff_forall_le_ordForm`: for `s ≤ m_P(F)`, `m_P(G) ≥ s` iff `G`
  has order at least `s` at every place over `P`.
* `PlaneCurves.Projective.ordForm_eq_one_of_not_isTangentAt`: a line through `P` that is not
  tangent has order one at every place over `P`.
* `PlaneCurves.Projective.ordForm_pderiv_one`: at `P = [0 : 0 : 1]`, with `X = 0` not tangent,
  `∂F/∂Y` has order `m_P(F) - 1` at every place over `P`.
* `PlaneCurves.Projective.IsOrdinaryMultiplePoint.placesOver_spec`: the milestone, collecting
  these statements.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.2, Problems 7.4, 7.5
-/

public section

open MvPolynomial TauCeti

/-! ### The places over an ordinary multiple point at the origin -/

namespace PlaneCurves.Affine

open AffineSpace

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 2) k} [(Ideal.span {F}).IsPrime]
  (hF : Irreducible F) (hX : ¬Associated F (X 0)) (h : IsOrdinaryMultiplePoint F 0)

/-- The **place over a tangent** at an ordinary multiple point. If the origin is an ordinary
multiple point of `F` and `Y - α X` is tangent to `F` there, then `(0, α)` is a simple point of the
strict transform `F'`; this is the place of `k(F)` that corresponds, under `k(F) ≅ k(F')`, to the
place of `k(F')` at `(0, α)`. -/
noncomputable def blowupPlace {α : k} (hα : IsTangentAt F 0 (X 1 - C α * X 0)) :
    Place k (functionField (Ideal.span {F})) :=
  haveI := isPrime_span_blowupStrictTransform hF hX
  (placeAt (h.isSimplePoint_blowupStrictTransform hα).1).map (blowupFunctionFieldEquiv hF hX).symm

theorem blowupPlace_def [(Ideal.span {blowupStrictTransform F}).IsPrime] {α : k}
    (hα : IsTangentAt F 0 (X 1 - C α * X 0)) :
    blowupPlace hF hX h hα = (placeAt (h.isSimplePoint_blowupStrictTransform hα).1).map
      (blowupFunctionFieldEquiv hF hX).symm :=
  (rfl)

/-- The valuation of `blowupPlace` is that of the place at `(0, α)` of the strict transform. -/
theorem valuation_blowupPlace [(Ideal.span {blowupStrictTransform F}).IsPrime] {α : k}
    (hα : IsTangentAt F 0 (X 1 - C α * X 0)) (w : functionField (Ideal.span {F})) :
    (blowupPlace hF hX h hα).valuation w =
      (placeAt (h.isSimplePoint_blowupStrictTransform hα).1).valuation
        (blowupFunctionFieldEquiv hF hX w) := by
  rw [blowupPlace_def, Place.valuation_map, AlgEquiv.symm_symm]

/-- The order at `blowupPlace` is the order at the place at `(0, α)` of the strict transform. -/
theorem addValuation_blowupPlace [(Ideal.span {blowupStrictTransform F}).IsPrime] {α : k}
    (hα : IsTangentAt F 0 (X 1 - C α * X 0)) (w : functionField (Ideal.span {F})) :
    (blowupPlace hF hX h hα).addValuation w =
      (placeAt (h.isSimplePoint_blowupStrictTransform hα).1).addValuation
        (blowupFunctionFieldEquiv hF hX w) := by
  rw [blowupPlace_def, Place.addValuation_map, AlgEquiv.symm_symm]

omit [(Ideal.span {F}).IsPrime] in
/-- `G(X, XZ)` takes at `(0, α)` the value of `G` at the origin. -/
private theorem eval_aeval_X_X_mul_X (α : k) (g : MvPolynomial (Fin 2) k) :
    eval ![0, α] (aeval ![X 0, X 0 * X 1] g) = eval 0 g := by
  refine (aeval_bind₁ ![0, α] ![X 0, X 0 * X 1] g).trans ?_
  change aeval _ g = aeval _ g
  congr 1
  ext i : 1
  fin_cases i <;> simp

/-- **`blowupPlace` lies over the origin**: its valuation ring contains `𝒪_0(F)`. -/
theorem localSubring_le_integers_blowupPlace {α : k} (hα : IsTangentAt F 0 (X 1 - C α * X 0)) :
    (AffineSpace.localSubring 0
      (span_le_vanishingIdeal (isOrdinaryMultiplePoint_def.1 h).1.eval_eq_zero)).toSubring ≤
      (blowupPlace hF hX h hα).integers.toSubring := by
  have := isPrime_span_blowupStrictTransform hF hX
  intro f hf
  obtain ⟨a, b, hb, rfl⟩ := (mem_localSubring_iff _ _).1 hf
  change _ ∈ (blowupPlace hF hX h hα).integers
  rw [blowupPlace_def, Place.mem_integers_map_iff, AlgEquiv.symm_symm,
    ← ValuationSubring.mem_toSubring, integers_toSubring_placeAt, mem_localSubring_iff]
  refine ⟨aeval ![X 0, X 0 * X 1] a, aeval ![X 0, X 0 * X 1] b, ?_, by simp [map_div₀]⟩
  rwa [eval_aeval_X_X_mul_X]

/-- **`x` has order one** at every place over an ordinary multiple point at the origin. -/
theorem addValuation_x_blowupPlace {α : k} (hα : IsTangentAt F 0 (X 1 - C α * X 0)) :
    (blowupPlace hF hX h hα).addValuation
      (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0))) = 1 := by
  have := isPrime_span_blowupStrictTransform hF hX
  rw [addValuation_blowupPlace, blowupFunctionFieldEquiv_x,
    ← map_natCast_ord_eq_addValuation_placeAt, h.ord_X_zero_blowupStrictTransform hα]
  rfl

/-- **Orders of polynomials over an ordinary multiple point.** At the place over the tangent
`Y - α X`, a polynomial `G` has order `m_0(G) + ord_{(0, α)}(G')`, where `G'` is its strict
transform: `G(x, xz) = x ^ m G'(x, z)` with `m = m_0(G)`, and `x` has order one. -/
theorem addValuation_blowupPlace_algebraMap_mk [(Ideal.span {blowupStrictTransform F}).IsPrime]
    {α : k} (hα : IsTangentAt F 0 (X 1 - C α * X 0)) (G : MvPolynomial (Fin 2) k) :
    (blowupPlace hF hX h hα).addValuation
        (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) G)) =
      ((G.orderAt 0).toNat : WithTop ℤ) +
        (placeAt (h.isSimplePoint_blowupStrictTransform hα).1).addValuation
          (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {blowupStrictTransform F})
            (blowupStrictTransform G))) := by
  have hx : (placeAt (h.isSimplePoint_blowupStrictTransform hα).1).addValuation
      (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {blowupStrictTransform F}) (X 0))) = 1 := by
    rw [← map_natCast_ord_eq_addValuation_placeAt, h.ord_X_zero_blowupStrictTransform hα]
    rfl
  rw [addValuation_blowupPlace, blowupFunctionFieldEquiv_algebraMap_mk,
    ← X_pow_mul_blowupStrictTransform, map_mul, map_mul, AddValuation.map_mul, map_pow, map_pow,
    AddValuation.map_pow, hx, nsmul_one]

/-- At the place over a tangent of an ordinary multiple point at the origin, a polynomial `G` has
order at least its multiplicity `m_0(G)`. -/
theorem natCast_orderAt_le_addValuation_blowupPlace {α : k}
    (hα : IsTangentAt F 0 (X 1 - C α * X 0)) (G : MvPolynomial (Fin 2) k) :
    ((G.orderAt 0).toNat : WithTop ℤ) ≤ (blowupPlace hF hX h hα).addValuation
      (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) G)) := by
  have := isPrime_span_blowupStrictTransform hF hX
  rw [addValuation_blowupPlace_algebraMap_mk]
  refine le_add_of_nonneg_right ((Place.addValuation_nonneg_iff _).2 ?_)
  rw [← ValuationSubring.mem_toSubring, integers_toSubring_placeAt]
  exact algebraMap_mem_localSubring _ _ _

/-- A polynomial expression in elements of a valuation ring, read in the field. -/
private theorem coe_aeval_integers {K : Type*} [Field K] [Algebra k K] (Q : Place k K)
    (u : Fin 2 → Q.integers) (g : MvPolynomial (Fin 2) k) :
    ((aeval u g : Q.integers) : K) = aeval ![(u 0 : K), (u 1 : K)] g := by
  have h := DFunLike.congr_fun (comp_aeval (R := k) (f := u)
    (IsScalarTower.toAlgHom k Q.integers K)) g
  have hu : (fun i ↦ IsScalarTower.toAlgHom k Q.integers K (u i)) = ![(u 0 : K), (u 1 : K)] := by
    ext i : 1
    fin_cases i <;> rfl
  rw [hu] at h
  exact h

include hF hX in
/-- **`z = y / x` is integral at a place over the origin.** If the origin is an ordinary multiple
point of `F` at which `X = 0` is not tangent, then `y / x` lies in the valuation ring of every place
of `k(F)` over the origin: it is a root of a monic polynomial over `𝒪_0(F)`. -/
theorem div_mem_integers_of_localSubring_le (hT : ¬IsTangentAt F 0 (X 0))
    {Q : Place k (functionField (Ideal.span {F}))}
    (hQ : (AffineSpace.localSubring 0
      (span_le_vanishingIdeal (isOrdinaryMultiplePoint_def.1 h).1.eval_eq_zero)).toSubring ≤
        Q.integers.toSubring) :
    algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 1)) /
      algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0)) ∈ Q.integers := by
  set x : functionField (Ideal.span {F}) :=
    algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0))
  set y : functionField (Ideal.span {F}) :=
    algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 1))
  have hx0 : x ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton]
    exact fun hd ↦ hX (hF.associated_of_dvd prime_X.irreducible hd)
  have hxQ : x ∈ Q.integers := hQ (algebraMap_mem_localSubring _ _ _)
  have hyQ : y ∈ Q.integers := hQ (algebraMap_mem_localSubring _ _ _)
  have hxy (g : MvPolynomial (Fin 2) k) :
      ((aeval ![(⟨x, hxQ⟩ : Q.integers), ⟨y, hyQ⟩] g : Q.integers) :
        functionField (Ideal.span {F})) =
        algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) g) := by
    have h' : aeval ![x, y] = (IsScalarTower.toAlgHom k (MvPolynomial (Fin 2) k ⧸ Ideal.span {F})
        (functionField (Ideal.span {F}))).comp (Ideal.Quotient.mkₐ k (Ideal.span {F})) :=
      algHom_ext fun i ↦ by fin_cases i <;> simp [x, y]
    rw [coe_aeval_integers]
    exact DFunLike.congr_fun h' g
  refine Q.mem_integers_of_isIntegral (R := Q.integers) (fun r ↦ r.2) ?_
  refine isIntegral_of_isUnit_aeval_blowupChartLeadingCoeff (F := F) (B := functionField _)
    (x := (⟨x, hxQ⟩ : Q.integers)) (y := ⟨y, hyQ⟩) ?_ ?_ (fun _ _ h ↦ mul_left_cancel₀ hx0 h) ?_
  · exact Subtype.ext ((hxy F).trans (by simp))
  · exact mul_div_cancel₀ y hx0
  · refine Q.isUnit_iff_valuation_eq_one.2 ?_
    rw [hxy]
    refine AffineSpace.valuation_algebraMap_mk_eq_one hQ ?_
    rw [eval_zero_blowupChartLeadingCoeff]
    exact (isTangentAt_zero_X_zero_iff).not.1 hT

/-- At a place `Q` of `k(F)` at which `x` and `z = y / x` lie in the valuation ring, the polynomial
expressions in `x` and `z` are the functions on the strict transform `F'`, read in `k(F)`. -/
private theorem coe_aeval_eq_blowupFunctionFieldEquiv_symm
    [(Ideal.span {blowupStrictTransform F}).IsPrime] {Q : Place k (functionField (Ideal.span {F}))}
    (hxQ : algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0)) ∈ Q.integers)
    (hzQ : algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 1)) /
      algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0)) ∈ Q.integers)
    (g : MvPolynomial (Fin 2) k) :
    ((aeval ![(⟨_, hxQ⟩ : Q.integers), ⟨_, hzQ⟩] g : Q.integers) :
      functionField (Ideal.span {F})) = (blowupFunctionFieldEquiv hF hX).symm
        (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {blowupStrictTransform F}) g)) := by
  rw [coe_aeval_integers, blowupFunctionFieldEquiv_symm_algebraMap_mk]
  rfl

variable [IsAlgClosed k]

/-- At the place over the tangent `Y - α X`, the function `z = y / x` takes the value `α`. -/
theorem valuation_blowupPlace_div_sub_lt_one {α : k} (hα : IsTangentAt F 0 (X 1 - C α * X 0)) :
    (blowupPlace hF hX h hα).valuation
      (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 1)) /
        algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0)) - algebraMap k _ α) < 1 := by
  have := isPrime_span_blowupStrictTransform hF hX
  have hP := (h.isSimplePoint_blowupStrictTransform hα).1
  rw [valuation_blowupPlace, map_sub, AlgEquiv.commutes, ← blowupFunctionFieldEquiv_symm_z hF hX,
    AlgEquiv.apply_symm_apply]
  simpa using AffineSpace.valuation_algebraMap_mk_sub_lt_one
    (isFunctionField_functionField_span_singleton hP.irreducible)
    (integers_toSubring_placeAt hP).symm.le (X 1)

/-- The places over distinct tangents are distinct. -/
theorem eq_of_blowupPlace_eq {α β : k} (hα : IsTangentAt F 0 (X 1 - C α * X 0))
    (hβ : IsTangentAt F 0 (X 1 - C β * X 0))
    (he : blowupPlace hF hX h hα = blowupPlace hF hX h hβ) :
    α = β :=
  Place.eq_of_valuation_sub_lt_one _ (valuation_blowupPlace_div_sub_lt_one hF hX h hα)
    (he ▸ valuation_blowupPlace_div_sub_lt_one hF hX h hβ)


/-- At a place `Q` over the origin at which `z = y / x` takes the value `α`, every function
`G(x, z)` on the strict transform takes its value `G(0, α)`. -/
private theorem valuation_blowupFunctionFieldEquiv_symm_sub_lt_one
    [(Ideal.span {blowupStrictTransform F}).IsPrime] {Q : Place k (functionField (Ideal.span {F}))}
    (hQ : (AffineSpace.localSubring 0
      (span_le_vanishingIdeal (isOrdinaryMultiplePoint_def.1 h).1.eval_eq_zero)).toSubring ≤
        Q.integers.toSubring) {α : k}
    (hα : Q.valuation (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 1)) /
      algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0)) - algebraMap k _ α) < 1)
    (hzQ : algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 1)) /
      algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0)) ∈ Q.integers)
    (g : MvPolynomial (Fin 2) k) :
    Q.valuation ((blowupFunctionFieldEquiv hF hX).symm
        (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {blowupStrictTransform F}) g)) -
      algebraMap k _ (eval ![0, α] g)) < 1 := by
  have hxQ := hQ (algebraMap_mem_localSubring _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0)))
  rw [← coe_aeval_eq_blowupFunctionFieldEquiv_symm hF hX hxQ hzQ]
  refine Q.valuation_aeval_sub_lt_one (fun i ↦ ?_) g
  fin_cases i
  · simpa using AffineSpace.valuation_algebraMap_mk_sub_lt_one
      (isFunctionField_functionField_span_singleton hF) hQ (X 0)
  · exact hα

include hF hX in
/-- At a place over the origin, `z = y / x` can only take the value `α` of a tangent `Y - α X`. -/
theorem isTangentAt_of_valuation_div_sub_lt_one {Q : Place k (functionField (Ideal.span {F}))}
    (hQ : (AffineSpace.localSubring 0
      (span_le_vanishingIdeal (isOrdinaryMultiplePoint_def.1 h).1.eval_eq_zero)).toSubring ≤
        Q.integers.toSubring) {α : k}
    (hα : Q.valuation (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 1)) /
      algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0)) - algebraMap k _ α) < 1)
    (hzQ : algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 1)) /
      algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0)) ∈ Q.integers) :
    IsTangentAt F 0 (X 1 - C α * X 0) := by
  have := isPrime_span_blowupStrictTransform hF hX
  rw [← eval_zero_blowupStrictTransform_eq_zero_iff h.ne_zero]
  by_contra hne
  have h1 := valuation_blowupFunctionFieldEquiv_symm_sub_lt_one hF hX h hQ hα hzQ
    (blowupStrictTransform F)
  rw [Ideal.Quotient.mk_singleton_self, map_zero, map_zero, zero_sub, Valuation.map_neg,
    Q.isTrivialOn.eq_one _ hne] at h1
  exact lt_irrefl _ h1

/-- A place `Q` over the origin at which `z = y / x` takes the value `α` is the place over the
tangent `Y - α X`: its valuation ring contains, and so is, the local ring of `F'` at `(0, α)`. -/
theorem eq_blowupPlace_of_valuation_div_sub_lt_one
    {Q : Place k (functionField (Ideal.span {F}))}
    (hQ : (AffineSpace.localSubring 0
      (span_le_vanishingIdeal (isOrdinaryMultiplePoint_def.1 h).1.eval_eq_zero)).toSubring ≤
        Q.integers.toSubring) {α : k}
    (hα : Q.valuation (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 1)) /
      algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0)) - algebraMap k _ α) < 1)
    (hzQ : algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 1)) /
      algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0)) ∈ Q.integers) :
    Q = blowupPlace hF hX h (isTangentAt_of_valuation_div_sub_lt_one hF hX h hQ hα hzQ) := by
  have := isPrime_span_blowupStrictTransform hF hX
  have hψ := valuation_blowupFunctionFieldEquiv_symm_sub_lt_one hF hX h hQ hα hzQ
  have hxQ := hQ (algebraMap_mem_localSubring _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0)))
  have hP := (h.isSimplePoint_blowupStrictTransform
    (isTangentAt_of_valuation_div_sub_lt_one hF hX h hQ hα hzQ)).1
  have hle : (placeAt hP).integers ≤ (Q.map (blowupFunctionFieldEquiv hF hX)).integers := by
    intro f hf
    rw [← ValuationSubring.mem_toSubring, integers_toSubring_placeAt, mem_localSubring_iff] at hf
    obtain ⟨a, b, hb, rfl⟩ := hf
    rw [Place.mem_integers_map_iff, map_div₀, Place.mem_integers_iff, map_div₀]
    have hb1 := Valuation.map_eq_of_sub_lt Q.valuation
      (by rw [Q.isTrivialOn.eq_one _ hb]; exact hψ b)
    rw [Q.isTrivialOn.eq_one _ hb] at hb1
    rw [hb1, div_one, ← coe_aeval_eq_blowupFunctionFieldEquiv_symm hF hX hxQ hzQ]
    exact Q.mem_integers_iff.1 (aeval ![(⟨_, hxQ⟩ : Q.integers), ⟨_, hzQ⟩] a).2
  rw [blowupPlace_def, Place.eq_of_integers_le hle, Place.map_symm_map]

/-- **The places over an ordinary multiple point.** Let the origin be an ordinary multiple point
of the irreducible curve `F`, at which `X = 0` is not tangent. Every place `Q` of `k(F)` whose
valuation ring contains `𝒪_0(F)` is `blowupPlace` for exactly one tangent `Y - α X` of `F` at the
origin. -/
theorem existsUnique_eq_blowupPlace (hT : ¬IsTangentAt F 0 (X 0))
    {Q : Place k (functionField (Ideal.span {F}))}
    (hQ : (AffineSpace.localSubring 0
      (span_le_vanishingIdeal (isOrdinaryMultiplePoint_def.1 h).1.eval_eq_zero)).toSubring ≤
        Q.integers.toSubring) :
    ∃! α : k, ∃ hα : IsTangentAt F 0 (X 1 - C α * X 0), Q = blowupPlace hF hX h hα := by
  have hzQ := div_mem_integers_of_localSubring_le hF hX h hT hQ
  obtain ⟨α, hα⟩ := (Q.degree_eq_one_iff_forall_exists_valuation_sub_lt_one.1
    (Q.degree_eq_one_of_isAlgClosed_of_isFunctionField
      (isFunctionField_functionField_span_singleton hF))) _ hzQ
  exact ⟨α, ⟨_, eq_blowupPlace_of_valuation_div_sub_lt_one hF hX h hQ hα hzQ⟩,
    fun β ⟨hβ, hQβ⟩ ↦ Place.eq_of_valuation_sub_lt_one Q
      (hQβ ▸ valuation_blowupPlace_div_sub_lt_one hF hX h hβ) hα⟩

/-! ### Orders of polynomials at the places over an ordinary multiple point -/

/-- **Orders at the places over an ordinary multiple point.** At the place over the tangent
`Y - α X`, a nonzero polynomial `G` has order exactly its multiplicity `m_0(G)` if and only if
`Y - α X` is not tangent to `G` at the origin. -/
theorem addValuation_blowupPlace_eq_iff {α : k} (hα : IsTangentAt F 0 (X 1 - C α * X 0))
    {G : MvPolynomial (Fin 2) k} (hG : G ≠ 0) :
    (blowupPlace hF hX h hα).addValuation
        (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) G)) = ((G.orderAt 0).toNat : ℕ) ↔
      ¬IsTangentAt G 0 (X 1 - C α * X 0) := by
  have := isPrime_span_blowupStrictTransform hF hX
  have hP := (h.isSimplePoint_blowupStrictTransform hα).1
  have he (z : functionField (Ideal.span {blowupStrictTransform F})) :
      (placeAt hP).valuation z = 1 ↔ (placeAt hP).addValuation z = 0 := by
    rw [← WithTop.coe_zero, Place.addValuation_eq_coe_iff, neg_zero, WithZero.exp_zero]
  rw [addValuation_blowupPlace_algebraMap_mk, ← eval_zero_blowupStrictTransform_eq_zero_iff hG,
    ← ne_eq, ← AffineSpace.valuation_algebraMap_mk_eq_one_iff
      (isFunctionField_functionField_span_singleton hP.irreducible)
      (integers_toSubring_placeAt hP).symm.le, he]
  generalize (placeAt hP).addValuation _ = t
  induction t using WithTop.recTopCoe <;> simp [← WithTop.coe_natCast, ← WithTop.coe_add]

/-- **Multiplicities from orders over an ordinary multiple point.** Let the origin be an ordinary
multiple point of multiplicity `r` of `F`, at which `X = 0` is not tangent. For a nonzero
polynomial `G` and `s ≤ r`, `m_0(G) ≥ s` if and only if `G` has order at least `s` at every
place over the origin. -/
theorem le_orderAt_iff_forall_le_addValuation_blowupPlace (hT : ¬IsTangentAt F 0 (X 0))
    {G : MvPolynomial (Fin 2) k} (hG : G ≠ 0) {s : ℕ} (hs : (s : ℕ∞) ≤ F.orderAt 0) :
    (s : ℕ∞) ≤ G.orderAt 0 ↔ ∀ (α : k) (hα : IsTangentAt F 0 (X 1 - C α * X 0)),
      (s : WithTop ℤ) ≤ (blowupPlace hF hX h hα).addValuation
        (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) G)) := by
  have hGn : G.orderAt 0 = (G.orderAt 0).toNat :=
    (ENat.natCast_toNat (orderAt_eq_top_iff.not.2 hG)).symm
  refine ⟨fun hsG α hα ↦ le_trans ?_ (natCast_orderAt_le_addValuation_blowupPlace hF hX h hα G),
    fun hall ↦ ?_⟩
  · rw [hGn, Nat.cast_le] at hsG
    exact_mod_cast hsG
  by_contra hlt
  have hlt' : G.orderAt 0 < F.orderAt 0 := (not_le.1 hlt).trans_le hs
  obtain ⟨L, hL, hLG⟩ : ∃ L, IsTangentAt F 0 L ∧ ¬IsTangentAt G 0 L := by
    by_contra! hall'
    exact (h.orderAt_le_of_forall_isTangentAt hG hall').not_gt hlt'
  obtain ⟨α, hLα⟩ := hL.exists_associated_X_one_sub_C_mul_X_zero hT
  have hα : IsTangentAt F 0 (X 1 - C α * X 0) := isTangentAt_def.2
    ⟨isHomogeneous_X_one_sub_C_mul_X_zero α, X_one_sub_C_mul_X_zero_ne_zero α,
      hLα.symm.dvd.trans hL.dvd⟩
  have hαG : ¬IsTangentAt G 0 (X 1 - C α * X 0) := fun hT' ↦ hLG (isTangentAt_def.2
    ⟨hL.isHomogeneous, hL.ne_zero, hLα.dvd.trans hT'.dvd⟩)
  have h1 := hall α hα
  rw [(addValuation_blowupPlace_eq_iff hF hX h hα hG).2 hαG] at h1
  rw [hGn] at hlt
  exact hlt (by exact_mod_cast h1)

/-- **The partial derivative `∂F/∂Y` at the places over an ordinary multiple point.** If the
origin is an ordinary multiple point of multiplicity `r` of `F`, then `∂F/∂Y` has order `r - 1`
at every place over the origin, in every characteristic. -/
theorem addValuation_blowupPlace_pderiv_one {α : k} (hα : IsTangentAt F 0 (X 1 - C α * X 0)) :
    (blowupPlace hF hX h hα).addValuation
        (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (pderiv 1 F))) =
      ((F.orderAt 0).toNat - 1 : ℕ) := by
  have hi : IsUnit (pderiv 1 (X 1 - C α * X 0 : MvPolynomial (Fin 2) k)) := by
    simp [pderiv_X]
  have h0 : pderiv 1 F ≠ 0 := fun h0 ↦ h.pderiv_leadingFormAt_ne_zero hα hi
    (by rw [← leadingFormAt_pderiv_of_ne_zero (h.pderiv_leadingFormAt_ne_zero hα hi), h0,
      leadingFormAt_zero])
  rw [(addValuation_blowupPlace_eq_iff hF hX h hα h0).2 (h.not_isTangentAt_pderiv hα hi),
    h.orderAt_pderiv hα hi, ENat.toNat_natCast]

/-- **Lines at the places over an ordinary multiple point.** A line `L` through the origin that is
not tangent to `F` there has order one at every place over the origin. -/
theorem addValuation_blowupPlace_eq_one {α : k} (hα : IsTangentAt F 0 (X 1 - C α * X 0))
    {L : MvPolynomial (Fin 2) k} (hL : L.IsHomogeneous 1) (hL₀ : L ≠ 0)
    (hLF : ¬IsTangentAt F 0 L) :
    (blowupPlace hF hX h hα).addValuation
      (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) L)) = 1 := by
  have hnt : ¬IsTangentAt L 0 (X 1 - C α * X 0) := by
    intro hT
    have hd := hT.dvd
    rw [hL.leadingFormAt_zero] at hd
    have hass := hα.prime.irreducible.associated_of_dvd (irreducible_of_isHomogeneous_one hL hL₀)
      hd
    exact hLF (isTangentAt_def.2 ⟨hL, hL₀, hass.symm.dvd.trans hα.dvd⟩)
  rw [(addValuation_blowupPlace_eq_iff hF hX h hα hL₀).2 hnt, hL.orderAt_zero hL₀,
    ENat.toNat_natCast, Nat.cast_one]

end PlaneCurves.Affine

/-! ### The places over an ordinary multiple point of a projective plane curve -/

namespace PlaneCurves.Projective

open Projectivization PlaneCurves.ProjectiveSpace TauCeti.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization

section
variable {k : Type*} [Field k] {P : ℙ k (Fin 3 → k)} {m : ℕ} {G : MvPolynomial (Fin 3) k}

/-- Forms of the same degree whose dehomogenizations are associated are associated. -/
private theorem associated_of_associated_dehomogenize {G' : MvPolynomial (Fin 3) k}
    (hG : G.IsHomogeneous m) (hG' : G'.IsHomogeneous m)
    (h : Associated (dehomogenize 2 G) (dehomogenize 2 G')) : Associated G G' := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨c, hc, hcu⟩ := (isUnit_iff_eq_C_of_isReduced (R := k)).1 u.isUnit
  refine ⟨(hc.map C).unit, dehomogenize_injOn 2 m (by simpa using hG.mul (isHomogeneous_C _ c))
    hG' ?_⟩
  simpa [hcu] using hu

/-- At the point with chart coordinates `0` in the chart `X₂ ≠ 0`, a line `L(X₀, X₁)` is tangent
to `G` iff it is tangent to the dehomogenization `G_(2)` at the origin. -/
private theorem isTangentAt_rename_iff (hG : G.IsHomogeneous m) (hP : P ∈ affineOpen 2)
    (h0 : affineChart 2 P = 0) {L : MvPolynomial (Fin 2) k} (hL : L.IsHomogeneous 1) :
    IsTangentAt G P (rename Fin.castSucc L) ↔ Affine.IsTangentAt (dehomogenize 2 G) 0 L := by
  have hc : (fun j : Fin 2 ↦ X ((2 : Fin 3).succAbove j) - C (affineChart 2 P j) * X 2 :
      Fin 2 → MvPolynomial (Fin 3) k) = X ∘ Fin.castSucc := by
    funext j
    fin_cases j
    · simp [h0]
    · simp only [Fin.isValue, h0, Pi.zero_apply, map_zero, zero_mul, sub_zero,
        Function.comp_apply]
      rfl
  have h := isTangentAt_aeval_chart_iff hG hP hL
  rwa [hc, h0, ← aeval_rename, aeval_X_left_apply] at h

/-- A line through the point with chart coordinates `0` in the chart `X₂ ≠ 0` is tangent to `G`
iff its dehomogenization, a line through the origin, is tangent to `G_(2)` there. -/
private theorem isTangentAt_iff_dehomogenize (hG : G.IsHomogeneous m) (hP : P ∈ affineOpen 2)
    (h0 : affineChart 2 P = 0) {L : MvPolynomial (Fin 3) k} (hL : L.IsHomogeneous 1)
    (hLP : eval P.rep L = 0) :
    IsTangentAt G P L ↔ Affine.IsTangentAt (dehomogenize 2 G) 0 (dehomogenize 2 L) := by
  rw [isTangentAt_iff_affine hG hP hL hLP, h0, taylor_zero]

end

variable {k : Type*} [Field k] [IsAlgClosed k] {F : MvPolynomial (Fin 3) k} {d : ℕ}
  {hF : F.IsHomogeneous d} [Fact (Irreducible F)]
  {P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k))}

variable (hF P) in
/-- The orders at the places over an ordinary multiple point `P`, as the milestone states them. -/
private def OrdinaryPlacesSpec : Prop :=
  (placesOver hF P).ncard = (mult F P.1).toNat ∧
  ∃ L : Place k (functionField hF) → MvPolynomial (Fin 3) k,
    (∀ Q ∈ placesOver hF P, IsTangentAt F P.1 (L Q)) ∧
    (∀ L', IsTangentAt F P.1 L' → ∃! Q, Q ∈ placesOver hF P ∧ Associated L' (L Q)) ∧
    (∀ {L'} (hL : L'.IsHomogeneous 1), L' ≠ 0 → eval P.1.rep L' = 0 → ¬IsTangentAt F P.1 L' →
      ∀ Q ∈ placesOver hF P, ordForm hF Q hL = 1) ∧
    ∀ {m G} (hG : G.IsHomogeneous m), G ≠ 0 →
      (∀ Q ∈ placesOver hF P, ((mult G P.1).toNat : WithTop ℤ) ≤ ordForm hF Q hG ∧
        (¬IsTangentAt G P.1 (L Q) → ordForm hF Q hG = (mult G P.1).toNat)) ∧
      ∀ s : ℕ, (s : ℕ∞) ≤ mult F P.1 →
        ((s : ℕ∞) ≤ mult G P.1 ↔ ∀ Q ∈ placesOver hF P, (s : WithTop ℤ) ≤ ordForm hF Q hG)

omit [IsAlgClosed k] [Fact (Irreducible F)] in
/-- The local rings at equal points have the same membership. -/
private theorem localSubring_le_iff_of_eq {f : MvPolynomial (Fin 2) k} [(Ideal.span {f}).IsPrime]
    {a b : Fin 2 → k} (hab : a = b) {ha : Ideal.span {f} ≤ vanishingIdeal k {a}}
    {hb : Ideal.span {f} ≤ vanishingIdeal k {b}}
    {S : Subring (AffineSpace.functionField (Ideal.span {f}))} :
    (AffineSpace.localSubring a ha).toSubring ≤ S ↔
      (AffineSpace.localSubring b hb).toSubring ≤ S := by
  subst hab
  rfl

/-- **The milestone in a chart.** At the point `(0, 0)` of the chart `X₂ ≠ 0`, with `X₀` not
tangent, the places over `P` are the places `blowupPlace` of the affine curve `F_(2)`, carried to
`k(C)`; the milestone and the order of `∂F/∂Y` follow from their affine counterparts. -/
private theorem ordinaryPlacesSpec_of_chart (h : IsOrdinaryMultiplePoint F P.1)
    (hP : P.1 ∈ affineOpen 2) (h0 : affineChart 2 P.1 = 0) (hT : ¬IsTangentAt F P.1 (X 0)) :
    OrdinaryPlacesSpec hF P ∧ ∀ Q ∈ placesOver hF P,
      ordForm hF Q (hF.pderiv (i := 1)) = ((mult F P.1).toNat - 1 : ℕ) := by
  classical
  have hi := not_dvd_X_of_mem_affineOpen hF P hP
  have := isPrime_span_dehomogenize hF hi
  set f := dehomogenize 2 F
  set e := functionField.chartEquiv hF 2 hi
  have h' : Affine.IsOrdinaryMultiplePoint f 0 :=
    h0 ▸ (isOrdinaryMultiplePoint_iff_affine hF hP).1 h
  have hf : Irreducible f := ((Ideal.span_singleton_prime h'.ne_zero).1 inferInstance).irreducible
  have hX : ¬Associated f (X 0) := fun ha ↦ by
    have h2 := Affine.isMultiplePoint_def.1 (Affine.isOrdinaryMultiplePoint_def.1 h').1
    rw [orderAt_eq_of_associated ha] at h2
    have h1 := orderAt_X_sub_C (0 : Fin 2 → k) 0
    simp only [Pi.zero_apply, map_zero, sub_zero] at h1
    rw [h1] at h2
    exact absurd h2 (by norm_num)
  have hrep (j : Fin 2) : P.1.rep ((2 : Fin 3).succAbove j) = 0 := by
    have h1 := rep_div_rep_eq_insertNth_affineChart ((2 : Fin 3).succAbove j) hP
    rw [h0, Fin.insertNth_apply_succAbove] at h1
    simpa [(mem_affineOpen_iff 2 P.1).1 hP] using h1
  have hP0 : eval P.1.rep (X 0) = 0 := by simpa using hrep 0
  have hT' : ¬Affine.IsTangentAt f 0 (X 0) := by
    rwa [isTangentAt_iff_dehomogenize hF hP h0 (isHomogeneous_X k 0) hP0, dehomogenize_X] at hT
  -- the projective tangent `X₁ - α X₀`
  have hLα (α : k) : rename Fin.castSucc (X 1 - C α * X 0 : MvPolynomial (Fin 2) k) =
      (X 1 - C α * X 0 : MvPolynomial (Fin 3) k) := by simp
  have htan {m : ℕ} {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous m) (α : k) :
      IsTangentAt G P.1 (X 1 - C α * X 0) ↔
        Affine.IsTangentAt (dehomogenize 2 G) 0 (X 1 - C α * X 0) := by
    rw [← isTangentAt_rename_iff hG hP h0 (isHomogeneous_X_one_sub_C_mul_X_zero α), hLα]
  have hmult {m : ℕ} {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous m) :
      mult G P.1 = (dehomogenize 2 G).orderAt 0 := by
    rw [mult_eq_orderAt_dehomogenize hG hP, h0]
  have hmem (Q : Place k (functionField hF)) : Q ∈ placesOver hF P ↔
      (AffineSpace.localSubring 0 (Affine.span_le_vanishingIdeal
        (Affine.isOrdinaryMultiplePoint_def.1 h').1.eval_eq_zero)).toSubring ≤
        (Q.map e).integers.toSubring := by
    rw [mem_placesOver_iff_localSubring_le_map_chartEquiv hP]
    exact localSubring_le_iff_of_eq h0
  have hord {Q : Place k (functionField hF)} (hQ : Q ∈ placesOver hF P) {m : ℕ}
      {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous m) :
      ordForm hF Q hG = (Q.map e).addValuation
        (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {f}) (dehomogenize 2 G))) :=
    ordForm_eq_addValuation_map_chartEquiv hP hQ hG
  -- the place over the tangent `Y - α X`
  have hover {α : k} (hα : Affine.IsTangentAt f 0 (X 1 - C α * X 0)) :
      (Affine.blowupPlace hf hX h' hα).map e.symm ∈ placesOver hF P := by
    rw [hmem, Place.map_map_symm]
    exact Affine.localSubring_le_integers_blowupPlace hf hX h' hα
  have hex (Q : Place k (functionField hF)) (hQ : Q ∈ placesOver hF P) :=
    Affine.existsUnique_eq_blowupPlace hf hX h' hT' ((hmem Q).1 hQ)
  let a : Place k (functionField hF) → k := fun Q ↦
    if hQ : Q ∈ placesOver hF P then (hex Q hQ).exists.choose else 0
  have ha {Q : Place k (functionField hF)} (hQ : Q ∈ placesOver hF P) :
      ∃ hα : Affine.IsTangentAt f 0 (X 1 - C (a Q) * X 0),
        Q.map e = Affine.blowupPlace hf hX h' hα := by
    simp only [a, hQ, ↓reduceDIte]
    exact (hex Q hQ).exists.choose_spec
  have hordα {Q : Place k (functionField hF)} (hQ : Q ∈ placesOver hF P) {m : ℕ}
      {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous m) :
      ordForm hF Q hG = (Affine.blowupPlace hf hX h' (ha hQ).1).addValuation
        (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {f}) (dehomogenize 2 G))) := by
    rw [hord hQ hG, (ha hQ).2]
  have hbl {α β : k} (hαβ : α = β) (hα : Affine.IsTangentAt f 0 (X 1 - C α * X 0))
      (hβ : Affine.IsTangentAt f 0 (X 1 - C β * X 0)) :
      Affine.blowupPlace hf hX h' hα = Affine.blowupPlace hf hX h' hβ := by
    subst hαβ
    rfl
  have haeq {Q : Place k (functionField hF)} (hQ : Q ∈ placesOver hF P) {α : k}
      (hα : Affine.IsTangentAt f 0 (X 1 - C α * X 0))
      (hQα : Q.map e = Affine.blowupPlace hf hX h' hα) : a Q = α :=
    (hex Q hQ).unique (ha hQ) ⟨hα, hQα⟩
  have hinj {Q Q' : Place k (functionField hF)} (hQ : Q ∈ placesOver hF P)
      (hQ' : Q' ∈ placesOver hF P) (haQ : a Q = a Q') : Q = Q' := by
    rw [← Place.map_symm_map e Q, ← Place.map_symm_map e Q', (ha hQ).2, (ha hQ').2,
      hbl haQ]
  have hdeh (α : k) : dehomogenize 2 (X 1 - C α * X 0 : MvPolynomial (Fin 3) k) =
      X 1 - C α * X 0 := by
    simp only [map_sub, map_mul, dehomogenize_X, algHom_C, algebraMap_eq]
    rw [show (1 : Fin 3) = (2 : Fin 3).succAbove 1 from rfl,
      show (0 : Fin 3) = (2 : Fin 3).succAbove 0 from rfl, Fin.insertNth_apply_succAbove,
      Fin.insertNth_apply_succAbove]
  have hL1 (α : k) : (X 1 - C α * X 0 : MvPolynomial (Fin 3) k).IsHomogeneous 1 :=
    (isHomogeneous_X k 1).sub (isHomogeneous_C_mul_X α 0)
  have hcov {L : MvPolynomial (Fin 2) k} (hL : Affine.IsTangentAt f 0 L) :
      ∃ α, Affine.IsTangentAt f 0 (X 1 - C α * X 0) ∧ Associated L (X 1 - C α * X 0) := by
    obtain ⟨α, hα⟩ := hL.exists_associated_X_one_sub_C_mul_X_zero hT'
    exact ⟨α, Affine.isTangentAt_def.2 ⟨isHomogeneous_X_one_sub_C_mul_X_zero α,
      X_one_sub_C_mul_X_zero_ne_zero α, hα.symm.dvd.trans hL.dvd⟩, hα⟩
  -- the count
  have hA : {α : k | Affine.IsTangentAt f 0 (X 1 - C α * X 0)}.ncard =
      (placesOver hF P).ncard :=
    (Set.ncard_congr (fun Q _ ↦ a Q) (fun Q hQ ↦ (ha hQ).1)
      (fun Q Q' hQ hQ' h ↦ hinj hQ hQ' h)
      (fun α hα ↦ ⟨_, hover hα, haeq (hover hα) hα (Place.map_map_symm _ _)⟩)).symm
  have hAfin : {α : k | Affine.IsTangentAt f 0 (X 1 - C α * X 0)}.Finite := by
    refine ((placesOver_finite hF P).image a).subset fun α hα ↦ ?_
    exact ⟨_, hover hα, haeq (hover hα) hα (Place.map_map_symm _ _)⟩
  let s := hAfin.toFinset.image fun α ↦ (X 1 - C α * X 0 : MvPolynomial (Fin 2) k)
  have hs : ∀ L ∈ s, Affine.IsTangentAt f 0 L := by
    intro L hL
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hL
    exact hAfin.mem_toFinset.1 hα
  have hpair : (s : Set (MvPolynomial (Fin 2) k)).Pairwise (fun L L' ↦ ¬Associated L L') := by
    intro L hL L' hL' hne hLL'
    obtain ⟨α, -, rfl⟩ := Finset.mem_image.1 hL
    obtain ⟨β, -, rfl⟩ := Finset.mem_image.1 hL'
    exact hne (by rw [associated_X_one_sub_C_mul_X_zero_iff.1 hLL'])
  have hcov' : ∀ L, Affine.IsTangentAt f 0 L → ∃ L' ∈ s, Associated L L' := by
    intro L hL
    obtain ⟨α, hα, hLα⟩ := hcov hL
    exact ⟨_, Finset.mem_image_of_mem _ (hAfin.mem_toFinset.2 hα), hLα⟩
  have hcard := ((Affine.isOrdinaryMultiplePoint_iff hs hpair hcov' h'.ne_zero).1 h').2
  rw [Finset.card_image_of_injective _ X_one_sub_C_mul_X_zero_injective,
    ← Set.ncard_eq_toFinset_card _ hAfin, hA, ← hmult hF] at hcard
  refine ⟨⟨by rw [← hcard, ENat.toNat_natCast], fun Q ↦ X 1 - C (a Q) * X 0,
    fun Q hQ ↦ (htan hF (a Q)).2 (ha hQ).1, fun L hL ↦ ?_, ?_, fun hG hG0 ↦ ⟨?_, ?_⟩⟩, ?_⟩
  · -- the tangents
    obtain ⟨α, hα, hLα⟩ := hcov ((isTangentAt_iff_dehomogenize hF hP h0 (isTangentAt_def.1 hL).1
      (isTangentAt_def.1 hL).2.2.1).1 hL)
    have hLα' : Associated L (X 1 - C α * X 0) :=
      associated_of_associated_dehomogenize (isTangentAt_def.1 hL).1 (hL1 α) (by rwa [hdeh])
    have hQα := haeq (hover hα) hα (Place.map_map_symm _ _)
    refine ⟨_, ⟨hover hα, by dsimp only; rwa [hQα]⟩, fun Q ⟨hQ, hLQ⟩ ↦ hinj hQ (hover hα) ?_⟩
    rw [hQα]
    have h2 := (hLα'.symm.trans hLQ).map (dehomogenize 2)
    rw [hdeh, hdeh] at h2
    exact (associated_X_one_sub_C_mul_X_zero_iff.1 h2).symm
  · -- a line through `P` that is not tangent
    intro L hL hL0 hLP hLT Q hQ
    have hPmk : P.1 = mk k (Fin.insertNth (α := fun _ ↦ k) 2 1 0)
        (Fin.insertNth_one_ne_zero 2 0) := by
      rw [← affineChart_symm_apply, ← h0]
      exact ((affineChart 2).left_inv (by rwa [affineChart_source])).symm
    have hLa : eval (Fin.insertNth (α := fun _ ↦ k) 2 1 0) L = 0 := by
      rw [← hL.eval_rep_mk_eq_zero_iff (Fin.insertNth_one_ne_zero 2 0), ← hPmk]
      exact hLP
    have hLh : (dehomogenize 2 L).IsHomogeneous 1 := by
      simpa only [taylor_zero] using isHomogeneous_taylor_dehomogenize 2 0 hL hLa
    rw [hordα hQ hL]
    exact Affine.addValuation_blowupPlace_eq_one hf hX h' (ha hQ).1 hLh
      (dehomogenize_ne_zero_of_isHomogeneous 2 hL hL0)
      ((isTangentAt_iff_dehomogenize hF hP h0 hL hLP).not.1 hLT)
  · -- (1)
    intro Q hQ
    rw [hordα hQ hG, hmult hG]
    exact ⟨Affine.natCast_orderAt_le_addValuation_blowupPlace hf hX h' (ha hQ).1 _,
      fun hGT ↦ (Affine.addValuation_blowupPlace_eq_iff hf hX h' (ha hQ).1
        (dehomogenize_ne_zero_of_isHomogeneous 2 hG hG0)).2 ((htan hG (a Q)).not.1 hGT)⟩
  · -- (2)
    intro s hs
    rw [hmult hF] at hs
    rw [hmult hG, Affine.le_orderAt_iff_forall_le_addValuation_blowupPlace hf hX h' hT'
      (dehomogenize_ne_zero_of_isHomogeneous 2 hG hG0) hs]
    refine ⟨fun H Q hQ ↦ ?_, fun H α hα ↦ ?_⟩
    · rw [hordα hQ hG]
      exact H _ (ha hQ).1
    · have := H _ (hover hα)
      rwa [hord (hover hα) hG, Place.map_map_symm] at this
  · -- (3)
    intro Q hQ
    have hd : dehomogenize 2 (pderiv 1 F) = pderiv 1 f := (pderiv_dehomogenize 2 1 F).symm
    rw [hordα hQ, hd, Affine.addValuation_blowupPlace_pderiv_one, hmult hF]


/-- The statement of the milestone moves along a change of coordinates. -/
private theorem ordinaryPlacesSpec_of_linearSubst (M : GL (Fin 3) k)
    {P' : zeroLocus (projectivePlaneCurve.ideal (hF.linearSubst M.1) :
      Set (MvPolynomial (Fin 3) k))}
    (hQP : map M.1.mulVecLin (Matrix.mulVec_injective_of_isUnit M.isUnit) P'.1 = P.1)
    (h : OrdinaryPlacesSpec (hF.linearSubst M.1) P') : OrdinaryPlacesSpec hF P := by
  set φ := functionField.linearSubstEquiv hF M
  have hM := Matrix.mulVec_injective_of_isUnit M.isUnit
  have hdet : IsUnit M.1.det := (Matrix.isUnit_iff_isUnit_det _).1 M.isUnit
  have hover {Q : Place k (functionField hF)} :
      Q.map φ ∈ placesOver (hF.linearSubst M.1) P' ↔ Q ∈ placesOver hF P :=
    by rw [mem_placesOver_iff, mem_placesOver_iff]; exact center_map_linearSubstEquiv_eq_iff hQP
  have hover' {R : Place k (functionField (hF.linearSubst M.1))} :
      R ∈ placesOver (hF.linearSubst M.1) P' ↔ R.map φ.symm ∈ placesOver hF P := by
    rw [← hover, Place.map_map_symm]
  have htan {m : ℕ} {G L : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous m) :
      IsTangentAt (linearSubst M.1 G) P'.1 (linearSubst M.1 L) ↔ IsTangentAt G P.1 L := by
    rw [isTangentAt_linearSubst_iff hG hM, hQP]
  have hmult {m : ℕ} {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous m) :
      mult (linearSubst M.1 G) P'.1 = mult G P.1 := by
    rw [mult_linearSubst hG hM, hQP]
  have hass {L L' : MvPolynomial (Fin 3) k} :
      Associated (linearSubst M.1 L) L' ↔ Associated L (linearSubst (M⁻¹).1 L') :=
    ⟨fun h ↦ by
      have := h.map (linearSubst (M⁻¹).1)
      rwa [linearSubst_inv_linearSubst] at this,
    fun h ↦ by
      have := h.map (linearSubst M.1)
      rwa [linearSubst_linearSubst_inv] at this⟩
  obtain ⟨hcard, L, hLt, hLu, hLl, hLG⟩ := h
  refine ⟨?_, fun Q ↦ linearSubst (M⁻¹).1 (L (Q.map φ)), fun Q hQ ↦ ?_, fun L' hL' ↦ ?_,
    fun hL hL0 hLP hLT Q hQ ↦ ?_, fun hG hG0 ↦ ?_⟩
  · rw [← hmult hF, ← hcard, placesOver_linearSubst hQP,
      Set.ncard_image_of_injective _ (Function.LeftInverse.injective (Place.map_symm_map φ))]
  · rw [← htan hF, linearSubst_linearSubst_inv]
    exact hLt _ (hover.2 hQ)
  · obtain ⟨R, ⟨hR, hLR⟩, hu⟩ := hLu _ ((htan hF).2 hL')
    refine ⟨R.map φ.symm, ⟨hover'.1 hR, by dsimp only; rwa [Place.map_map_symm, ← hass]⟩,
      fun Q ⟨hQ, hLQ⟩ ↦ ?_⟩
    rw [← hu (Q.map φ) ⟨hover.2 hQ, hass.2 hLQ⟩, Place.map_symm_map]
  · rw [← ordForm_linearSubst (M := M)]
    refine hLl (hL.linearSubst M.1) ((map_ne_zero_iff _ (linearSubst_injective hdet)).2 hL0)
      ?_ (by rwa [htan hF]) _ (hover.2 hQ)
    rwa [eval_rep_linearSubst_eq_zero_iff M hL, hQP]
  · obtain ⟨h1, h2⟩ := hLG (hG.linearSubst M.1)
      ((map_ne_zero_iff _ (linearSubst_injective hdet)).2 hG0)
    refine ⟨fun Q hQ ↦ ?_, fun s hs ↦ ?_⟩
    · rw [← ordForm_linearSubst (M := M), ← hmult hG]
      refine ⟨(h1 _ (hover.2 hQ)).1, fun hT ↦ (h1 _ (hover.2 hQ)).2 ?_⟩
      rwa [← linearSubst_linearSubst_inv M (L (Q.map φ)), htan hG]
    · rw [← hmult hF] at hs
      rw [← hmult hG, h2 s hs]
      refine ⟨fun H Q hQ ↦ ?_, fun H R hR ↦ ?_⟩
      · rw [← ordForm_linearSubst (M := M)]
        exact H _ (hover.2 hQ)
      · have := H _ (hover'.1 hR)
        rwa [← ordForm_linearSubst (M := M), Place.map_map_symm] at this


/-- The milestone's statement holds at every ordinary multiple point. -/
private theorem ordinaryPlacesSpec (h : IsOrdinaryMultiplePoint F P.1) :
    OrdinaryPlacesSpec hF P := by
  obtain ⟨c, hcP, hcT⟩ := ((infinite_setOf_eval_sum_C_mul_X_eq_zero P.1).sdiff
    (finite_setOf_isTangentAt (Fact.out : Irreducible F).ne_zero P.1)).nonempty
  obtain ⟨M, hMP, hMX⟩ := exists_map_eq_and_linearSubst_eq_X_zero P.1 hcP
  have hM := Matrix.mulVec_injective_of_isUnit M.isUnit
  have hO : mk k (Pi.single 2 1) (by simp) ∈ zeroLocus
      (projectivePlaneCurve.ideal (hF.linearSubst M.1) : Set (MvPolynomial (Fin 3) k)) := by
    rw [mem_zeroLocus_ideal_iff, eval_rep_linearSubst_eq_zero_iff M hF, hMP]
    exact (mem_zeroLocus_ideal_iff hF).1 P.2
  refine ordinaryPlacesSpec_of_linearSubst M (P' := ⟨_, hO⟩) hMP
    (ordinaryPlacesSpec_of_chart ?_ ((mk_mem_affineOpen_iff _ _ _).2 (by simp))
      (affineChart_mk_single 2) ?_).1
  · rwa [isOrdinaryMultiplePoint_linearSubst_iff hF hM, hMP]
  · rw [← hMX, isTangentAt_linearSubst_iff hF hM, hMP]
    exact hcT

variable {m : ℕ} {G : MvPolynomial (Fin 3) k} {Q : Place k (functionField hF)}

/-- **The number of places over an ordinary multiple point.** Exactly `m_P(F)` places of `k(C)`
lie over an ordinary multiple point `P` of `C`. -/
theorem ncard_placesOver_of_isOrdinaryMultiplePoint (h : IsOrdinaryMultiplePoint F P.1) :
    (placesOver hF P).ncard = (mult F P.1).toNat :=
  (ordinaryPlacesSpec h).1

/-- **The places over an ordinary multiple point and its tangents.** At an ordinary multiple
point `P` of `C`, each place `Q` over `P` has a tangent `L_Q` of `C` at `P`, and `Q ↦ L_Q` is a
bijection from the places over `P` onto the tangents of `C` at `P` taken up to associates. A
nonzero form `G` has order `m_P(G)` at `Q` if `L_Q` is not tangent to `G` at `P`. -/
theorem exists_isTangentAt_and_ordForm_eq_mult (h : IsOrdinaryMultiplePoint F P.1) :
    ∃ L : Place k (functionField hF) → MvPolynomial (Fin 3) k,
      (∀ Q ∈ placesOver hF P, IsTangentAt F P.1 (L Q)) ∧
      (∀ L', IsTangentAt F P.1 L' → ∃! Q, Q ∈ placesOver hF P ∧ Associated L' (L Q)) ∧
      ∀ {m : ℕ} {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous m), G ≠ 0 →
        ∀ Q ∈ placesOver hF P, ¬IsTangentAt G P.1 (L Q) →
          ordForm hF Q hG = (mult G P.1).toNat := by
  obtain ⟨-, L, hLt, hLu, -, hLG⟩ := ordinaryPlacesSpec h
  exact ⟨L, hLt, hLu, fun hG hG0 Q hQ ↦ ((hLG hG hG0).1 Q hQ).2⟩

/-- At a place over an ordinary multiple point `P`, a nonzero form `G` has order at least its
multiplicity `m_P(G)`. -/
theorem natCast_toNat_mult_le_ordForm (h : IsOrdinaryMultiplePoint F P.1)
    (hG : G.IsHomogeneous m) (hG0 : G ≠ 0) (hQ : Q ∈ placesOver hF P) :
    ((mult G P.1).toNat : WithTop ℤ) ≤ ordForm hF Q hG :=
  (((ordinaryPlacesSpec h).2.choose_spec.2.2.2 hG hG0).1 Q hQ).1

/-- **Multiplicities from orders over an ordinary multiple point.** Let `P` be an ordinary
multiple point of `C`. For a nonzero form `G` and `s ≤ m_P(F)`, `m_P(G) ≥ s` iff `G` has order
at least `s` at every place over `P`. -/
theorem le_mult_iff_forall_le_ordForm (h : IsOrdinaryMultiplePoint F P.1)
    (hG : G.IsHomogeneous m) (hG0 : G ≠ 0) {s : ℕ} (hs : (s : ℕ∞) ≤ mult F P.1) :
    (s : ℕ∞) ≤ mult G P.1 ↔ ∀ Q ∈ placesOver hF P, (s : WithTop ℤ) ≤ ordForm hF Q hG :=
  ((ordinaryPlacesSpec h).2.choose_spec.2.2.2 hG hG0).2 s hs

/-- **Lines at the places over an ordinary multiple point.** A line through an ordinary multiple
point `P` of `C` that is not tangent to `C` there has order one at every place over `P`. -/
theorem ordForm_eq_one_of_not_isTangentAt (h : IsOrdinaryMultiplePoint F P.1)
    {L : MvPolynomial (Fin 3) k} (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0)
    (hLP : eval P.1.rep L = 0) (hLF : ¬IsTangentAt F P.1 L) (hQ : Q ∈ placesOver hF P) :
    ordForm hF Q hL = 1 :=
  (ordinaryPlacesSpec h).2.choose_spec.2.2.1 hL hL0 hLP hLF Q hQ

/-- **The partial derivative `∂F/∂Y` at the places over an ordinary multiple point.** Let `P`, in
the chart `Z ≠ 0` with affine coordinates `(0, 0)`, be an ordinary multiple point of `C` at which
`X = 0` is not tangent. Then `∂F/∂Y` has order `m_P(F) - 1` at every place over `P`, in every
characteristic. -/
theorem ordForm_pderiv_one (h : IsOrdinaryMultiplePoint F P.1) (hP : P.1 ∈ affineOpen 2)
    (h0 : affineChart 2 P.1 = 0) (hT : ¬IsTangentAt F P.1 (X 0)) (hQ : Q ∈ placesOver hF P) :
    ordForm hF Q (hF.pderiv (i := 1)) = ((mult F P.1).toNat - 1 : ℕ) :=
  (ordinaryPlacesSpec_of_chart h hP h0 hT).2 Q hQ

/-- **Orders at the places over an ordinary multiple point.** Let `k` be algebraically closed,
`C : F = 0` an irreducible projective plane curve and `P` an ordinary multiple point of `C`, of
multiplicity `r = m_P(F)`.

* Exactly `r` places of `k(C)` lie over `P`, and there is a tangent `L_Q` of `C` at `P` for each
  place `Q` over `P` such that `Q ↦ L_Q` is a bijection onto the tangents of `C` at `P`, taken up
  to associates.
* A line through `P` that is not tangent to `C` has order `1` at every place over `P`.

For every nonzero form `G` (in particular every `G` of which `C` is not a component), and every
place `Q` over `P`:

1. `ord_Q(G) ≥ m_P(G)`, with equality if `L_Q` is not tangent to `G` at `P`;
2. for `s ≤ r`, `m_P(G) ≥ s` iff `ord_Q(G) ≥ s` for every `Q` over `P`;
3. if `P = [0 : 0 : 1]`, that is the point `(0, 0)` of the chart `Z ≠ 0`, and `X = 0` is not
   tangent to `C` at `P`, then `ord_Q(∂F/∂Y) = r - 1`.

Milestone: *Orders at the places over an ordinary multiple point*. -/
theorem IsOrdinaryMultiplePoint.placesOver_spec (h : IsOrdinaryMultiplePoint F P.1) :
    (placesOver hF P).ncard = (mult F P.1).toNat ∧
    (∃ L : Place k (functionField hF) → MvPolynomial (Fin 3) k,
      (∀ Q ∈ placesOver hF P, IsTangentAt F P.1 (L Q)) ∧
      (∀ L', IsTangentAt F P.1 L' → ∃! Q, Q ∈ placesOver hF P ∧ Associated L' (L Q)) ∧
      ∀ {m : ℕ} {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous m), G ≠ 0 →
        ∀ Q ∈ placesOver hF P, ¬IsTangentAt G P.1 (L Q) →
          ordForm hF Q hG = (mult G P.1).toNat) ∧
    (∀ {L : MvPolynomial (Fin 3) k} (hL : L.IsHomogeneous 1), L ≠ 0 → eval P.1.rep L = 0 →
      ¬IsTangentAt F P.1 L → ∀ Q ∈ placesOver hF P, ordForm hF Q hL = 1) ∧
    -- (1)
    (∀ {m : ℕ} {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous m), G ≠ 0 →
      ∀ Q ∈ placesOver hF P, ((mult G P.1).toNat : WithTop ℤ) ≤ ordForm hF Q hG) ∧
    -- (2)
    (∀ {m : ℕ} {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous m), G ≠ 0 →
      ∀ s : ℕ, (s : ℕ∞) ≤ mult F P.1 →
        ((s : ℕ∞) ≤ mult G P.1 ↔ ∀ Q ∈ placesOver hF P, (s : WithTop ℤ) ≤ ordForm hF Q hG)) ∧
    -- (3)
    (P.1 ∈ affineOpen 2 → affineChart 2 P.1 = 0 → ¬IsTangentAt F P.1 (X 0) →
      ∀ Q ∈ placesOver hF P,
        ordForm hF Q (hF.pderiv (i := 1)) = ((mult F P.1).toNat - 1 : ℕ)) :=
  ⟨ncard_placesOver_of_isOrdinaryMultiplePoint h, exists_isTangentAt_and_ordForm_eq_mult h,
    fun hL hL0 hLP hLF _ hQ ↦ ordForm_eq_one_of_not_isTangentAt h hL hL0 hLP hLF hQ,
    fun hG hG0 _ hQ ↦ natCast_toNat_mult_le_ordForm h hG hG0 hQ,
    fun hG hG0 _ hs ↦ le_mult_iff_forall_le_ordForm h hG hG0 hs,
    fun hP h0 hT _ hQ ↦ ordForm_pderiv_one h hP h0 hT hQ⟩

end PlaneCurves.Projective

end
