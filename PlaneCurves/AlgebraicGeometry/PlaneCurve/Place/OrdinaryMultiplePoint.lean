/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.Blowup.Chart
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Place.SimplePoint
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

## Main definitions

* `PlaneCurves.Affine.blowupPlace hF hX h hα`: the place of `k(F)` over the origin corresponding
  to the tangent `Y - α X`.

## Main results

* `PlaneCurves.AffineSpace.valuation_algebraMap_mk_sub_lt_one`: if the valuation ring of a place
  `Q` of `k(V)` contains `𝒪_P(V)`, then every polynomial `g` agrees with `g(P)` to first order
  at `Q`; `valuation_algebraMap_mk_eq_one` for `g(P) ≠ 0`.
* `PlaneCurves.Affine.valuation_blowupPlace`, `PlaneCurves.Affine.addValuation_blowupPlace`: the
  valuation and the order of `blowupPlace` are those of the place at `(0, α)` of `F'`.
* `PlaneCurves.Affine.localSubring_le_integers_blowupPlace`: `blowupPlace` lies over the origin.
* `PlaneCurves.Affine.valuation_blowupPlace_div_sub_lt_one`, `eq_of_blowupPlace_eq`: `y / x - α`
  has positive order at the place over `Y - α X`, so distinct tangents give distinct places.
* `PlaneCurves.Affine.existsUnique_eq_blowupPlace`: every place over the origin is `blowupPlace`
  for exactly one tangent.
* `PlaneCurves.Affine.addValuation_x_blowupPlace`: `x` has order one at each `blowupPlace`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.2, Problems 7.4, 7.5
-/

public section

open MvPolynomial TauCeti

/-! ### Places over a point of an affine variety -/

namespace PlaneCurves.AffineSpace

variable {k σ : Type*} [Field k] {I : Ideal (MvPolynomial σ k)} [I.IsPrime] {P : σ → k}
  {hI : I ≤ vanishingIdeal k {P}} {Q : Place k (functionField I)}

/-- If the valuation ring of a place `Q` of `k(V)` contains the local ring `𝒪_P(V)`, then every
polynomial `g` with `g(P) ≠ 0` has valuation one at `Q`: it is a unit of `𝒪_P(V)`. -/
theorem valuation_algebraMap_mk_eq_one (hQ : (localSubring P hI).toSubring ≤ Q.integers.toSubring)
    {g : MvPolynomial σ k} (hg : eval P g ≠ 0) :
    Q.valuation (algebraMap _ _ (Ideal.Quotient.mk I g)) = 1 := by
  have h0 := algebraMap_mk_ne_zero hI hg
  have hinv : (algebraMap _ (functionField I) (Ideal.Quotient.mk I g))⁻¹ ∈ Q.integers :=
    hQ ((mem_localSubring_iff P hI).2 ⟨1, g, hg, by simp⟩)
  have hu : IsUnit (⟨_, hQ (algebraMap_mem_localSubring P hI _)⟩ : Q.integers) :=
    (Units.mkOfMulEqOne _ ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ h0))).isUnit
  exact Q.isUnit_iff_valuation_eq_one.1 hu

variable [IsAlgClosed k]

/-- **Values at a place over a point.** If the valuation ring of a place `Q` of the function field
`k(V)` of a variety contains the local ring `𝒪_P(V)`, then every polynomial `g` agrees at `Q` with
its value `g(P)` to first order: `v_Q(g - g(P)) < 1`. -/
theorem valuation_algebraMap_mk_sub_lt_one (hK : IsFunctionField k (functionField I))
    (hQ : (localSubring P hI).toSubring ≤ Q.integers.toSubring) (g : MvPolynomial σ k) :
    Q.valuation (algebraMap _ _ (Ideal.Quotient.mk I g) - algebraMap k _ (eval P g)) < 1 := by
  obtain ⟨c, hc⟩ := (Q.degree_eq_one_iff_forall_exists_valuation_sub_lt_one.1
    (Q.degree_eq_one_of_isAlgClosed_of_isFunctionField hK)) _
    (hQ (algebraMap_mem_localSubring P hI (Ideal.Quotient.mk I g)))
  obtain rfl | hne := eq_or_ne c (eval P g)
  · exact hc
  have h1 := valuation_algebraMap_mk_eq_one hQ (g := g - C c)
    (by simpa [sub_eq_zero] using hne.symm)
  have hC : algebraMap _ (functionField I) (Ideal.Quotient.mk I (C c)) = algebraMap k _ c := by
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial σ k ⧸ I)]
    rfl
  rw [map_sub, map_sub, hC] at h1
  exact absurd hc (by rw [h1]; exact lt_irrefl 1)

end PlaneCurves.AffineSpace

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
  have := isPrime_span_blowupStrictTransform hF hX
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
  -- `z = y / x` is integral over `𝒪_Q`, hence in `𝒪_Q`.
  have hzQ : y / x ∈ Q.integers := by
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
  have hK := isFunctionField_functionField_span_singleton hF
  obtain ⟨α, hα⟩ := (Q.degree_eq_one_iff_forall_exists_valuation_sub_lt_one.1
    (Q.degree_eq_one_of_isAlgClosed_of_isFunctionField hK)) _ hzQ
  -- At `Q`, polynomials in `x` and `z` take their values at `(0, α)`.
  have hψ := Q.valuation_aeval_sub_lt_one (u := ![⟨x, hxQ⟩, ⟨y / x, hzQ⟩]) (p := ![0, α])
    fun i ↦ by
      fin_cases i
      · simpa using AffineSpace.valuation_algebraMap_mk_sub_lt_one hK hQ (X 0)
      · exact hα
  have he (g : MvPolynomial (Fin 2) k) :
      ((aeval ![(⟨x, hxQ⟩ : Q.integers), ⟨y / x, hzQ⟩] g : Q.integers) :
        functionField (Ideal.span {F})) = (blowupFunctionFieldEquiv hF hX).symm
          (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {blowupStrictTransform F}) g)) := by
    rw [coe_aeval_integers, blowupFunctionFieldEquiv_symm_algebraMap_mk]
    rfl
  have hαT : IsTangentAt F 0 (X 1 - C α * X 0) := by
    rw [← eval_zero_blowupStrictTransform_eq_zero_iff h.ne_zero]
    by_contra hne
    have h1 := hψ (blowupStrictTransform F)
    rw [he, Ideal.Quotient.mk_singleton_self, map_zero, map_zero, zero_sub, Valuation.map_neg,
      Q.isTrivialOn.eq_one _ hne] at h1
    exact lt_irrefl _ h1
  refine ⟨α, ⟨hαT, ?_⟩, fun β ⟨hβ, hQβ⟩ ↦ Place.eq_of_valuation_sub_lt_one Q
    (hQβ ▸ valuation_blowupPlace_div_sub_lt_one hF hX h hβ) hα⟩
  have hP := (h.isSimplePoint_blowupStrictTransform hαT).1
  have hle : (placeAt hP).integers ≤ (Q.map (blowupFunctionFieldEquiv hF hX)).integers := by
    intro f hf
    rw [← ValuationSubring.mem_toSubring, integers_toSubring_placeAt, mem_localSubring_iff] at hf
    obtain ⟨a, b, hb, rfl⟩ := hf
    rw [Place.mem_integers_map_iff, map_div₀, ← he, ← he, Place.mem_integers_iff, map_div₀]
    have hb1 := Valuation.map_eq_of_sub_lt Q.valuation
      (by rw [Q.isTrivialOn.eq_one _ hb]; exact hψ b)
    rw [Q.isTrivialOn.eq_one _ hb] at hb1
    rw [hb1, div_one]
    exact Q.mem_integers_iff.1
      (aeval ![(⟨x, hxQ⟩ : Q.integers), ⟨y / x, hzQ⟩] a).2
  rw [blowupPlace_def, Place.eq_of_integers_le hle, Place.map_symm_map]

end PlaneCurves.Affine

end
