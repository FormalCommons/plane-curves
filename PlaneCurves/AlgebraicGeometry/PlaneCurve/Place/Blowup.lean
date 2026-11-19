/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.AffineSpace.Place
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.Blowup.Chart
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Place.SimplePoint
public import PlaneCurves.FieldTheory.FunctionField.Place.AddValuation
public import PlaneCurves.FieldTheory.FunctionField.Place.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Map

/-!
# The places over the origin through the blow-up chart

Let `k` be a field and `F` an irreducible affine plane curve, other than the line `X = 0`, through
the origin. Let `K = k(F)` be its function field, `x, y` the coordinate functions, and `F'` the
strict transform of `F` under the blow-up of the origin, with function field `k(F') ≅ K`
(`blowupFunctionFieldEquiv`: `x ↦ x`, `z ↦ y / x`). Nothing is assumed about the singularity of `F`
at the origin.

If `X = 0` is not tangent to `F` at the origin, then `z = y / x` lies in the valuation ring of every
place `Q` of `K` over the origin: it is a root of the monic polynomial obtained from
`F(x, xz) = x ^ r F'(x, z)` (`Affine/Blowup/Chart.lean`). Over an algebraically closed field `z`
then takes a value `α` at `Q`, and `Q`, read in `k(F')`, lies over the point `(0, α)` of `F'` on
the exceptional line. Conversely every place of `k(F')` over a point `(0, α)` of `F'` lies, read in
`K`, over the origin, and `z` takes the value `α` there. So the places of `K` over the origin are
the places of `k(F')` over the points of the fibre `F' = 0, X = 0`, each over exactly one of them.

At every place `Q` of `K`, a polynomial `G` of multiplicity `s` at the origin, with strict
transform `G'`, has order `s · ord_Q(x) + ord_Q(G'(x, z))`, from `G(x, xz) = x ^ s G'(x, z)`.

## Main results

* `PlaneCurves.Affine.div_mem_integers_of_localSubring_le`: `z = y / x` lies in the valuation
  ring of every place over the origin, if `X = 0` is not tangent.
* `PlaneCurves.Affine.localSubring_le_integers_map_symm`,
  `PlaneCurves.Affine.valuation_map_symm_div_sub_lt_one`: a place of `k(F')` over `(0, α)` lies
  over the origin, and `z` takes the value `α` there.
* `PlaneCurves.Affine.eval_blowupStrictTransform_eq_zero_of_valuation_div_sub_lt_one`,
  `PlaneCurves.Affine.localSubring_le_integers_map_of_valuation_div_sub_lt_one`: a place over the
  origin at which `z` takes the value `α` lies over the point `(0, α)` of `F'`.
* `PlaneCurves.Affine.localSubring_le_integers_iff`,
  `PlaneCurves.Affine.existsUnique_localSubring_le_integers_map`: a place lies over the origin iff
  it lies over a point `(0, α)` of `F'`, and that `α` is unique.
* `PlaneCurves.Affine.setOf_localSubring_le_integers_eq_iUnion`,
  `PlaneCurves.Affine.pairwise_disjoint_setOf_localSubring_le_integers`: the places over the
  origin are the union, over the points `(0, α)` of `F'`, of the places over them, and the union
  is disjoint.
* `PlaneCurves.Affine.addValuation_algebraMap_mk_eq_nsmul_add`: orders of polynomials through the
  chart.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.2, §7.4
-/

public section

open MvPolynomial TauCeti

namespace PlaneCurves.Affine

open AffineSpace

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 2) k} [(Ideal.span {F}).IsPrime]
  (hF : Irreducible F) (hX : ¬Associated F (X 0))

/-! ### `z = y / x` at the places over the origin -/

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
/-- **`z = y / x` is integral at a place over the origin.** If the curve `F` passes through the
origin and `X = 0` is not tangent to it there, then `y / x` lies in the valuation ring of every
place of `k(F)` over the origin: it is a root of a monic polynomial over `𝒪_0(F)`. -/
theorem div_mem_integers_of_localSubring_le (h0 : eval 0 F = 0) (hT : ¬IsTangentAt F 0 (X 0))
    {Q : Place k (functionField (Ideal.span {F}))}
    (hQ : (AffineSpace.localSubring 0 (span_le_vanishingIdeal h0)).toSubring ≤
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

/-- An element that agrees with a constant to first order at a place lies in its valuation
ring. -/
private theorem mem_integers_of_valuation_sub_lt_one {K : Type*} [Field K] [Algebra k K]
    {Q : Place k K} {f : K} {c : k} (hc : Q.valuation (f - algebraMap k K c) < 1) :
    f ∈ Q.integers := by
  have h := add_mem (Q.mem_integers_iff.2 hc.le) (Q.algebraMap_mem_integers c)
  rwa [sub_add_cancel] at h

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

omit [(Ideal.span {F}).IsPrime] in
/-- `G(X, XZ)` takes at `(0, α)` the value of `G` at the origin. -/
private theorem eval_aeval_X_X_mul_X (α : k) (g : MvPolynomial (Fin 2) k) :
    eval ![0, α] (aeval ![X 0, X 0 * X 1] g) = eval 0 g := by
  refine (aeval_bind₁ ![0, α] ![X 0, X 0 * X 1] g).trans ?_
  change aeval _ g = aeval _ g
  congr 1
  ext i : 1
  fin_cases i <;> simp

/-! ### The places of `k(F')` over the fibre lie over the origin -/

/-- **The places over the fibre lie over the origin.** A place of `k(F')` over a point `(0, α)` of
the strict transform, read in `k(F)`, lies over the origin. -/
theorem localSubring_le_integers_map_symm [(Ideal.span {blowupStrictTransform F}).IsPrime]
    (h0 : eval 0 F = 0) {α : k} (hα : eval ![0, α] (blowupStrictTransform F) = 0)
    {Q : Place k (functionField (Ideal.span {blowupStrictTransform F}))}
    (hQ : (AffineSpace.localSubring ![0, α] (span_le_vanishingIdeal hα)).toSubring ≤
      Q.integers.toSubring) :
    (AffineSpace.localSubring 0 (span_le_vanishingIdeal h0)).toSubring ≤
      (Q.map (blowupFunctionFieldEquiv hF hX).symm).integers.toSubring := by
  intro f hf
  obtain ⟨a, b, hb, rfl⟩ := (mem_localSubring_iff _ _).1 hf
  change _ ∈ (Q.map (blowupFunctionFieldEquiv hF hX).symm).integers
  rw [Place.mem_integers_map_iff, AlgEquiv.symm_symm]
  refine hQ ((mem_localSubring_iff _ _).2
    ⟨aeval ![X 0, X 0 * X 1] a, aeval ![X 0, X 0 * X 1] b, ?_, by simp [map_div₀]⟩)
  rwa [eval_aeval_X_X_mul_X]

variable [IsAlgClosed k]

/-- At a place of `k(F')` over the point `(0, α)` of the strict transform, read in `k(F)`, the
function `z = y / x` takes the value `α`. -/
theorem valuation_map_symm_div_sub_lt_one [(Ideal.span {blowupStrictTransform F}).IsPrime]
    {α : k} (hα : eval ![0, α] (blowupStrictTransform F) = 0)
    {Q : Place k (functionField (Ideal.span {blowupStrictTransform F}))}
    (hQ : (AffineSpace.localSubring ![0, α] (span_le_vanishingIdeal hα)).toSubring ≤
      Q.integers.toSubring) :
    (Q.map (blowupFunctionFieldEquiv hF hX).symm).valuation
      (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 1)) /
        algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0)) - algebraMap k _ α) < 1 := by
  rw [Place.valuation_map, AlgEquiv.symm_symm, map_sub, AlgEquiv.commutes,
    ← blowupFunctionFieldEquiv_symm_z hF hX, AlgEquiv.apply_symm_apply]
  simpa using AffineSpace.valuation_algebraMap_mk_sub_lt_one
    (isFunctionField_functionField_span_singleton (irreducible_blowupStrictTransform hF hX)) hQ
    (X 1)

/-! ### The places over the origin lie over the fibre -/

include hF hX in
/-- At a place `Q` over the origin at which `z = y / x` takes the value `α`, every function
`G(x, z)` on the strict transform takes its value `G(0, α)`. -/
theorem valuation_blowupFunctionFieldEquiv_symm_sub_lt_one
    [(Ideal.span {blowupStrictTransform F}).IsPrime] (h0 : eval 0 F = 0)
    {Q : Place k (functionField (Ideal.span {F}))}
    (hQ : (AffineSpace.localSubring 0 (span_le_vanishingIdeal h0)).toSubring ≤
      Q.integers.toSubring) {α : k}
    (hα : Q.valuation (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 1)) /
      algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0)) - algebraMap k _ α) < 1)
    (g : MvPolynomial (Fin 2) k) :
    Q.valuation ((blowupFunctionFieldEquiv hF hX).symm
        (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {blowupStrictTransform F}) g)) -
      algebraMap k _ (eval ![0, α] g)) < 1 := by
  have hxQ := hQ (algebraMap_mem_localSubring _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0)))
  rw [← coe_aeval_eq_blowupFunctionFieldEquiv_symm hF hX hxQ
    (mem_integers_of_valuation_sub_lt_one hα)]
  refine Q.valuation_aeval_sub_lt_one (fun i ↦ ?_) g
  fin_cases i
  · simpa using AffineSpace.valuation_algebraMap_mk_sub_lt_one
      (isFunctionField_functionField_span_singleton hF) hQ (X 0)
  · exact hα

include hF hX in
/-- At a place over the origin, `z = y / x` can only take a value `α` with `(0, α)` on the strict
transform. -/
theorem eval_blowupStrictTransform_eq_zero_of_valuation_div_sub_lt_one (h0 : eval 0 F = 0)
    {Q : Place k (functionField (Ideal.span {F}))}
    (hQ : (AffineSpace.localSubring 0 (span_le_vanishingIdeal h0)).toSubring ≤
      Q.integers.toSubring) {α : k}
    (hα : Q.valuation (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 1)) /
      algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0)) - algebraMap k _ α) < 1) :
    eval ![0, α] (blowupStrictTransform F) = 0 := by
  have := isPrime_span_blowupStrictTransform hF hX
  by_contra hne
  have h1 := valuation_blowupFunctionFieldEquiv_symm_sub_lt_one hF hX h0 hQ hα
    (blowupStrictTransform F)
  rw [Ideal.Quotient.mk_singleton_self, map_zero, map_zero, zero_sub, Valuation.map_neg,
    Q.isTrivialOn.eq_one _ hne] at h1
  exact lt_irrefl _ h1

/-- A place `Q` over the origin at which `z = y / x` takes the value `α`, read in `k(F')`, lies
over the point `(0, α)` of the strict transform. -/
theorem localSubring_le_integers_map_of_valuation_div_sub_lt_one
    [(Ideal.span {blowupStrictTransform F}).IsPrime] (h0 : eval 0 F = 0)
    {Q : Place k (functionField (Ideal.span {F}))}
    (hQ : (AffineSpace.localSubring 0 (span_le_vanishingIdeal h0)).toSubring ≤
      Q.integers.toSubring) {α : k}
    (hα : Q.valuation (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 1)) /
      algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0)) - algebraMap k _ α) < 1) :
    (AffineSpace.localSubring ![0, α] (span_le_vanishingIdeal
      (eval_blowupStrictTransform_eq_zero_of_valuation_div_sub_lt_one hF hX h0 hQ hα))).toSubring ≤
      (Q.map (blowupFunctionFieldEquiv hF hX)).integers.toSubring := by
  have hψ := valuation_blowupFunctionFieldEquiv_symm_sub_lt_one hF hX h0 hQ hα
  have hxQ := hQ (algebraMap_mem_localSubring _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0)))
  have hzQ := mem_integers_of_valuation_sub_lt_one hα
  intro f hf
  obtain ⟨a, b, hb, rfl⟩ := (mem_localSubring_iff _ _).1 hf
  change _ ∈ (Q.map (blowupFunctionFieldEquiv hF hX)).integers
  rw [Place.mem_integers_map_iff, map_div₀, Place.mem_integers_iff, map_div₀]
  have hb1 := Valuation.map_eq_of_sub_lt Q.valuation
    (by rw [Q.isTrivialOn.eq_one _ hb]; exact hψ b)
  rw [Q.isTrivialOn.eq_one _ hb] at hb1
  rw [hb1, div_one, ← coe_aeval_eq_blowupFunctionFieldEquiv_symm hF hX hxQ hzQ]
  exact Q.mem_integers_iff.1 (aeval ![(⟨_, hxQ⟩ : Q.integers), ⟨_, hzQ⟩] a).2

/-! ### The places over the origin are the places over the fibre -/

/-- **The places over the origin through the chart.** If `X = 0` is not tangent to `F` at the
origin, a place `Q` of `k(F)` lies over the origin if and only if, read in `k(F')`, it lies over
a point `(0, α)` of the strict transform. -/
theorem localSubring_le_integers_iff [(Ideal.span {blowupStrictTransform F}).IsPrime]
    (h0 : eval 0 F = 0) (hT : ¬IsTangentAt F 0 (X 0))
    {Q : Place k (functionField (Ideal.span {F}))} :
    (AffineSpace.localSubring 0 (span_le_vanishingIdeal h0)).toSubring ≤ Q.integers.toSubring ↔
      ∃ (α : k) (hα : eval ![0, α] (blowupStrictTransform F) = 0),
        (AffineSpace.localSubring ![0, α] (span_le_vanishingIdeal hα)).toSubring ≤
          (Q.map (blowupFunctionFieldEquiv hF hX)).integers.toSubring := by
  refine ⟨fun hQ ↦ ?_, fun ⟨α, hα, hQ⟩ ↦ ?_⟩
  · obtain ⟨α, hα⟩ := (Q.degree_eq_one_iff_forall_exists_valuation_sub_lt_one.1
      (Q.degree_eq_one_of_isAlgClosed_of_isFunctionField
        (isFunctionField_functionField_span_singleton hF))) _
      (div_mem_integers_of_localSubring_le hF hX h0 hT hQ)
    exact ⟨α, eval_blowupStrictTransform_eq_zero_of_valuation_div_sub_lt_one hF hX h0 hQ hα,
      localSubring_le_integers_map_of_valuation_div_sub_lt_one hF hX h0 hQ hα⟩
  · have h := localSubring_le_integers_map_symm hF hX h0 hα hQ
    rwa [Place.map_symm_map] at h

/-- **The point of the fibre under a place over the origin.** If `X = 0` is not tangent to `F` at
the origin, every place `Q` of `k(F)` over the origin lies, read in `k(F')`, over exactly one
point `(0, α)` of the strict transform; `α` is the value of `z = y / x` at `Q`. -/
theorem existsUnique_localSubring_le_integers_map [(Ideal.span {blowupStrictTransform F}).IsPrime]
    (h0 : eval 0 F = 0) (hT : ¬IsTangentAt F 0 (X 0))
    {Q : Place k (functionField (Ideal.span {F}))}
    (hQ : (AffineSpace.localSubring 0 (span_le_vanishingIdeal h0)).toSubring ≤
      Q.integers.toSubring) :
    ∃! α : k, ∃ hα : eval ![0, α] (blowupStrictTransform F) = 0,
      (AffineSpace.localSubring ![0, α] (span_le_vanishingIdeal hα)).toSubring ≤
        (Q.map (blowupFunctionFieldEquiv hF hX)).integers.toSubring := by
  obtain ⟨α, hα, hQα⟩ := (localSubring_le_integers_iff hF hX h0 hT).1 hQ
  refine ⟨α, ⟨hα, hQα⟩, fun β ⟨hβ, hQβ⟩ ↦ ?_⟩
  have h := valuation_map_symm_div_sub_lt_one hF hX hα hQα
  have h' := valuation_map_symm_div_sub_lt_one hF hX hβ hQβ
  rw [Place.map_symm_map] at h h'
  exact Place.eq_of_valuation_sub_lt_one Q h' h

/-- **The places over the origin.** If `X = 0` is not tangent to `F` at the origin, the places of
`k(F)` over the origin are the places of `k(F')` over the points `(0, α)` of the strict transform,
read in `k(F)`. -/
theorem setOf_localSubring_le_integers_eq_iUnion [(Ideal.span {blowupStrictTransform F}).IsPrime]
    (h0 : eval 0 F = 0) (hT : ¬IsTangentAt F 0 (X 0)) :
    {Q : Place k (functionField (Ideal.span {F})) |
      (AffineSpace.localSubring 0 (span_le_vanishingIdeal h0)).toSubring ≤
        Q.integers.toSubring} =
      ⋃ α : k, (fun Q' : Place k (functionField (Ideal.span {blowupStrictTransform F})) ↦
          Q'.map (blowupFunctionFieldEquiv hF hX).symm) ''
        {Q' | ∃ hα : eval ![0, α] (blowupStrictTransform F) = 0,
          (AffineSpace.localSubring ![0, α] (span_le_vanishingIdeal hα)).toSubring ≤
            Q'.integers.toSubring} := by
  ext Q
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image]
  rw [localSubring_le_integers_iff hF hX h0 hT]
  constructor
  · rintro ⟨α, hα, hQ⟩
    exact ⟨α, _, ⟨hα, hQ⟩, Place.map_symm_map _ _⟩
  · rintro ⟨α, Q', ⟨hα, hQ'⟩, rfl⟩
    exact ⟨α, hα, by rwa [Place.map_map_symm]⟩

omit [(Ideal.span {F}).IsPrime] in
include hF hX in
/-- The places of `k(F')` over distinct points `(0, α)` of the strict transform are distinct. -/
theorem pairwise_disjoint_setOf_localSubring_le_integers
    [(Ideal.span {blowupStrictTransform F}).IsPrime] :
    Pairwise (Function.onFun Disjoint fun α : k ↦
      {Q' : Place k (functionField (Ideal.span {blowupStrictTransform F})) |
        ∃ hα : eval ![0, α] (blowupStrictTransform F) = 0,
          (AffineSpace.localSubring ![0, α] (span_le_vanishingIdeal hα)).toSubring ≤
            Q'.integers.toSubring}) := by
  intro α β hne
  refine Set.disjoint_left.2 fun Q ⟨hα, hQα⟩ ⟨hβ, hQβ⟩ ↦ hne ?_
  simpa using congrFun (AffineSpace.eq_of_localSubring_le_integers
    (isFunctionField_functionField_span_singleton (irreducible_blowupStrictTransform hF hX))
    hQα hQβ) 1

/-! ### Orders through the chart -/

omit [IsAlgClosed k] in
/-- **Orders through the blow-up chart.** At every place `Q` of `k(F)`, a polynomial `G` of
multiplicity `s = m_0(G)` at the origin, with strict transform `G'`, has order
`s · ord_Q(x) + ord_Q(G'(x, z))`: `G(x, xz) = x ^ s G'(x, z)`. -/
theorem addValuation_algebraMap_mk_eq_nsmul_add [(Ideal.span {blowupStrictTransform F}).IsPrime]
    (Q : Place k (functionField (Ideal.span {F}))) (G : MvPolynomial (Fin 2) k) :
    Q.addValuation (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) G)) =
      (G.orderAt 0).toNat •
          Q.addValuation (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0))) +
        (Q.map (blowupFunctionFieldEquiv hF hX)).addValuation
          (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {blowupStrictTransform F})
            (blowupStrictTransform G))) := by
  rw [← Q.addValuation_map_apply (blowupFunctionFieldEquiv hF hX),
    blowupFunctionFieldEquiv_algebraMap_mk, ← X_pow_mul_blowupStrictTransform, map_mul, map_mul,
    AddValuation.map_mul, map_pow, map_pow, AddValuation.map_pow,
    ← blowupFunctionFieldEquiv_x hF hX,
    Place.addValuation_map_apply]

end PlaneCurves.Affine

end
