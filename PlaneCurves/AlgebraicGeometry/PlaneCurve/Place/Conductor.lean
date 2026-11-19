/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Place.OrdinaryMultiplePoint
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Noether.Basic
public import PlaneCurves.RingTheory.Ideal.GoingUp

/-!
# The conductor at an ordinary multiple point

Let `k` be an algebraically closed field and `F` an irreducible affine plane curve, other than the
line `X = 0`, with an ordinary multiple point of multiplicity `r` at the origin at which `X = 0` is
not tangent. Let `K = k(F)` be its function field, `x, y` the coordinate functions, and
`A = 𝒪_0(F)` the local ring of the origin.

The element `z = y / x` is integral over `A` (it is a root of a monic polynomial of degree `r`
obtained from `F(x, xz) = x ^ r F'(x, z)`), and `x ^ (r - 1)` carries `A[z]` into `A`
(`pow_mem_conductor_adjoin_of_isUnit_aeval_blowupChartLeadingCoeff`). This file shows that `A[z]`
is the integral closure of `A` in `K`: a function `w` in the valuation ring of every place over
the origin lies in `A[z]`. Otherwise the ideal `J = {b ∈ A[z] | b w ∈ A[z]}` lies in a maximal
ideal `m` of `A[z]`. As `A[z]` is integral over `A`, `m` lies over the maximal ideal of `A`, so
`x ∈ m`, and as `k` is algebraically closed, `z ≡ α (mod m)` for some `α ∈ k`. Then `F'(0, α) = 0`,
so `Y - α X` is tangent to `F`, and `w` lies in the valuation ring `𝒪_{(0, α)}(F')` of the place
over this tangent: `w = a(x, z) / b(x, z)` with `b(0, α) ≠ 0`. But then `b(x, z) ∈ J ⊆ m`, while
`b(x, z) ≡ b(0, α) ≢ 0 (mod m)`.

Together with the conductor, this gives Lemma 3 of §7.5 of Fulton at an affine ordinary multiple
point: a function with order at least `r - 1` at every place over the origin lies in `𝒪_0(F)`.

On an irreducible projective plane curve `C : F = 0` with an ordinary multiple point `P` of
multiplicity `r`, a change of coordinates moves `P` to `[0 : 0 : 1]` with `X = 0` not tangent,
and the chart `Z ≠ 0` gives Lemma 3: a function with `ord_Q ≥ r - 1` at every place `Q` over `P`
lies in `𝒪_P(C)`. Proposition 3 of §7.5 follows: if `F ∤ G` and `ord_Q(H) ≥ ord_Q(G) + r - 1` at
every `Q` over `P`, then `h / g ∈ 𝒪_P(C)` for the restrictions `g = G / Xᵢᵉ`, `h = H / Xᵢᵉ'`, so
`H_* ∈ (F_*, G_*)` through `𝒪_P(ℙ²) ⧸ (F_*) ≅ 𝒪_P(C)`.

## Main results

* `PlaneCurves.Affine.isIntegral_div`, `PlaneCurves.Affine.pow_mem_conductor_adjoin_div`:
  `z = y / x` is integral over `𝒪_0(F)`, and `x ^ (r - 1)` lies in the conductor of
  `𝒪_0(F)[z]`.
* `PlaneCurves.Affine.mem_adjoin_div_of_forall_mem_integers`: a function in the valuation ring of
  every place over the origin lies in `𝒪_0(F)[y / x]`.
* `PlaneCurves.Affine.integralClosure_localSubring_eq_adjoin`: the integral closure of `𝒪_0(F)`
  in `k(F)` is `𝒪_0(F)[y / x]`; `PlaneCurves.Affine.pow_mem_conductor_integralClosure`: so
  `x ^ (r - 1)` lies in its conductor.
* `PlaneCurves.Affine.mem_localSubring_of_forall_le_addValuation`: Lemma 3 of §7.5 at an affine
  ordinary multiple point.
* `PlaneCurves.Projective.mem_localSubring_of_forall_le_addValuation`: Lemma 3 of §7.5 on a
  projective plane curve.
* `PlaneCurves.Projective.noetherConditionsAt_of_forall_le_ordForm`: Proposition 3 of §7.5.
* `PlaneCurves.Projective.IsOrdinaryMultiplePoint.noetherConditionsAt_of_forall_le_ordForm`: the
  two together.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.5, Lemma 3 and Proposition 3
-/

public section

open MvPolynomial TauCeti IsLocalRing

namespace PlaneCurves.Affine

open AffineSpace

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 2) k} [(Ideal.span {F}).IsPrime]
  {hI : Ideal.span {F} ≤ vanishingIdeal k {(0 : Fin 2 → k)}}

omit [(Ideal.span {F}).IsPrime] in
private theorem aeval_mk_X {R : Type*} [CommSemiring R] [Algebra k R]
    (f : MvPolynomial (Fin 2) k ⧸ Ideal.span {F} →ₐ[k] R) (g : MvPolynomial (Fin 2) k) :
    aeval ![f (Ideal.Quotient.mk _ (X 0)), f (Ideal.Quotient.mk _ (X 1))] g =
      f (Ideal.Quotient.mk _ g) := by
  have h : (![f (Ideal.Quotient.mk _ (X 0)), f (Ideal.Quotient.mk _ (X 1))] : Fin 2 → R) =
      (f.comp (Ideal.Quotient.mkₐ k _)) ∘ X := by
    ext i : 1
    fin_cases i <;> rfl
  rw [h, ← aeval_unique]
  rfl

/-- If `X` is not tangent to `F` at the origin, `H(x, y)` is a unit of `𝒪_0(F)`: its value at the
origin is the coefficient `a_{0r}` of `Y ^ r`. -/
theorem isUnit_aeval_blowupChartLeadingCoeff_localSubring (hT : ¬IsTangentAt F 0 (X 0)) :
    IsUnit (aeval ![algebraMap _ (localSubring 0 hI).toSubring
        (Ideal.Quotient.mk (Ideal.span {F}) (X 0)),
      algebraMap _ (localSubring 0 hI).toSubring (Ideal.Quotient.mk (Ideal.span {F}) (X 1))]
      (blowupChartLeadingCoeff F)) := by
  have e := aeval_mk_X (IsScalarTower.toAlgHom k (MvPolynomial (Fin 2) k ⧸ Ideal.span {F})
      (localSubring 0 hI).toSubring)
    (blowupChartLeadingCoeff F)
  simp only [IsScalarTower.coe_toAlgHom'] at e
  rw [e, isUnit_iff_evalAt_ne_zero, evalAt_algebraMap, coordinateEval_mk,
    eval_zero_blowupChartLeadingCoeff]
  exact (isTangentAt_zero_X_zero_iff).not.1 hT

private theorem aeval_eq_zero :
    aeval ![algebraMap _ (localSubring 0 hI).toSubring (Ideal.Quotient.mk (Ideal.span {F}) (X 0)),
      algebraMap _ (localSubring 0 hI).toSubring (Ideal.Quotient.mk (Ideal.span {F}) (X 1))] F =
      0 := by
  have e := aeval_mk_X (IsScalarTower.toAlgHom k (MvPolynomial (Fin 2) k ⧸ Ideal.span {F})
    (localSubring 0 hI).toSubring) F
  simp only [IsScalarTower.coe_toAlgHom'] at e
  rw [e, Ideal.Quotient.mk_singleton_self, map_zero]

variable (hF : Irreducible F) (hX : ¬Associated F (X 0)) (h : IsOrdinaryMultiplePoint F 0)

omit [(Ideal.span {F}).IsPrime] in
include hF hX in
private theorem algebraMap_mk_X_zero_ne_zero :
    algebraMap _ (functionField (Ideal.span {F})) (Ideal.Quotient.mk (Ideal.span {F}) (X 0)) ≠
      0 := by
  rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]
  exact fun hd ↦ hX (hF.associated_of_dvd prime_X.irreducible hd)

include hF hX in
/-- At an ordinary multiple point at the origin at which `X = 0` is not tangent, `y / x` is
integral over `𝒪_0(F)`. -/
theorem isIntegral_div (hT : ¬IsTangentAt F 0 (X 0)) :
    IsIntegral (localSubring 0 hI).toSubring
      (algebraMap _ (functionField (Ideal.span {F})) (Ideal.Quotient.mk (Ideal.span {F}) (X 1)) /
        algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0))) :=
  isIntegral_of_isUnit_aeval_blowupChartLeadingCoeff aeval_eq_zero
    (mul_div_cancel₀ _ (algebraMap_mk_X_zero_ne_zero hF hX))
    (fun _ _ h ↦ mul_left_cancel₀ (algebraMap_mk_X_zero_ne_zero hF hX) h)
    (isUnit_aeval_blowupChartLeadingCoeff_localSubring hT)

include hF hX in
/-- **The conductor of `𝒪_0(F)[y / x]`.** At an ordinary multiple point of multiplicity `r` at
the origin, at which `X = 0` is not tangent, `x ^ (r - 1)` carries `𝒪_0(F)[y / x]` into
`𝒪_0(F)`. -/
theorem pow_mem_conductor_adjoin_div (hT : ¬IsTangentAt F 0 (X 0)) :
    algebraMap _ (localSubring 0 hI).toSubring (Ideal.Quotient.mk (Ideal.span {F}) (X 0)) ^
        ((F.orderAt 0).toNat - 1) ∈
      TauCeti.Algebra.conductor (localSubring 0 hI).toSubring
        (Algebra.adjoin (localSubring 0 hI).toSubring
          {algebraMap _ (functionField (Ideal.span {F}))
              (Ideal.Quotient.mk (Ideal.span {F}) (X 1)) /
            algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0))}) :=
  pow_mem_conductor_adjoin_of_isUnit_aeval_blowupChartLeadingCoeff aeval_eq_zero
    (mul_div_cancel₀ _ (algebraMap_mk_X_zero_ne_zero hF hX))
    (fun _ _ h ↦ mul_left_cancel₀ (algebraMap_mk_X_zero_ne_zero hF hX) h)
    (isUnit_aeval_blowupChartLeadingCoeff_localSubring hT)

variable [IsAlgClosed k]

include hF hX h in
/-- **Functions without poles over an ordinary multiple point.** Let the origin be an ordinary
multiple point of `F`, at which `X = 0` is not tangent. A function `w` that lies in the valuation
ring of every place over the origin lies in `𝒪_0(F)[y / x]`. -/
theorem mem_adjoin_div_of_forall_mem_integers (hT : ¬IsTangentAt F 0 (X 0))
    {w : functionField (Ideal.span {F})}
    (hw : ∀ Q : Place k (functionField (Ideal.span {F})),
      (localSubring 0 hI).toSubring ≤ Q.integers.toSubring → w ∈ Q.integers) :
    w ∈ Algebra.adjoin (localSubring 0 hI).toSubring
      {algebraMap _ (functionField (Ideal.span {F})) (Ideal.Quotient.mk (Ideal.span {F}) (X 1)) /
        algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0))} := by
  have := isPrime_span_blowupStrictTransform hF hX
  set A := (localSubring 0 hI).toSubring
  set x : functionField (Ideal.span {F}) :=
    algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0))
  set z : functionField (Ideal.span {F}) :=
    algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 1)) / x
  have hzB : z ∈ Algebra.adjoin A {z} := Algebra.subset_adjoin (Set.mem_singleton z)
  have hBi : Algebra.IsIntegral A (Algebra.adjoin A {z}) :=
    Algebra.IsIntegral.adjoin (by simpa using isIntegral_div (hI := hI) hF hX hT)
  generalize Algebra.adjoin A {z} = B at hzB hBi ⊢
  let J : Ideal B :=
    { carrier := {b | (b : functionField (Ideal.span {F})) * w ∈ B}
      add_mem' := fun {a b} ha hb ↦ by
        simpa [add_mul] using B.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun c b hb ↦ by
        simpa [mul_assoc] using B.mul_mem c.2 hb }
  by_cases hJ : J = ⊤
  · simpa [J] using (Ideal.eq_top_iff_one J).1 hJ
  exfalso
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
  obtain ⟨φ, hφ⟩ := hm.exists_algHom_ker_eq_of_isIntegral (evalAt 0 hI)
  have hφm (b : B) : φ b = 0 ↔ b ∈ m := by
    rw [← hφ, RingHom.mem_ker]
  let xB : B := algebraMap A B (algebraMap (MvPolynomial (Fin 2) k ⧸ Ideal.span {F}) A
    (Ideal.Quotient.mk (Ideal.span {F}) (X 0)))
  let zB : B := ⟨z, hzB⟩
  have hxB : φ xB = 0 := by
    have hk : RingHom.ker (φ.comp (IsScalarTower.toAlgHom k A B)) = maximalIdeal A :=
      eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ fun c ↦ ⟨algebraMap k A c, by simp⟩)
    have hxA : algebraMap (MvPolynomial (Fin 2) k ⧸ Ideal.span {F}) A
        (Ideal.Quotient.mk (Ideal.span {F}) (X 0)) ∈ maximalIdeal A := by
      rw [← ker_evalAt, RingHom.mem_ker, evalAt_algebraMap, coordinateEval_mk]
      simp
    rw [← hk, RingHom.mem_ker] at hxA
    exact hxA
  have hφg (g : MvPolynomial (Fin 2) k) : φ (aeval ![xB, zB] g) = eval ![0, φ zB] g := by
    rw [comp_aeval_apply, ← coe_aeval_eq_eval]
    refine congrArg (aeval · g) ?_
    ext i : 1
    fin_cases i
    exacts [hxB, rfl]
  have hcoe (g : MvPolynomial (Fin 2) k) :
      ((aeval ![xB, zB] g : B) : functionField (Ideal.span {F})) = aeval ![x, z] g := by
    refine (comp_aeval_apply (f := ![xB, zB]) ((B.val).restrictScalars k) g).trans
      (congrArg (aeval · g) ?_)
    ext i : 1
    fin_cases i <;> rfl
  have hcoe' (g : MvPolynomial (Fin 2) k) :
      ((aeval ![xB, zB] g : B) : functionField (Ideal.span {F})) =
        (blowupFunctionFieldEquiv hF hX).symm
          (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {blowupStrictTransform F}) g)) := by
    rw [hcoe, ← blowupFunctionFieldEquiv_symm_algebraMap_mk hF hX]
  have hα : IsTangentAt F 0 (X 1 - C (φ zB) * X 0) := by
    rw [← eval_zero_blowupStrictTransform_eq_zero_iff hF.ne_zero, ← hφg]
    have h0 : aeval ![xB, zB] (blowupStrictTransform F) = 0 := by
      refine Subtype.ext ?_
      rw [hcoe', Ideal.Quotient.mk_singleton_self, map_zero, map_zero]
      rfl
    rw [h0, map_zero]
  have hwQ := hw _ (localSubring_le_integers_blowupPlace hF hX h hα)
  rw [blowupPlace_def, Place.mem_integers_map_iff, AlgEquiv.symm_symm,
    ← ValuationSubring.mem_toSubring, integers_toSubring_placeAt, mem_localSubring_iff] at hwQ
  obtain ⟨a, b, hb, hab⟩ := hwQ
  have hbm : aeval ![xB, zB] b ∉ m := by
    rw [← hφm, hφg]
    exact hb
  refine hbm (hJm ?_)
  change ((aeval ![xB, zB] b : B) : functionField (Ideal.span {F})) * w ∈ B
  have hb0 := algebraMap_mk_ne_zero
    (span_le_vanishingIdeal (h.isSimplePoint_blowupStrictTransform hα).1.eval_eq_zero) hb
  have hba : ((aeval ![xB, zB] b : B) : functionField (Ideal.span {F})) * w =
      ((aeval ![xB, zB] a : B) : functionField (Ideal.span {F})) := by
    rw [hcoe' b, hcoe' a]
    apply (blowupFunctionFieldEquiv hF hX).injective
    rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, hab,
      mul_div_cancel₀ _ hb0]
  rw [hba]
  exact (aeval ![xB, zB] a).2

include hF hX h in
/-- **The integral closure of the local ring at an ordinary multiple point.** Let the origin be
an ordinary multiple point of `F`, at which `X = 0` is not tangent. The integral closure of
`𝒪_0(F)` in `k(F)` is `𝒪_0(F)[y / x]`. -/
theorem integralClosure_localSubring_eq_adjoin (hT : ¬IsTangentAt F 0 (X 0)) :
    integralClosure (localSubring 0 hI).toSubring (functionField (Ideal.span {F})) =
      Algebra.adjoin (localSubring 0 hI).toSubring
        {algebraMap _ (functionField (Ideal.span {F}))
            (Ideal.Quotient.mk (Ideal.span {F}) (X 1)) /
          algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0))} := by
  refine le_antisymm (fun w hw ↦ mem_adjoin_div_of_forall_mem_integers hF hX h hT fun Q hQ ↦
    Q.mem_integers_of_isIntegral (fun r ↦ hQ r.2) hw) ?_
  rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
  exact isIntegral_div hF hX hT

include hF hX h in
/-- **The conductor of the integral closure.** At an ordinary multiple point of multiplicity `r`
at the origin, at which `X = 0` is not tangent, `x ^ (r - 1)` lies in the conductor of the
integral closure of `𝒪_0(F)` in `k(F)`. -/
theorem pow_mem_conductor_integralClosure (hT : ¬IsTangentAt F 0 (X 0)) :
    algebraMap _ (localSubring 0 hI).toSubring (Ideal.Quotient.mk (Ideal.span {F}) (X 0)) ^
        ((F.orderAt 0).toNat - 1) ∈
      TauCeti.Algebra.conductor (localSubring 0 hI).toSubring
        (integralClosure (localSubring 0 hI).toSubring (functionField (Ideal.span {F}))) := by
  rw [TauCeti.Algebra.mem_conductor_iff]
  rintro ⟨b, hb⟩
  rw [integralClosure_localSubring_eq_adjoin hF hX h hT] at hb
  have hcond := pow_mem_conductor_adjoin_div (hI := hI) hF hX hT
  rw [TauCeti.Algebra.mem_conductor_iff] at hcond
  obtain ⟨c, hc⟩ := hcond ⟨b, hb⟩
  exact ⟨c, Subtype.ext (by simpa using congrArg Subtype.val hc)⟩

include hF hX h in
/-- **Lemma 3 of §7.5 of Fulton, at an affine ordinary multiple point.** Let the origin be an
ordinary multiple point of multiplicity `r` of the irreducible curve `F`, at which `X = 0` is not
tangent. A function `w ∈ k(F)` with order at least `r - 1` at every place over the origin lies
in `𝒪_0(F)`. -/
theorem mem_localSubring_of_forall_le_addValuation (hT : ¬IsTangentAt F 0 (X 0))
    {w : functionField (Ideal.span {F})}
    (hw : ∀ Q : Place k (functionField (Ideal.span {F})),
      (localSubring 0 hI).toSubring ≤ Q.integers.toSubring →
        (((F.orderAt 0).toNat - 1 : ℕ) : WithTop ℤ) ≤ Q.addValuation w) :
    w ∈ (localSubring 0 hI).toSubring := by
  have hx0 := pow_ne_zero ((F.orderAt 0).toNat - 1) (algebraMap_mk_X_zero_ne_zero hF hX)
  have hmem := mem_adjoin_div_of_forall_mem_integers (w := w / algebraMap _ _
      (Ideal.Quotient.mk (Ideal.span {F}) (X 0)) ^ ((F.orderAt 0).toNat - 1)) hF hX h hT
    fun Q hQ ↦ by
    obtain ⟨α, ⟨hα, rfl⟩, -⟩ := existsUnique_eq_blowupPlace hF hX h hT hQ
    have hv := hw _ hQ
    rw [← div_mul_cancel₀ w hx0, AddValuation.map_mul, AddValuation.map_pow,
      addValuation_x_blowupPlace, nsmul_one] at hv
    refine (Place.addValuation_nonneg_iff _).1 ?_
    generalize (blowupPlace hF hX h hα).addValuation _ = t at hv
    induction t using WithTop.recTopCoe
    · exact le_top
    · rw [← WithTop.coe_natCast, ← WithTop.coe_add, WithTop.coe_le_coe] at hv
      exact WithTop.coe_nonneg.2 (by omega)
  obtain ⟨c, hc⟩ := (TauCeti.Algebra.mem_conductor_iff.1
    (pow_mem_conductor_adjoin_div (hI := hI) hF hX hT)) ⟨_, hmem⟩
  have hc' : (c : functionField (Ideal.span {F})) = algebraMap _ _
      (Ideal.Quotient.mk (Ideal.span {F}) (X 0)) ^ ((F.orderAt 0).toNat - 1) *
        (w / algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0)) ^
          ((F.orderAt 0).toNat - 1)) := by
    exact congrArg Subtype.val hc
  rw [mul_div_cancel₀ _ hx0] at hc'
  exact hc' ▸ c.2

end PlaneCurves.Affine

/-! ### Lemma 3 and Proposition 3 of §7.5 on a projective plane curve -/

namespace PlaneCurves.Projective

open Projectivization PlaneCurves.ProjectiveSpace TauCeti.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type*} [Field k] [IsAlgClosed k] {F : MvPolynomial (Fin 3) k} {d : ℕ}
  {hF : F.IsHomogeneous d} [Fact (Irreducible F)]
  {P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k))}

/-- **Lemma 3 in the chart.** At the point `(0, 0)` of the chart `X₂ ≠ 0`, with `X₀` not tangent,
the statement follows from its affine counterpart through `k(C) ≅ k(F_(2))`. -/
private theorem mem_localSubring_of_chart (h : IsOrdinaryMultiplePoint F P.1)
    (hP : P.1 ∈ affineOpen 2) (h0 : affineChart 2 P.1 = 0) (hT : ¬IsTangentAt F P.1 (X 0))
    {z : functionField hF}
    (hz : ∀ Q ∈ placesOver hF P, (((mult F P.1).toNat - 1 : ℕ) : WithTop ℤ) ≤ Q.addValuation z) :
    z ∈ (localSubring hF P).toSubring := by
  have := isPrime_span_dehomogenize hF (not_dvd_X_of_mem_affineOpen hF P hP)
  have h' : Affine.IsOrdinaryMultiplePoint (dehomogenize 2 F) 0 :=
    h0 ▸ (isOrdinaryMultiplePoint_iff_affine hF hP).1 h
  have hf : Irreducible (dehomogenize 2 F) :=
    ((Ideal.span_singleton_prime h'.ne_zero).1 inferInstance).irreducible
  have hX : ¬Associated (dehomogenize 2 F) (X 0) := by
    simpa using (Affine.isOrdinaryMultiplePoint_def.1 h').1.not_associated_X_sub_C 0
  have hT' : ¬Affine.IsTangentAt (dehomogenize 2 F) 0 (X 0) := by
    rw [← isTangentAt_rename_succAbove_iff hP h0 hF (isHomogeneous_X k 0), rename_X]
    exact hT
  set e := functionField.chartEquiv hF 2 (not_dvd_X_of_mem_affineOpen hF P hP)
  have hI : Ideal.span {dehomogenize 2 F} ≤ MvPolynomial.vanishingIdeal k {(0 : Fin 2 → k)} :=
    Affine.span_le_vanishingIdeal (Affine.isOrdinaryMultiplePoint_def.1 h').1.eval_eq_zero
  have hloc :=
    AffineSpace.localSubring_congr _ (span_dehomogenize_le_vanishingIdeal hF P hP) h0 hI
  have hmem : e z ∈ (AffineSpace.localSubring 0 hI).toSubring := by
    refine Affine.mem_localSubring_of_forall_le_addValuation hf hX h' hT' fun R hR ↦ ?_
    have hQ : R.map e.symm ∈ placesOver hF P := by
      rw [mem_placesOver_iff_localSubring_le_map_chartEquiv_of_eq hP h0, Place.map_map_symm]
      exact hR
    have := hz _ hQ
    rwa [Place.addValuation_map, AlgEquiv.symm_symm, mult_eq_orderAt_dehomogenize hF hP,
      h0] at this
  rw [← hloc] at hmem
  obtain ⟨y, hy⟩ := (localSubring.chartEquiv hF 2 P hP).surjective ⟨e z, hmem⟩
  have hyz : (y : functionField hF) = z :=
    e.injective (by rw [← localSubring.coe_chartEquiv (hP := hP), hy])
  exact hyz ▸ y.2

/-- Lemma 3 moves along a change of coordinates. -/
private theorem mem_localSubring_of_linearSubst (M : GL (Fin 3) k)
    {P' : zeroLocus (projectivePlaneCurve.ideal (hF.linearSubst M.1) :
      Set (MvPolynomial (Fin 3) k))}
    (hQP : map M.1.mulVecLin (Matrix.mulVec_injective_of_isUnit M.isUnit) P'.1 = P.1)
    (h : ∀ z : functionField (hF.linearSubst M.1),
      (∀ R ∈ placesOver (hF.linearSubst M.1) P',
        (((mult (linearSubst M.1 F) P'.1).toNat - 1 : ℕ) : WithTop ℤ) ≤ R.addValuation z) →
      z ∈ (localSubring (hF.linearSubst M.1) P').toSubring)
    {z : functionField hF}
    (hz : ∀ Q ∈ placesOver hF P, (((mult F P.1).toNat - 1 : ℕ) : WithTop ℤ) ≤ Q.addValuation z) :
    z ∈ (localSubring hF P).toSubring := by
  set φ := functionField.linearSubstEquiv hF M
  have hφ := h (φ z) fun R hR ↦ by
    rw [placesOver_linearSubst hQP] at hR
    obtain ⟨Q, hQ, rfl⟩ := hR
    rw [Place.addValuation_map_apply,
      mult_linearSubst hF (Matrix.mulVec_injective_of_isUnit M.isUnit), hQP]
    exact hz Q hQ
  rw [← map_localSubring_linearSubstEquiv hQP, LocalSubring.map_toSubring, Subring.mem_map] at hφ
  obtain ⟨y, hy, hyz⟩ := hφ
  exact φ.injective hyz ▸ hy

/-- **Lemma 3 of §7.5 of Fulton.** Let `P` be an ordinary multiple point of multiplicity `r` of
the irreducible projective plane curve `C : F = 0`. A rational function `z ∈ k(C)` with
`ord_Q(z) ≥ r - 1` at every place `Q` over `P` lies in `𝒪_P(C)`. -/
theorem mem_localSubring_of_forall_le_addValuation (h : IsOrdinaryMultiplePoint F P.1)
    {z : functionField hF}
    (hz : ∀ Q ∈ placesOver hF P, (((mult F P.1).toNat - 1 : ℕ) : WithTop ℤ) ≤ Q.addValuation z) :
    z ∈ (localSubring hF P).toSubring := by
  obtain ⟨M, P', hMP, hP, h0, h', hT⟩ :=
    exists_linearSubst_isOrdinaryMultiplePoint_affineChart_eq_zero hF P h
  exact mem_localSubring_of_linearSubst M hMP (fun _ ↦ mem_localSubring_of_chart h' hP h0 hT) hz

/-- **Proposition 3 of §7.5 of Fulton.** Let `P` be an ordinary multiple point of multiplicity
`r` of the irreducible projective plane curve `C : F = 0`, and `G`, `H` forms with `F ∤ G`. If
`ord_Q(H) ≥ ord_Q(G) + r - 1` at every place `Q` over `P`, then Noether's conditions hold at `P`
for `F`, `G` and `H`: `H_* ∈ (F_*, G_*)` in `𝒪_P(ℙ²)`. -/
theorem noetherConditionsAt_of_forall_le_ordForm (h : IsOrdinaryMultiplePoint F P.1)
    {e e' : ℕ} {G H : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous e) (hH : H.IsHomogeneous e')
    (hFG : ¬F ∣ G)
    (hGH : ∀ Q ∈ placesOver hF P,
      ordForm hF Q hG + ((mult F P.1).toNat - 1 : ℕ) ≤ ordForm hF Q hH) :
    NoetherConditionsAt P.1 F G H := by
  obtain ⟨i, hi⟩ := exists_mem_affineOpen P.1
  have hXP (m : ℕ) : eval P.1.rep (X i ^ m : MvPolynomial (Fin 3) k) ≠ 0 := by
    simpa using pow_ne_zero m ((mem_affineOpen_iff _ _).1 hi)
  let c {m : ℕ} {G' : MvPolynomial (Fin 3) k} (hG' : G'.IsHomogeneous m) :
      HomogeneousLocalization.NumDenSameDeg (homogeneousSubmodule (Fin 3) k)
        (pointIdeal P.1).toIdeal.primeCompl :=
    ⟨m, ⟨G', (mem_homogeneousSubmodule _ _).2 hG'⟩,
      ⟨X i ^ m, (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X_pow _ _)⟩,
      pow_mem (X_mem_primeCompl_pointIdeal hi) m⟩
  have hord {m : ℕ} {G' : MvPolynomial (Fin 3) k} (hG' : G'.IsHomogeneous m)
      {Q : Place k (functionField hF)} (hQ : Q ∈ placesOver hF P) :
      ordForm hF Q hG' = Q.addValuation
        (toLocalSubring hF P (HomogeneousLocalization.mk (c hG')) : functionField hF) := by
    rw [ordForm_eq_addValuation_mk hG' (isHomogeneous_X_pow _ _)
      (mem_placesOver_iff.1 hQ ▸ hXP m), coe_toLocalSubring_mk]
  set g := toLocalSubring hF P (HomogeneousLocalization.mk (c hG))
  set g' := toLocalSubring hF P (HomogeneousLocalization.mk (c hH))
  have hg : (g : functionField hF) ≠ 0 := by
    obtain ⟨Q, hQ⟩ := placesOver_nonempty hF P
    intro h0
    have := hord hG hQ
    rw [h0, AddValuation.map_zero, ordForm_eq_top_iff] at this
    exact hFG this
  have hz : (g' : functionField hF) / g ∈ (localSubring hF P).toSubring := by
    refine mem_localSubring_of_forall_le_addValuation h fun Q hQ ↦ ?_
    have hle := hGH Q hQ
    have hgt : Q.addValuation (g : functionField hF) ≠ ⊤ := by
      rwa [Ne, Q.addValuation_eq_top_iff]
    rw [hord hG hQ, hord hH hQ] at hle
    change Q.addValuation (g : functionField hF) + _ ≤ Q.addValuation (g' : functionField hF) at hle
    rw [← div_mul_cancel₀ (g' : functionField hF) hg, AddValuation.map_mul,
      add_comm (Q.addValuation (_ / _))] at hle
    exact (WithTop.add_le_add_iff_left hgt).1 hle
  obtain ⟨w, hw⟩ := toLocalSubring_surjective hF P ⟨_, hz⟩
  have hker : HomogeneousLocalization.mk (c hH) - w * HomogeneousLocalization.mk (c hG) ∈
      Ideal.span {localEquation P.1 F} := by
    rw [← ker_toLocalSubring hF P, RingHom.mem_ker, map_sub, map_mul, hw, sub_eq_zero]
    exact Subtype.ext (div_mul_cancel₀ _ hg).symm
  obtain ⟨u, hu⟩ := associated_localEquation_mk (P := P.1) (c hH)
  obtain ⟨u', hu'⟩ := (associated_localEquation_mk (P := P.1) (c hG)).symm
  replace hu : localEquation P.1 H * u = HomogeneousLocalization.mk (c hH) := hu
  replace hu' : HomogeneousLocalization.mk (c hG) * u' = localEquation P.1 G := hu'
  rw [noetherConditionsAt_iff hF hG]
  set I := Ideal.span {localEquation P.1 F, localEquation P.1 G}
  have hGI : HomogeneousLocalization.mk (c hG) ∈ I := by
    rw [← mul_one (HomogeneousLocalization.mk (c hG)), ← Units.mul_inv u', ← mul_assoc, hu']
    exact I.mul_mem_right _ (Ideal.subset_span (by simp))
  have hHI : HomogeneousLocalization.mk (c hH) ∈ I := by
    rw [← sub_add_cancel (HomogeneousLocalization.mk (c hH)) (w * _)]
    refine I.add_mem ?_ (I.mul_mem_left _ hGI)
    exact Ideal.span_mono (by simp) hker
  have : localEquation P.1 H = HomogeneousLocalization.mk (c hH) * ↑u⁻¹ := by
    rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  rw [this]
  exact I.mul_mem_right _ hHI

/-- **Noether's conditions at an ordinary multiple point via orders at places.** Let `k` be
algebraically closed, `C : F = 0` an irreducible projective plane curve and `P` an ordinary
multiple point of `C` of multiplicity `r`.

* (Lemma 3 of §7.5) A rational function `z ∈ k(C)` with `ord_Q(z) ≥ r - 1` at every place `Q`
  over `P` lies in `𝒪_P(C)`.
* (Proposition 3 of §7.5) If `G`, `H` are forms, `F ∤ G`, and `ord_Q(H) ≥ ord_Q(G) + r - 1` at
  every place `Q` over `P`, then Noether's conditions hold at `P` for `F`, `G`, `H`:
  `H_* ∈ (F_*, G_*)` in `𝒪_P(ℙ²)`.

Milestone: *Noether's conditions at an ordinary multiple point via orders at places*. -/
theorem IsOrdinaryMultiplePoint.noetherConditionsAt_of_forall_le_ordForm
    (h : IsOrdinaryMultiplePoint F P.1) :
    (∀ z : functionField hF,
      (∀ Q ∈ placesOver hF P, (((mult F P.1).toNat - 1 : ℕ) : WithTop ℤ) ≤ Q.addValuation z) →
        z ∈ (localSubring hF P).toSubring) ∧
    ∀ {e e' : ℕ} {G H : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous e)
      (hH : H.IsHomogeneous e'), ¬F ∣ G →
      (∀ Q ∈ placesOver hF P,
        ordForm hF Q hG + ((mult F P.1).toNat - 1 : ℕ) ≤ ordForm hF Q hH) →
      NoetherConditionsAt P.1 F G H :=
  ⟨fun _ hz ↦ Projective.mem_localSubring_of_forall_le_addValuation h hz,
    fun hG hH hFG hGH ↦ Projective.noetherConditionsAt_of_forall_le_ordForm h hG hH hFG hGH⟩

end PlaneCurves.Projective

end
