/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Place.OrdinaryMultiplePoint

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

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.5
-/

public section

open MvPolynomial TauCeti IsLocalRing

namespace PlaneCurves.Affine

open AffineSpace

/-- If `A` is a local `k`-algebra with a `k`-algebra map to `k`, `k` algebraically closed, and `B`
is integral over `A`, then every maximal ideal of `B` is the kernel of a `k`-algebra map to `k`. -/
private theorem exists_algHom_ker_eq {k A B : Type*} [Field k] [IsAlgClosed k] [CommRing A]
    [IsLocalRing A] [Algebra k A] [CommRing B] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    [Algebra.IsIntegral A B] (e : A →ₐ[k] k) (m : Ideal B) [m.IsMaximal] :
    ∃ φ : B →ₐ[k] k, RingHom.ker φ = m := by
  let : Field (B ⧸ m) := Ideal.Quotient.field m
  have hker : RingHom.ker e = maximalIdeal A :=
    eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ fun c ↦ ⟨algebraMap k A c, by simp⟩)
  have hmA : m.comap (algebraMap A B) = maximalIdeal A :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
      (algebraMap_isIntegral_iff.2 inferInstance) m)
  have hc : (algebraMap k (B ⧸ m)).comp e.toRingHom = algebraMap A (B ⧸ m) := by
    ext c
    change Ideal.Quotient.mk m (algebraMap k B (e c)) = Ideal.Quotient.mk m (algebraMap A B c)
    rw [Ideal.Quotient.eq, IsScalarTower.algebraMap_apply k A B, ← map_sub, ← Ideal.mem_comap,
      hmA, ← hker, RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
  have hsurj : Function.Surjective (Algebra.ofId k (B ⧸ m)) := by
    intro b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨p, hp, hpb⟩ := Algebra.IsIntegral.isIntegral (R := A) b
    have hq := hp.map e.toRingHom
    have hqb : Polynomial.aeval (Ideal.Quotient.mk m b) (p.map e.toRingHom) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, hc, ← Polynomial.aeval_def,
        ← Ideal.Quotient.mkₐ_eq_mk A, Polynomial.aeval_algHom_apply, Polynomial.aeval_def, hpb,
        map_zero]
    rw [← Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hq
      IsAlgClosed.card_roots_eq_natDegree, map_multiset_prod, Multiset.prod_eq_zero_iff,
      Multiset.map_map] at hqb
    obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 hqb
    exact ⟨a, (sub_eq_zero.1 (by simpa using ha)).symm⟩
  let ψ := AlgEquiv.ofBijective (Algebra.ofId k (B ⧸ m))
    ⟨(algebraMap k (B ⧸ m)).injective, hsurj⟩
  refine ⟨ψ.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m), ?_⟩
  ext b
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

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
  obtain ⟨φ, hφ⟩ := exists_algHom_ker_eq (evalAt 0 hI) m
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

end
