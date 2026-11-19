/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.AffineSpace.PlaneCurveDimension
public import PlaneCurves.AlgebraicGeometry.AffineSpace.RationalFunction
public import PlaneCurves.FieldTheory.FunctionField.HolomorphyRing.Length
public import PlaneCurves.RingTheory.Conductor
public import TauCeti.FieldTheory.FunctionField.Place.Degree
public import TauCeti.FieldTheory.FunctionField.Place.Existence
public import TauCeti.RingTheory.UniversallyJapanese

/-!
# Places over a point of an affine variety

Let `V = V(I) ⊆ 𝔸^σ` be a variety over a field `k`, `P` a point of `V`, and `Q` a place of the
function field `k(V)` whose valuation ring contains the local ring `𝒪_P(V)`, that is, a place
over `P`. This file shows that polynomial functions take their values at `P` at such a place.

When `k(V)` is a function field of one variable over an algebraically closed field `k`, finitely
many places lie over `P`, and at least one. The local ring `𝒪_P(V)` is Japanese, being a
localization of the finitely generated `k`-domain `Γ(V)`, so its integral closure in `k(V)` is a
finite `𝒪_P(V)`-module; this integral closure is the holomorphy ring of the places over `P`. Hence
the length of `𝒪_P(V) ⧸ (g)`, for a nonzero `g ∈ 𝒪_P(V)`, is the sum of the orders of `g` at the
places over `P`.

## Main results

* `PlaneCurves.AffineSpace.valuation_algebraMap_mk_eq_one`: a polynomial `g` with `g(P) ≠ 0` has
  valuation one at `Q`.
* `PlaneCurves.AffineSpace.valuation_algebraMap_mk_sub_lt_one`: for `k` algebraically closed and
  `k(V)` a function field, every polynomial `g` agrees with `g(P)` to first order at `Q`:
  `v_Q(g - g(P)) < 1`.
* `PlaneCurves.AffineSpace.valuation_algebraMap_mk_eq_one_iff`: then `g` has valuation one at
  `Q` exactly when `g(P) ≠ 0`.
* `PlaneCurves.AffineSpace.finite_setOf_localSubring_le_integers`,
  `PlaneCurves.AffineSpace.nonempty_setOf_localSubring_le_integers`: finitely many places lie
  over `P`, and at least one.
* `PlaneCurves.AffineSpace.isJapanese_localSubring`: `𝒪_P(V)` is Japanese, and
  `finite_integralClosure_localSubring`: its integral closure in `k(V)` is a finite module.
* `PlaneCurves.AffineSpace.integralClosure_localSubring`: the integral closure of `𝒪_P(V)` in
  `k(V)` is the holomorphy ring of the places over `P`.
* `PlaneCurves.AffineSpace.exists_ne_zero_mul_mem_range_localSubring`: a nonzero conductor
  element of `𝒪_P(V)`.
* `PlaneCurves.AffineSpace.map_natCast_ord_localSubring_eq_sum_addValuation`:
  `ℓ(𝒪_P(V) ⧸ (g)) = ∑_Q ord_Q g`, the sum running over the places over `P`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.5, Proposition 2
-/

public section

open MvPolynomial TauCeti TauCeti.Ring

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

/-- If the valuation ring of a place `Q` of the function field `k(V)` contains `𝒪_P(V)`, a
polynomial `g` has valuation one at `Q` exactly when `g(P) ≠ 0`. -/
theorem valuation_algebraMap_mk_eq_one_iff (hK : IsFunctionField k (functionField I))
    (hQ : (localSubring P hI).toSubring ≤ Q.integers.toSubring) {g : MvPolynomial σ k} :
    Q.valuation (algebraMap _ _ (Ideal.Quotient.mk I g)) = 1 ↔ eval P g ≠ 0 := by
  refine ⟨fun h1 h0 ↦ ?_, valuation_algebraMap_mk_eq_one hQ⟩
  have h := valuation_algebraMap_mk_sub_lt_one hK hQ g
  rw [h0, map_zero, sub_zero, h1] at h
  exact lt_irrefl 1 h

/-! ### The places over a point of a curve -/

section Curve

variable (P hI)

omit [IsAlgClosed k] in
/-- `𝒪_P(V)` is Japanese: it is a localization of the coordinate ring `Γ(V)`, a domain of finite
type over the field `k`. -/
instance isJapanese_localSubring [Finite σ] : IsJapanese (localSubring P hI).toSubring :=
  have : IsJapanese (MvPolynomial σ k ⧸ I) := IsUniversallyJapanese.isJapanese k _
  isJapanese_of_isLocalization (R := MvPolynomial σ k ⧸ I)
    (RingHom.ker (coordinateEval P hI)).primeCompl _

omit [IsAlgClosed k] in
/-- The integral closure of `𝒪_P(V)` in `k(V)` is a finite `𝒪_P(V)`-module. -/
theorem finite_integralClosure_localSubring [Finite σ] :
    Module.Finite (localSubring P hI).toSubring
      (integralClosure (localSubring P hI).toSubring (functionField I)) :=
  IsJapanese.finite_integralClosure (functionField I) (functionField I)

omit [IsAlgClosed k] in
/-- **A conductor element of `𝒪_P(V)`**: some nonzero `t ∈ 𝒪_P(V)` carries the integral closure
of `𝒪_P(V)` in `k(V)` into `𝒪_P(V)`. -/
theorem exists_ne_zero_mul_mem_range_localSubring [Finite σ] :
    ∃ t : (localSubring P hI).toSubring, t ≠ 0 ∧
      ∀ z ∈ integralClosure (localSubring P hI).toSubring (functionField I),
        algebraMap (localSubring P hI).toSubring (functionField I) t * z ∈
          (algebraMap (localSubring P hI).toSubring (functionField I)).range := by
  have := finite_integralClosure_localSubring P hI
  obtain ⟨a, ha, hac⟩ := TauCeti.Algebra.exists_mem_conductor_of_isLocalization
    (A := (localSubring P hI).toSubring)
    (B := integralClosure (localSubring P hI).toSubring (functionField I))
    (L := functionField I) (nonZeroDivisors _) Subtype.val_injective
  refine ⟨a, nonZeroDivisors.ne_zero ha, fun z hz ↦ ?_⟩
  obtain ⟨c, hc⟩ := TauCeti.Algebra.mem_conductor_iff.1 hac ⟨z, hz⟩
  exact ⟨c, congrArg Subtype.val hc⟩

omit [IsAlgClosed k] in
/-- **The integral closure of `𝒪_P(V)`** in `k(V)` is the holomorphy ring of the places over
`P`, for `k(V)` a function field. -/
theorem integralClosure_localSubring (hK : IsFunctionField k (functionField I)) :
    (integralClosure (localSubring P hI).toSubring (functionField I)).toSubring =
      (holomorphyRing {Q : Place k (functionField I) |
        (localSubring P hI).toSubring ≤ Q.integers.toSubring}).toSubring := by
  let R : Subalgebra k (functionField I) :=
    { (localSubring P hI).toSubring with
      algebraMap_mem' := fun c ↦ (algebraMap k (localSubring P hI).toSubring c).2 }
  have h := restrictScalars_integralClosure_eq_holomorphyRing hK R
  ext z
  exact SetLike.ext_iff.1 h z

include hI in
/-- A polynomial vanishing at `P` but not on `V`, when `k(V)` is a function field. -/
private theorem exists_eval_eq_zero_notMem [Finite σ] (hK : IsFunctionField k (functionField I)) :
    ∃ g : MvPolynomial σ k, eval P g = 0 ∧ g ∉ I := by
  by_contra! h
  have hle : vanishingIdeal k {P} ≤ I := fun g hg ↦
    h g ((mem_vanishingIdeal_singleton_iff P g).1 hg)
  have := (trdeg_functionField_eq_zero_iff (I := I)).2 ⟨P, le_antisymm hI hle⟩
  rw [hK.trdeg_eq_one] at this
  exact one_ne_zero this

omit [I.IsPrime] [IsAlgClosed k] in
private theorem algebraMap_mk_ne_zero_of_notMem {g : MvPolynomial σ k} (hg : g ∉ I) :
    algebraMap _ (functionField I) (Ideal.Quotient.mk I g) ≠ 0 := fun h ↦
  hg (Ideal.Quotient.eq_zero_iff_mem.1 (IsFractionRing.injective _ (functionField I)
    (h.trans (map_zero _).symm)))

/-- **Finitely many places lie over a point** of a variety whose function field is a function
field of one variable. -/
theorem finite_setOf_localSubring_le_integers [Finite σ]
    (hK : IsFunctionField k (functionField I)) :
    {Q : Place k (functionField I) |
      (localSubring P hI).toSubring ≤ Q.integers.toSubring}.Finite := by
  obtain ⟨g, hgP, hgI⟩ := exists_eval_eq_zero_notMem P hI hK
  refine (Place.finite_setOf_ord_pos hK
    (algebraMap _ (functionField I) (Ideal.Quotient.mk I g))).subset fun Q hQ ↦ ?_
  have h := valuation_algebraMap_mk_sub_lt_one hK hQ g
  rw [hgP, map_zero, sub_zero] at h
  exact (Q.valuation_lt_one_iff_ord_pos (algebraMap_mk_ne_zero_of_notMem hgI)).1 h

/-- **Some place lies over every point** of a variety whose function field is a function field of
one variable. -/
theorem nonempty_setOf_localSubring_le_integers [Finite σ]
    (hK : IsFunctionField k (functionField I)) :
    {Q : Place k (functionField I) |
      (localSubring P hI).toSubring ≤ Q.integers.toSubring}.Nonempty := by
  obtain ⟨g, hgP, hgI⟩ := exists_eval_eq_zero_notMem P hI hK
  let z : (localSubring P hI).toSubring := algebraMap _ _ (Ideal.Quotient.mk I g)
  have hzm : z ∈ IsLocalRing.maximalIdeal _ := by
    rw [← ker_evalAt, RingHom.mem_ker, evalAt_algebraMap, coordinateEval_mk]
    exact hgP
  have hz0 : z ≠ 0 := fun h ↦ algebraMap_mk_ne_zero_of_notMem hgI (by
    rw [← coe_algebraMap_localSubring]
    exact congrArg Subtype.val h)
  obtain ⟨Q, hQ, -⟩ := Place.exists_forall_mem_integers_and_valuation_lt_one hK
    (R := (localSubring P hI).toSubring)
    (fun c ↦ (algebraMap k (localSubring P hI).toSubring c).2)
    (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Submodule.ne_bot_iff _).2 ⟨z, hzm, hz0⟩)
  exact ⟨Q, fun x hx ↦ hQ ⟨x, hx⟩⟩

/-- **`ℓ(𝒪_P(V) ⧸ (g)) = ∑_Q ord_Q g`.** For a variety `V` whose function field `k(V)` is a
function field of one variable over an algebraically closed field `k`, and a nonzero `g` in the
local ring `𝒪_P(V)` at a point `P`, the length of `𝒪_P(V) ⧸ (g)` is the sum of the orders of `g`
at the places of `k(V)` over `P`. The length is cast from `ℕ∞` to `WithTop ℤ`. -/
theorem map_natCast_ord_localSubring_eq_sum_addValuation [Finite σ]
    (hK : IsFunctionField k (functionField I)) {g : (localSubring P hI).toSubring} (hg : g ≠ 0) :
    (Ring.ord (localSubring P hI).toSubring g).map (Nat.cast : ℕ → ℤ) =
      ∑ Q ∈ (finite_setOf_localSubring_le_integers P hI hK).toFinset,
        Q.addValuation (g : functionField I) :=
  have := finite_integralClosure_localSubring P hI
  have ht := (exists_ne_zero_mul_mem_range_localSubring P hI).choose_spec
  map_natCast_ord_eq_sum_addValuation_of_integralClosure_eq_holomorphyRing Subtype.val_injective
    (by rw [Set.Finite.coe_toFinset]; exact integralClosure_localSubring P hI hK)
    (surjective_algebraMap_residueField_localSubring P hI) ht.1 ht.2 hg

end Curve

end PlaneCurves.AffineSpace

end
