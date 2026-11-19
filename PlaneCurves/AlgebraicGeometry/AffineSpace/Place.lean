/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.AffineSpace.RationalFunction
public import TauCeti.FieldTheory.FunctionField.Place.Degree

/-!
# Places over a point of an affine variety

Let `V = V(I) ⊆ 𝔸^σ` be a variety over a field `k`, `P` a point of `V`, and `Q` a place of the
function field `k(V)` whose valuation ring contains the local ring `𝒪_P(V)`, that is, a place
over `P`. This file shows that polynomial functions take their values at `P` at such a place.

## Main results

* `PlaneCurves.AffineSpace.valuation_algebraMap_mk_eq_one`: a polynomial `g` with `g(P) ≠ 0` has
  valuation one at `Q`.
* `PlaneCurves.AffineSpace.valuation_algebraMap_mk_sub_lt_one`: for `k` algebraically closed and
  `k(V)` a function field, every polynomial `g` agrees with `g(P)` to first order at `Q`:
  `v_Q(g - g(P)) < 1`.
* `PlaneCurves.AffineSpace.valuation_algebraMap_mk_eq_one_iff`: then `g` has valuation one at
  `Q` exactly when `g(P) ≠ 0`.
* `PlaneCurves.AffineSpace.eq_of_localSubring_le_integers`: then `Q` lies over at most one point.
-/

public section

open MvPolynomial TauCeti

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

/-- **A place lies over at most one point**: if the valuation ring of a place `Q` of the function
field `k(V)` contains both `𝒪_P(V)` and `𝒪_{P'}(V)`, then `P = P'`. -/
theorem eq_of_localSubring_le_integers (hK : IsFunctionField k (functionField I)) {P' : σ → k}
    {hI' : I ≤ vanishingIdeal k {P'}} (hQ : (localSubring P hI).toSubring ≤ Q.integers.toSubring)
    (hQ' : (localSubring P' hI').toSubring ≤ Q.integers.toSubring) : P = P' :=
  funext fun i ↦ by
    simpa using Q.eq_of_valuation_sub_lt_one (valuation_algebraMap_mk_sub_lt_one hK hQ (X i))
      (valuation_algebraMap_mk_sub_lt_one hK hQ' (X i))

end PlaneCurves.AffineSpace

end
