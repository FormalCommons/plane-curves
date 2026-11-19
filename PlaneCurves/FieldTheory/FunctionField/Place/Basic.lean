/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import TauCeti.FieldTheory.FunctionField.Place.Basic

/-!
# The valuation ring of a place

For a place `Q` of a field extension `K/k`, Tau Ceti gives two valuations on `K`: the normalized
valuation `Q.valuation` of the place, and the valuation `Q.integers.valuation` of its valuation
ring `𝒪_Q`, with values in the value group of `𝒪_Q`. This file shows that they are equivalent,
so that statements about either can be read off the other, and that `𝒪_Q` is not all of `K`.
It also shows that agreement with constants to first order is compatible with polynomial
expressions: if each `uᵢ ∈ 𝒪_Q` agrees with a constant `pᵢ`, then `g(u)` agrees with `g(p)`.

## Main results

* `TauCeti.Place.isEquiv_valuation_integers`: `Q.valuation` and `Q.integers.valuation` are
  equivalent valuations.
* `TauCeti.Place.valuation_integers_lt_one_iff`: they agree on which elements have valuation
  `< 1`, the maximal ideal of `𝒪_Q`.
* `TauCeti.Place.exists_notMem_integers`: some element of `K` is not in `𝒪_Q`.
* `TauCeti.Place.valuation_sub_algebraMap_lt_one_iff`: `v_Q(a - c) < 1` iff `a` and the
  constant `c` have the same residue.
* `TauCeti.Place.valuation_aeval_sub_lt_one`: if `v_Q(uᵢ - pᵢ) < 1` for all `i`, then
  `v_Q(g(u) - g(p)) < 1` for every polynomial `g`.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][Stichtenoth2009], §1.1
-/

public section

namespace TauCeti.Place

variable {k K : Type*} [Field k] [Field K] [Algebra k K] (Q : Place k K)

/-- The valuation of a place is equivalent to the valuation of its valuation ring. -/
theorem isEquiv_valuation_integers : Q.valuation.IsEquiv Q.integers.valuation := by
  rw [integers_def]
  exact Valuation.isEquiv_valuation_valuationSubring _

/-- An element has valuation `< 1` for the valuation ring of a place iff it has valuation `< 1`
for the place. -/
theorem valuation_integers_lt_one_iff {z : K} :
    Q.integers.valuation z < 1 ↔ Q.valuation z < 1 :=
  Q.isEquiv_valuation_integers.lt_one_iff_lt_one.symm

/-- The valuation ring of a place is not the whole field. -/
theorem exists_notMem_integers : ∃ z, z ∉ Q.integers := by
  by_contra! h
  exact Q.integers_ne_top (eq_top_iff.2 fun z _ ↦ h z)

/-- An element `a` of `𝒪_Q` agrees with the constant `c` to first order, `v_Q(a - c) < 1`,
exactly when the residue of `a` is the residue of `c`. -/
theorem valuation_sub_algebraMap_lt_one_iff (a : Q.integers) (c : k) :
    Q.valuation ((a : K) - algebraMap k K c) < 1 ↔
      IsLocalRing.residue Q.integers a = algebraMap k Q.ResidueField c := by
  rw [← coe_algebraMap_constants, ← AddSubgroupClass.coe_sub,
    ← Q.residue_eq_zero_iff_valuation_lt_one, map_sub, sub_eq_zero,
    IsScalarTower.algebraMap_apply k Q.integers Q.ResidueField,
    IsLocalRing.ResidueField.algebraMap_eq]

/-- **Values of polynomial expressions at a place.** If each `uᵢ ∈ 𝒪_Q` agrees with the constant
`pᵢ` to first order, `v_Q(uᵢ - pᵢ) < 1`, then so does `g(u)` with `g(p)`, for every polynomial
`g`. -/
theorem valuation_aeval_sub_lt_one {σ : Type*} {u : σ → Q.integers} {p : σ → k}
    (hu : ∀ i, Q.valuation ((u i : K) - algebraMap k K (p i)) < 1) (g : MvPolynomial σ k) :
    Q.valuation ((MvPolynomial.aeval u g : K) - algebraMap k K (MvPolynomial.eval p g)) < 1 := by
  have h : (IsScalarTower.toAlgHom k Q.integers Q.ResidueField).comp (MvPolynomial.aeval u) =
      (Algebra.ofId k Q.ResidueField).comp (MvPolynomial.aeval p) :=
    MvPolynomial.algHom_ext fun i ↦ by
      simpa using (Q.valuation_sub_algebraMap_lt_one_iff (u i) (p i)).1 (hu i)
  rw [valuation_sub_algebraMap_lt_one_iff]
  simpa using DFunLike.congr_fun h g

end TauCeti.Place

end
