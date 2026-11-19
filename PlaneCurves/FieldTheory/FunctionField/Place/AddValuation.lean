/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import TauCeti.FieldTheory.FunctionField.Place.Filtration
public import TauCeti.FieldTheory.FunctionField.Place.Map
public import TauCeti.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.RingTheory.Valuation.ToAdditive
public import PlaneCurves.RingTheory.Length

/-!
# The additive valuation of a place

For a place `Q` of a field extension `K/k`, Tau Ceti's order function `Q.ord : K → ℤ` has the
junk value `Q.ord 0 = 0`. This file defines the order of `Q` as an additive valuation
`Q.addValuation : AddValuation K (WithTop ℤ)`, which takes the value `⊤` (Fulton's `∞`) at `0`
and agrees with `Q.ord` elsewhere. It is the additive valuation `Valuation.addVal` attached to
the normalized valuation of `Q`.

## Main definitions

* `TauCeti.Place.addValuation`: the order `ord_Q : K → ℤ ∪ {∞}` of a place, as an additive
  valuation.

## Main results

* `TauCeti.Place.addValuation_of_ne_zero`: `ord_Q z = Q.ord z` for `z ≠ 0`.
* `TauCeti.Place.addValuation_eq_top_iff`: `ord_Q z = ∞ ↔ z = 0`.
* `TauCeti.Place.addValuation_nonneg_iff`: the valuation ring `𝒪_Q` is `{z | 0 ≤ ord_Q z}`.
* `TauCeti.Place.addValuation_pos_iff`: the maximal ideal of `𝒪_Q` is `{z | 0 < ord_Q z}`.
* `TauCeti.Place.addValuation_algebraMap`: nonzero constants have order `0`.
* `TauCeti.Place.map_natCast_addVal_eq_addValuation` and
  `TauCeti.Place.map_natCast_ord_eq_addValuation`: on `𝒪_Q`, the order is the additive valuation
  `IsDiscreteValuationRing.addVal` of the discrete valuation ring `𝒪_Q`, and the order of
  vanishing `Ring.ord` (the length of `𝒪_Q/(z)`), both read in `WithTop ℤ`.
* `TauCeti.Place.map_natCast_ord_ringEquiv_eq_addValuation`: the same in any ring isomorphic to
  `𝒪_Q`.
* `TauCeti.Place.addValuation_map`: the order of the transported place `Q.map e` is the order of
  `Q` composed with `e⁻¹`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.1
* [H. Stichtenoth, *Algebraic Function Fields and Codes*][Stichtenoth2009], §1.1
-/

public section

open scoped WithZero

open IsLocalRing

namespace TauCeti.Place

variable {k K : Type*} [Field k] [Field K] [Algebra k K] (Q : Place k K)

/-- The **order** `ord_Q : K → ℤ ∪ {∞}` of a place `Q`, as an additive valuation: it is `⊤` at
`0` and `Q.ord z` at `z ≠ 0`. It is the additive valuation attached to the normalized valuation
of `Q`. -/
noncomputable def addValuation : AddValuation K (WithTop ℤ) :=
  Q.valuation.addVal

/-- The defining equation of `Place.addValuation`. -/
theorem addValuation_def : Q.addValuation = Q.valuation.addVal :=
  (rfl)

/-- The order of `z` is `WithZero.negLog` of its valuation. -/
theorem addValuation_apply (z : K) : Q.addValuation z = WithZero.negLog (Q.valuation z) := by
  rw [addValuation_def, Valuation.addVal_apply]

/-- `z` has finite order `n` exactly when its valuation is `exp (-n)`. -/
theorem addValuation_eq_coe_iff {z : K} {n : ℤ} :
    Q.addValuation z = n ↔ Q.valuation z = WithZero.exp (-n) := by
  rw [addValuation_def, Valuation.addVal_eq_coe]

/-- Away from `0`, the order of a place is Tau Ceti's order function `Q.ord`. -/
@[simp]
theorem addValuation_of_ne_zero {z : K} (hz : z ≠ 0) : Q.addValuation z = Q.ord z := by
  rw [addValuation_eq_coe_iff, Q.valuation_eq_exp_neg_ord hz]

/-- Only `0` has order `∞`. -/
@[simp]
theorem addValuation_eq_top_iff {z : K} : Q.addValuation z = ⊤ ↔ z = 0 := by
  rw [addValuation_apply, WithZero.negLog_eq_top, map_eq_zero]

/-- Exactly the nonzero elements have finite order. -/
theorem addValuation_ne_top_iff {z : K} : Q.addValuation z ≠ ⊤ ↔ z ≠ 0 :=
  (Q.addValuation_eq_top_iff).not

/-- The valuation ring of a place consists of the elements of nonnegative order. -/
theorem addValuation_nonneg_iff {z : K} : 0 ≤ Q.addValuation z ↔ z ∈ Q.integers := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [Q.addValuation_of_ne_zero hz, WithTop.coe_nonneg, Q.mem_integers_iff_ord_nonneg]

/-- The elements of positive order are those of valuation less than one. -/
theorem addValuation_pos_iff_valuation_lt_one {z : K} :
    0 < Q.addValuation z ↔ Q.valuation z < 1 := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [Q.addValuation_of_ne_zero hz, WithTop.coe_pos, Q.valuation_lt_one_iff_ord_pos hz]

/-- The maximal ideal of the valuation ring of a place consists of the elements of positive
order. -/
theorem addValuation_pos_iff {z : Q.integers} :
    0 < Q.addValuation (z : K) ↔ z ∈ maximalIdeal Q.integers := by
  rw [addValuation_pos_iff_valuation_lt_one, mem_maximalIdeal_iff_valuation_lt_one]

/-- Nonzero constants have order `0`. -/
@[simp]
theorem addValuation_algebraMap {c : k} (hc : c ≠ 0) : Q.addValuation (algebraMap k K c) = 0 := by
  rw [Q.addValuation_of_ne_zero (by simpa using hc), ord_algebraMap, WithTop.coe_zero]

/-- On the valuation ring `𝒪_Q`, the order of `Q` is the additive valuation of the discrete
valuation ring `𝒪_Q`, read in `WithTop ℤ` through the cast `ℕ∞ → WithTop ℤ`. -/
theorem map_natCast_addVal_eq_addValuation (z : Q.integers) :
    (IsDiscreteValuationRing.addVal Q.integers z).map (Nat.cast : ℕ → ℤ) =
      Q.addValuation (z : K) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hz' : (z : K) ≠ 0 := by simpa using hz
  have hnn : 0 ≤ Q.ord (z : K) := Q.mem_integers_iff_ord_nonneg.mp z.2
  have h : IsDiscreteValuationRing.addVal Q.integers z = ((Q.ord (z : K)).toNat : ℕ∞) := by
    refine ENat.eq_of_forall_natCast_le_iff fun n ↦ ?_
    rw [← TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal,
      Q.mem_maximalIdeal_pow_iff_coe_mem_filtration, Q.mem_filtration_iff_le_ord hz',
      Nat.cast_le]
    omega
  rw [h, Q.addValuation_of_ne_zero hz', ENat.map_natCast, Int.toNat_of_nonneg hnn]

/-- On the valuation ring `𝒪_Q`, the order of `Q` is the order of vanishing
`Ring.ord 𝒪_Q z = ℓ(𝒪_Q/(z))`, read in `WithTop ℤ` through the cast `ℕ∞ → WithTop ℤ`. -/
theorem map_natCast_ord_eq_addValuation (z : Q.integers) :
    (Ring.ord Q.integers z).map (Nat.cast : ℕ → ℤ) = Q.addValuation (z : K) := by
  rw [Ring.ord_eq_addVal, map_natCast_addVal_eq_addValuation]

/-- The order of `Q` is the order of vanishing in any ring `R` isomorphic to `𝒪_Q`:
`ord_Q (e x) = Ring.ord R x`, read in `WithTop ℤ`, for `e : R ≃+* 𝒪_Q`. -/
theorem map_natCast_ord_ringEquiv_eq_addValuation {R : Type*} [CommRing R]
    (e : R ≃+* Q.integers) (x : R) :
    (Ring.ord R x).map (Nat.cast : ℕ → ℤ) = Q.addValuation (e x : K) := by
  rw [← Ring.ord_ringEquiv e, map_natCast_ord_eq_addValuation]

/-- The order of the transport `Q.map e` of a place along an isomorphism `e : K ≃ₐ[k] K'` is the
order of `Q` composed with `e⁻¹`. -/
@[simp]
theorem addValuation_map {K' : Type*} [Field K'] [Algebra k K'] (e : K ≃ₐ[k] K') (z : K') :
    (Q.map e).addValuation z = Q.addValuation (e.symm z) := by
  rw [addValuation_apply, addValuation_apply, valuation_map]

end TauCeti.Place

end
