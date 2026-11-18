/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Multiplicity
public import PlaneCurves.RingTheory.MvPolynomial.HilbertFunction
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Linear systems of plane curves with assigned multiple points

For `d : ℕ` and `r : ℙ² →₀ ℕ`, assigning the multiplicity `r P` to finitely many points `P`, the
linear system `V(d; r)` is the space of forms `F` of degree `d` in `X, Y, Z` with
`m_P(F) ≥ r P` for every `P` (together with `0`). It is a subspace of the space of forms of
degree `d`, which has dimension `(d + 1)(d + 2)/2`.

In an affine chart `Xᵢ ≠ 0` containing `P`, with chart coordinates `a`, the condition
`m_P(F) ≥ n` says that the `n(n + 1)/2` Taylor coefficients at `a` of total degree `< n` of the
dehomogenization `F_(i)` vanish. These are linear conditions, and for `n ≤ d + 1` they are
independent. So one point of multiplicity `r ≤ d + 1` imposes exactly `r(r + 1)/2` conditions,
and the points of `r` together impose at most `∑ r_P(r_P + 1)/2`.

The dimensions here are dimensions of vector spaces; the projective dimension of the linear
system is one less.

## Main definitions

* `PlaneCurves.Projective.linearSystem d r`: the linear system `V(d; r)`.

## Main results

* `PlaneCurves.Projective.mem_linearSystem`: membership in `V(d; r)`.
* `PlaneCurves.Projective.le_mult_iff_coeff_taylor_dehomogenize`: `m_P(F) ≥ n` in a chart.
* `PlaneCurves.Projective.finrank_linearSystem_single_add`: one point of multiplicity
  `r ≤ d + 1` imposes `r(r + 1)/2` independent conditions on forms of degree `d`.
* `PlaneCurves.Projective.finrank_linearSystem_ge`: the dimension of `V(d; r)` is at least
  `(d + 1)(d + 2)/2 - ∑ r_P(r_P + 1)/2`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.2
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Module Projectivization TauCeti
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] {F G : MvPolynomial (Fin 3) k} {P : ℙ k (Fin 3 → k)} {d : ℕ}

/-! ### The linear system -/

/-! ### The linear system -/

/-- The *linear system* `V(d; r)` of plane curves of degree `d` with assigned multiplicities
`r : ℙ² →₀ ℕ`: the forms `F` of degree `d` with `m_P(F) ≥ r P` for every point `P`, together
with `0` (whose multiplicity is `⊤`). -/
noncomputable def linearSystem (d : ℕ) (r : ℙ k (Fin 3 → k) →₀ ℕ) :
    Submodule k (MvPolynomial (Fin 3) k) where
  carrier := {F | F.IsHomogeneous d ∧ ∀ P, (r P : ℕ∞) ≤ mult F P}
  add_mem' {F G} hF hG := ⟨hF.1.add hG.1, fun P ↦ by
    have h := min_orderAt_le_orderAt_add F G P.rep
    rw [← mult_def, ← mult_def, ← mult_def] at h
    exact (le_min (hF.2 P) (hG.2 P)).trans h⟩
  zero_mem' := ⟨isHomogeneous_zero _ _ _, fun P ↦ by simp⟩
  smul_mem' c F hF := by
    refine ⟨(mem_homogeneousSubmodule _ _).1
      (Submodule.smul_mem _ c ((mem_homogeneousSubmodule _ _).2 hF.1)), fun P ↦ ?_⟩
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · rw [mult_smul hc]
      exact hF.2 P

theorem mem_linearSystem {r : ℙ k (Fin 3 → k) →₀ ℕ} :
    F ∈ linearSystem d r ↔ F.IsHomogeneous d ∧ ∀ P, (r P : ℕ∞) ≤ mult F P :=
  Iff.rfl

theorem linearSystem_le_homogeneousSubmodule (d : ℕ) (r : ℙ k (Fin 3 → k) →₀ ℕ) :
    linearSystem d r ≤ homogeneousSubmodule (Fin 3) k d :=
  fun _ hF ↦ (mem_homogeneousSubmodule _ _).2 hF.1

/-- With no assigned points, the linear system is the space of all forms of degree `d`. -/
@[simp]
theorem linearSystem_zero (d : ℕ) :
    linearSystem d (0 : ℙ k (Fin 3 → k) →₀ ℕ) = homogeneousSubmodule (Fin 3) k d := by
  ext F
  simp [mem_linearSystem, mem_homogeneousSubmodule]

/-- Raising the assigned multiplicities shrinks the linear system. -/
theorem linearSystem_anti {r s : ℙ k (Fin 3 → k) →₀ ℕ} (h : r ≤ s) :
    linearSystem d s ≤ linearSystem d r :=
  fun _ hF ↦ ⟨hF.1, fun P ↦ (Nat.cast_le.2 (h P)).trans (hF.2 P)⟩

/-- A form lies in the linear system of a single point `P` of multiplicity `n` exactly when it
has degree `d` and `m_P(F) ≥ n`. -/
theorem mem_linearSystem_single {n : ℕ} :
    F ∈ linearSystem d (Finsupp.single P n) ↔ F.IsHomogeneous d ∧ (n : ℕ∞) ≤ mult F P := by
  refine ⟨fun h ↦ ⟨h.1, by simpa using h.2 P⟩, fun h ↦ ⟨h.1, fun Q ↦ ?_⟩⟩
  rcases eq_or_ne P Q with rfl | hPQ
  · simpa using h.2
  · rw [Finsupp.single_eq_of_ne' hPQ]
    simp

/- The cubic `X² Z` has multiplicity at least `2` at `[0 : 1 : 0]`, so it lies in the linear
system `V(3; 2 [0 : 1 : 0])`. -/
example : (X 0 : MvPolynomial (Fin 3) k) ^ 2 * X 2 ∈
    linearSystem 3 (Finsupp.single (mk k ![0, 1, 0] (by simp)) 2) := by
  have hX : ((X 0 : MvPolynomial (Fin 3) k)).IsHomogeneous 1 := isHomogeneous_X k 0
  refine mem_linearSystem_single.2 ⟨(hX.pow 2).mul (isHomogeneous_X k 2), ?_⟩
  rw [mult_mul, mult_pow]
  have h1 : (1 : ℕ∞) ≤ mult (X 0 : MvPolynomial (Fin 3) k) (mk k ![0, 1, 0] (by simp)) := by
    rw [Order.one_le_iff_pos, mult_mk hX, orderAt_pos_iff]
    simp
  calc (2 : ℕ∞) = 2 • 1 := by norm_num
    _ ≤ 2 • mult (X 0) _ := nsmul_le_nsmul_right h1 2
    _ ≤ _ := le_self_add

/-! ### The conditions in an affine chart -/

/-- **Multiplicity conditions in a chart.** For a form `F` and a point `P` of the affine chart
`Xᵢ ≠ 0`, `m_P(F) ≥ n` exactly when every Taylor coefficient of total degree `< n` of the
dehomogenization `F_(i)` at the chart coordinates of `P` vanishes. -/
theorem le_mult_iff_coeff_taylor_dehomogenize (hF : F.IsHomogeneous d) {i : Fin 3}
    (hP : P ∈ affineOpen i) {n : ℕ} :
    (n : ℕ∞) ≤ mult F P ↔ ∀ m : Fin 2 →₀ ℕ, m.degree < n →
      (taylor (affineChart i P) (dehomogenize i F)).coeff m = 0 := by
  rw [mult_eq_orderAt_dehomogenize hF hP, le_orderAt_iff]
  simp

/-- The exponents of the monomials of total degree `< n` in two variables. -/
private noncomputable def lowExponents (n : ℕ) : Finset (Fin 2 →₀ ℕ) :=
  (Finset.range n).biUnion fun j ↦ Finset.univ.finsuppAntidiag j

private theorem mem_lowExponents {n : ℕ} {m : Fin 2 →₀ ℕ} :
    m ∈ lowExponents n ↔ m.degree < n := by
  simp [lowExponents, Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]

private theorem card_lowExponents (n : ℕ) : (lowExponents n).card = n * (n + 1) / 2 := by
  rw [lowExponents, Finset.card_biUnion]
  · simp only [Finset.card_finsuppAntidiag_nat_eq_multichoose, Finset.card_univ,
      Fintype.card_fin, Nat.multichoose_two]
    have h : ∀ n, 2 * ∑ j ∈ Finset.range n, (j + 1) = n * (n + 1) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ, mul_add, ih]; ring
    rw [← h n]
    omega
  · intro j _ l _ hjl
    refine Finset.disjoint_left.2 fun s hj hl ↦ hjl ?_
    rw [Finset.mem_finsuppAntidiag] at hj hl
    exact hj.1.symm.trans hl.1

/-- The Taylor coefficients of total degree `< n` at `a` of the dehomogenization `F_(i)`. -/
private noncomputable def chartConditions (i : Fin 3) (a : Fin 2 → k) (n : ℕ) :
    MvPolynomial (Fin 3) k →ₗ[k] (lowExponents n → k) :=
  LinearMap.pi fun m ↦
    lcoeff k m.1 ∘ₗ (taylor a).toLinearMap ∘ₗ (dehomogenize (R := k) i).toLinearMap

private theorem chartConditions_apply (i : Fin 3) (a : Fin 2 → k) (n : ℕ)
    (F : MvPolynomial (Fin 3) k) (m : lowExponents n) :
    chartConditions i a n F m = (taylor a (dehomogenize i F)).coeff m :=
  rfl

private theorem chartConditions_eq_zero_iff (hF : F.IsHomogeneous d) {i : Fin 3}
    (hP : P ∈ affineOpen i) {n : ℕ} :
    chartConditions i (affineChart i P) n F = 0 ↔ (n : ℕ∞) ≤ mult F P := by
  rw [le_mult_iff_coeff_taylor_dehomogenize hF hP, funext_iff]
  simp [chartConditions_apply, mem_lowExponents]

/-- For `n ≤ d + 1` the conditions are independent on forms of degree `d`: any values of the
Taylor coefficients of degree `< n` are taken by some form of degree `d`. -/
private theorem chartConditions_surjective (i : Fin 3) (a : Fin 2 → k) {n : ℕ}
    (hn : n ≤ d + 1) : Function.Surjective
      ((chartConditions i a n).domRestrict (homogeneousSubmodule (Fin 3) k d)) := by
  intro c
  set g : MvPolynomial (Fin 2) k := ∑ m : lowExponents n, monomial m.1 (c m)
  have hg : (taylor (-a) g).totalDegree ≤ d := by
    refine (totalDegree_taylor_le _ _).trans ((totalDegree_finsetSum _ _).trans ?_)
    refine Finset.sup_le fun m _ ↦ (totalDegree_monomial_le _ _).trans ?_
    have := mem_lowExponents.1 m.2
    rw [Finsupp.degree_eq_sum] at this
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simp only [id]
    omega
  obtain ⟨q, hq, hdq⟩ := exists_isHomogeneous_dehomogenize_eq i hg
  refine ⟨⟨q, (mem_homogeneousSubmodule _ _).2 hq⟩, funext fun m ↦ ?_⟩
  rw [LinearMap.domRestrict_apply, chartConditions_apply, hdq]
  have := taylor_neg_taylor (-a) g
  rw [neg_neg] at this
  rw [this, coeff_sum, Finset.sum_eq_single_of_mem m (Finset.mem_univ _)]
  · simp
  · intro b _ hb
    rw [coeff_monomial, ite_eq_right_iff.2 fun h ↦ absurd h (Subtype.val_injective.ne hb)]

private theorem finrank_homogeneousSubmodule_fin_three (d : ℕ) :
    finrank k (homogeneousSubmodule (Fin 3) k d) = (d + 1) * (d + 2) / 2 := by
  rw [finrank_homogeneousSubmodule_eq_multichoose, Fintype.card_fin]
  have := Nat.two_mul_multichoose_three d
  rw [mul_comm (d + 1)]
  omega

/-! ### Dimension counts -/

/-- **One point imposes `r(r + 1)/2` independent conditions.** For a point `P` of `ℙ²` and
`r ≤ d + 1`, the forms of degree `d` with `m_P(F) ≥ r` form a subspace of codimension
`r(r + 1)/2` in the space of forms of degree `d`, which has dimension `(d + 1)(d + 2)/2`. -/
theorem finrank_linearSystem_single_add {r : ℕ} (hr : r ≤ d + 1) (P : ℙ k (Fin 3 → k)) :
    finrank k (linearSystem d (Finsupp.single P r)) + r * (r + 1) / 2 =
      (d + 1) * (d + 2) / 2 := by
  obtain ⟨i, hi⟩ := exists_mem_affineOpen P
  set H := homogeneousSubmodule (Fin 3) k d
  set φ := (chartConditions i (affineChart i P) r).domRestrict H
  have hker : LinearMap.ker φ = (linearSystem d (Finsupp.single P r)).comap H.subtype := by
    ext ⟨F, hF⟩
    rw [mem_homogeneousSubmodule] at hF
    simp [φ, LinearMap.domRestrict_apply, chartConditions_eq_zero_iff hF hi,
      mem_linearSystem_single, hF]
  have hrange : finrank k (LinearMap.range φ) = r * (r + 1) / 2 := by
    rw [LinearMap.range_eq_top.2 (chartConditions_surjective i _ hr), finrank_top,
      Module.finrank_fintype_fun_eq_card, Fintype.card_coe, card_lowExponents]
  rw [← finrank_homogeneousSubmodule_fin_three (k := k) d,
    ← LinearMap.finrank_range_add_finrank_ker φ, hrange, hker, (Submodule.comapSubtypeEquivOfLe
      (linearSystem_le_homogeneousSubmodule d _)).finrank_eq, add_comm]

/-- **Lower bound for the dimension of a linear system.** For points `P` of `ℙ²` with assigned
multiplicities `r P`, the space `V(d; r)` of forms of degree `d` with `m_P(F) ≥ r P` for every
`P` has dimension at least `(d + 1)(d + 2)/2 - ∑_P r_P(r_P + 1)/2`. Equivalently, as a linear
subvariety of `ℙ^{d(d+3)/2}`, its dimension is at least `d(d + 3)/2 - ∑_P r_P(r_P + 1)/2`. -/
theorem finrank_linearSystem_ge (d : ℕ) (r : ℙ k (Fin 3 → k) →₀ ℕ) :
    (d + 1) * (d + 2) / 2 - r.sum (fun _ n ↦ n * (n + 1) / 2) ≤
      finrank k (linearSystem d r) := by
  choose i hi using fun P : ℙ k (Fin 3 → k) ↦ exists_mem_affineOpen P
  set H := homogeneousSubmodule (Fin 3) k d
  set Φ : H →ₗ[k] ((P : r.support) → lowExponents (r P) → k) :=
    LinearMap.pi fun P ↦ (chartConditions (i P) (affineChart (i P) P.1) (r P)).domRestrict H
  have hker : LinearMap.ker Φ = (linearSystem d r).comap H.subtype := by
    ext ⟨F, hF⟩
    rw [mem_homogeneousSubmodule] at hF
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply,
      mem_linearSystem, hF, true_and, funext_iff, Φ, LinearMap.pi_apply,
      LinearMap.domRestrict_apply, Pi.zero_apply]
    refine ⟨fun h P ↦ ?_, fun h P ↦ ?_⟩
    · by_cases hP : P ∈ r.support
      · exact (chartConditions_eq_zero_iff hF (hi P)).1 (funext (h ⟨P, hP⟩))
      · simp [Finsupp.notMem_support_iff.1 hP]
    · exact congrFun ((chartConditions_eq_zero_iff hF (hi P)).2 (h P))
  have hrange : finrank k (LinearMap.range Φ) ≤ r.sum (fun _ n ↦ n * (n + 1) / 2) := by
    refine (Submodule.finrank_le _).trans_eq ?_
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, card_lowExponents]
    exact Finset.sum_coe_sort r.support fun P ↦ r P * (r P + 1) / 2
  have := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hker, (Submodule.comapSubtypeEquivOfLe
      (linearSystem_le_homogeneousSubmodule d _)).finrank_eq,
    finrank_homogeneousSubmodule_fin_three] at this
  omega

end PlaneCurves.Projective

end
