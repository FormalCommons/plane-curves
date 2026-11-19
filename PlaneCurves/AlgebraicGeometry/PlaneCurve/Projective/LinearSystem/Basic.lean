/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Multiplicity
public import PlaneCurves.RingTheory.MvPolynomial.HilbertFunction
public import PlaneCurves.RingTheory.MvPolynomial.PowIdealOfVars
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.ChangeOfCoordinates

/-!
# Linear systems of plane curves with assigned multiple points

For `d : ℕ` and `r : ℙ² →₀ ℕ`, assigning the multiplicity `r P` to finitely many points `P`, the
linear system `V(d; r)` is the space of forms `F` of degree `d` in `X, Y, Z` with
`m_P(F) ≥ r P` for every `P` (together with `0`). It is a subspace of the space of forms of
degree `d`, which has dimension `(d + 1)(d + 2)/2`.

In an affine chart `Xᵢ ≠ 0` containing `P`, with chart coordinates `a`, the condition
`m_P(F) ≥ n` says that the Taylor expansion at `a` of the dehomogenization `F_(i)` lies in
`(X, Y)ⁿ`, that is, that `F` lies in the kernel of the linear map `F ↦ taylor a F_(i)` to
`k[X, Y] ⧸ (X, Y)ⁿ`, a space of dimension `n(n + 1)/2`. For `n ≤ d + 1` this map is onto from
the forms of degree `d`. So one point of multiplicity `r ≤ d + 1` imposes exactly `r(r + 1)/2`
conditions, and the points of `r` together impose at most `∑ r_P(r_P + 1)/2`.

The dimensions here are dimensions of vector spaces; the projective dimension of the linear
system is one less.

## Main definitions

* `PlaneCurves.Projective.linearSystem d r`: the linear system `V(d; r)`.

## Main results

* `PlaneCurves.Projective.mem_linearSystem`: membership in `V(d; r)`.
* `PlaneCurves.Projective.linearSubst_mem_linearSystem_iff`: behaviour under a projective change
  of coordinates.
* `PlaneCurves.Projective.le_mult_iff_coeff_taylor_dehomogenize`,
  `PlaneCurves.Projective.le_mult_iff_taylor_dehomogenize_mem`: `m_P(F) ≥ n` in a chart.
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

/-- A form lies in `V(d; r)` exactly when it has degree `d` and `m_P(F) ≥ r P` for every `P`. -/
theorem mem_linearSystem {r : ℙ k (Fin 3 → k) →₀ ℕ} :
    F ∈ linearSystem d r ↔ F.IsHomogeneous d ∧ ∀ P, (r P : ℕ∞) ≤ mult F P :=
  Iff.rfl

/-- The linear system `V(d; r)` consists of forms of degree `d`. -/
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

/-- **Change of coordinates.** For an invertible matrix `M`, with the projective change of
coordinates `T = [M]`, the form `F^M = F(M X)` lies in `V(d; r ∘ T)` exactly when `F` lies in
`V(d; r)`: the multiplicity `r(T(Q))` is assigned to `Q`. -/
theorem linearSubst_mem_linearSystem_iff {M : Matrix (Fin 3) (Fin 3) k}
    (hM : Function.Injective M.mulVecLin) {r : ℙ k (Fin 3 → k) →₀ ℕ} :
    linearSubst M F ∈
        linearSystem d (r.comapDomain (map M.mulVecLin hM) (map_injective _ hM).injOn) ↔
      F ∈ linearSystem d r := by
  have hdet : IsUnit M.det :=
    (Matrix.isUnit_iff_isUnit_det M).1 (Matrix.mulVec_injective_iff_isUnit.1 hM)
  have hhom : (linearSubst M F).IsHomogeneous d ↔ F.IsHomogeneous d :=
    ⟨fun h ↦ by simpa [linearSubst_nonsing_inv_linearSubst hdet] using h.linearSubst M⁻¹,
      fun h ↦ h.linearSubst M⟩
  rw [mem_linearSystem, mem_linearSystem, hhom]
  refine and_congr_right fun hF ↦ ?_
  simp only [Finsupp.comapDomain_apply, mult_linearSubst hF hM]
  exact ((ProjectiveSpace.bijective_map_mulVecLin
    (Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet.ne_zero)).2.forall
    (p := fun P ↦ (r P : ℕ∞) ≤ mult F P)).symm

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

/-- **Multiplicity conditions in a chart, as an ideal.** For a form `F` and a point `P` of the
affine chart `Xᵢ ≠ 0`, `m_P(F) ≥ n` exactly when the Taylor expansion of the dehomogenization
`F_(i)` at the chart coordinates of `P` lies in `(X, Y)ⁿ`. -/
theorem le_mult_iff_taylor_dehomogenize_mem (hF : F.IsHomogeneous d) {i : Fin 3}
    (hP : P ∈ affineOpen i) {n : ℕ} :
    (n : ℕ∞) ≤ mult F P ↔
      taylor (affineChart i P) (dehomogenize i F) ∈ idealOfVars (Fin 2) k ^ n := by
  rw [le_mult_iff_coeff_taylor_dehomogenize hF hP, mem_pow_idealOfVars_iff']

/-- The residue modulo `(X, Y)ⁿ` of the Taylor expansion at `a` of the dehomogenization
`F_(i)`. -/
private noncomputable def chartConditions (i : Fin 3) (a : Fin 2 → k) (n : ℕ) :
    MvPolynomial (Fin 3) k →ₗ[k] MvPolynomial (Fin 2) k ⧸ idealOfVars (Fin 2) k ^ n :=
  (Ideal.Quotient.mkₐ k _).toLinearMap ∘ₗ (taylor a).toLinearMap ∘ₗ
    (dehomogenize (R := k) i).toLinearMap

private theorem chartConditions_apply (i : Fin 3) (a : Fin 2 → k) (n : ℕ)
    (F : MvPolynomial (Fin 3) k) :
    chartConditions i a n F = Ideal.Quotient.mk _ (taylor a (dehomogenize i F)) :=
  rfl

private theorem chartConditions_eq_zero_iff (hF : F.IsHomogeneous d) {i : Fin 3}
    (hP : P ∈ affineOpen i) {n : ℕ} :
    chartConditions i (affineChart i P) n F = 0 ↔ (n : ℕ∞) ≤ mult F P := by
  rw [le_mult_iff_taylor_dehomogenize_mem hF hP, chartConditions_apply,
    Ideal.Quotient.eq_zero_iff_mem]

/-- For `n ≤ d + 1` the conditions are independent on forms of degree `d`: every class modulo
`(X, Y)ⁿ` is the residue of the Taylor expansion of `F_(i)` for some form `F` of degree `d`. -/
private theorem chartConditions_surjective (i : Fin 3) (a : Fin 2 → k) {n : ℕ}
    (hn : n ≤ d + 1) : Function.Surjective
      ((chartConditions i a n).domRestrict (homogeneousSubmodule (Fin 3) k d)) := by
  intro c
  obtain ⟨⟨g, hg⟩, rfl⟩ := (restrictSupportEquivQuotientPowIdealOfVars n).surjective c
  have hgd : (taylor (-a) g).totalDegree ≤ d := by
    refine (totalDegree_taylor_le _ _).trans ((mem_restrictTotalDegree _ _ _).1 ?_)
    rw [← restrictSupport_degree_lt_succ]
    exact restrictSupport_mono k (Set.ofPred_subset_ofPred.2 fun m (hm : m.degree < n) ↦
      show m.degree < d + 1 by omega) hg
  obtain ⟨q, hq, hdq⟩ := exists_isHomogeneous_dehomogenize_eq i hgd
  refine ⟨⟨q, (mem_homogeneousSubmodule _ _).2 hq⟩, ?_⟩
  have := taylor_neg_taylor (-a) g
  rw [neg_neg] at this
  rw [LinearMap.domRestrict_apply, chartConditions_apply, hdq, this,
    restrictSupportEquivQuotientPowIdealOfVars_apply]

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
      finrank_quotient_pow_idealOfVars_fin_two]
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
  set Φ : H →ₗ[k]
      ((P : r.support) → MvPolynomial (Fin 2) k ⧸ idealOfVars (Fin 2) k ^ r P) :=
    LinearMap.pi fun P ↦ (chartConditions (i P) (affineChart (i P) P.1) (r P)).domRestrict H
  have hker : LinearMap.ker Φ = (linearSystem d r).comap H.subtype := by
    ext ⟨F, hF⟩
    rw [mem_homogeneousSubmodule] at hF
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply,
      mem_linearSystem, hF, true_and, funext_iff, Φ, LinearMap.pi_apply,
      LinearMap.domRestrict_apply, Pi.zero_apply]
    refine ⟨fun h P ↦ ?_, fun h P ↦ ?_⟩
    · by_cases hP : P ∈ r.support
      · exact (chartConditions_eq_zero_iff hF (hi P)).1 (h ⟨P, hP⟩)
      · simp [Finsupp.notMem_support_iff.1 hP]
    · exact (chartConditions_eq_zero_iff hF (hi P)).2 (h P)
  have hrange : finrank k (LinearMap.range Φ) ≤ r.sum (fun _ n ↦ n * (n + 1) / 2) := by
    refine (Submodule.finrank_le _).trans_eq ?_
    rw [Module.finrank_pi_fintype]
    simp only [finrank_quotient_pow_idealOfVars_fin_two]
    exact Finset.sum_coe_sort r.support fun P ↦ r P * (r P + 1) / 2
  have := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hker, (Submodule.comapSubtypeEquivOfLe
      (linearSystem_le_homogeneousSubmodule d _)).finrank_eq,
    finrank_homogeneousSubmodule_fin_three] at this
  omega

end PlaneCurves.Projective

end
