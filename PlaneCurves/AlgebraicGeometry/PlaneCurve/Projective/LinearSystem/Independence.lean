/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.LinearSystem.Basic
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.LinearSubvariety
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.ChartLocalRing
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Independence of the conditions imposed by assigned multiple points

For points `P` of `ℙ²` with assigned multiplicities `r P`, the linear system `V(d; r)` of forms
of degree `d` with `m_P(F) ≥ r P` has dimension at least `(d + 1)(d + 2)/2 - ∑ r_P(r_P + 1)/2`
(`finrank_linearSystem_ge`). This file shows that equality holds when `d ≥ ∑ r_P - 1`: the
conditions are then independent.

The proof works over any field, with a triangular family of forms instead of Fulton's
induction. For a point `P`, let `G` be the product of `L_Q^{r_Q}` over the other points `Q`,
where `L_Q` is a line through `Q` missing `P`. Then `G` satisfies the conditions at every other
point, and its residue in `k[X, Y] ⧸ (X, Y)^{r_P}` at `P` is a unit since `G(P) ≠ 0`. The forms
`G H` with `H` of degree `e = d - ∑_{Q ≠ P} r_Q ≥ r_P - 1` therefore realize every value of the
conditions at `P`, and none at the other points.

## Main results

* `PlaneCurves.Projective.isUnit_chartConditions`: the residue of a form not vanishing at `P`
  is a unit.
* `PlaneCurves.Projective.multConditions_surjective`: for `∑ r_P ≤ d + 1` the multiplicity
  conditions of `V(d; r)` are onto.
* `PlaneCurves.Projective.finrank_linearSystem_add`,
  `PlaneCurves.Projective.finrank_linearSystem_eq`: for `∑ r_P ≤ d + 1`, `V(d; r)` has
  dimension exactly `(d + 1)(d + 2)/2 - ∑ r_P(r_P + 1)/2`.
* `PlaneCurves.Projective.finrank_linearSystem_and_properties`: the dimension of linear systems
  of plane curves with assigned multiple points, Fulton's Lemma and Theorem 1 of §5.2.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.2
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Module Projectivization TauCeti PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] {G : MvPolynomial (Fin 3) k} {P : ℙ k (Fin 3 → k)} {d e : ℕ}

/-- **Forms not through a point are units modulo its conditions.** For a form `G` with
`G(P) ≠ 0` and `P` in the chart `Xᵢ ≠ 0`, the residue of `G` in `k[X, Y] ⧸ (X, Y)ⁿ` at the chart
coordinates of `P` is a unit. -/
theorem isUnit_chartConditions (hG : G.IsHomogeneous e) {i : Fin 3} (hP : P ∈ affineOpen i)
    (hGP : eval P.rep G ≠ 0) (n : ℕ) :
    IsUnit (chartConditions i (affineChart i P) n G) := by
  have hc : constantCoeff (taylor (affineChart i P) (dehomogenize i G)) ≠ 0 := by
    rwa [constantCoeff_taylor, Ne, eval_affineChart_dehomogenize_eq_zero_iff hP hG]
  set t := taylor (affineChart i P) (dehomogenize i G)
  set c := constantCoeff t
  have ht : t - C c ∈ idealOfVars (Fin 2) k := by
    rw [← ker_constantCoeff, RingHom.mem_ker, map_sub, constantCoeff_C, sub_self]
  have hnil : IsNilpotent (Ideal.Quotient.mk (idealOfVars (Fin 2) k ^ n) (t - C c)) :=
    ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow ht n⟩
  have hu : IsUnit (Ideal.Quotient.mk (idealOfVars (Fin 2) k ^ n) (C c)) :=
    (hc.isUnit.map C).map _
  have := hnil.isUnit_add_left_of_commute hu (Commute.all _ _)
  rwa [← map_add, add_sub_cancel, ← chartConditions_apply] at this

/-- For distinct points `P ≠ Q` of `ℙ²` there is a line through `Q` missing `P`. -/
private theorem exists_linear_form (P Q : ℙ k (Fin 3 → k)) (h : Q ≠ P) :
    ∃ L : MvPolynomial (Fin 3) k, L.IsHomogeneous 1 ∧ eval Q.rep L = 0 ∧ eval P.rep L ≠ 0 := by
  obtain ⟨a, hQ, hP⟩ := exists_sum_C_mul_X_mem_zeroLocus_notMem_zeroLocus h
  rw [mem_zeroLocus_singleton_sum_C_mul_X_iff] at hQ hP
  exact ⟨_, isHomogeneous_sum_C_mul_X a, by simpa [dotProduct] using hQ,
    by simpa [dotProduct] using hP⟩

open scoped Classical in
/-- For `∑ r_Q ≤ d + 1`, every value of the conditions at one point `P` of the support of `r`,
with the conditions at the other points zero, is attained by a form of degree `d`. -/
private theorem single_mem_range_multConditions {r : ℙ k (Fin 3 → k) →₀ ℕ}
    (hd : r.sum (fun _ n ↦ n) ≤ d + 1) {i : ℙ k (Fin 3 → k) → Fin 3}
    (hi : ∀ P, P ∈ affineOpen (i P)) (P : r.support)
    (c : MvPolynomial (Fin 2) k ⧸ idealOfVars (Fin 2) k ^ r P) :
    Pi.single P c ∈ LinearMap.range (multConditions d r i) := by
  classical
  choose! L hL hLQ hLP using fun Q ↦ exists_linear_form P.1 Q
  set S := r.support.erase P.1
  set s := ∑ Q ∈ S, r Q
  set G := ∏ Q ∈ S, L Q ^ r Q
  have hsum : r P + s = r.sum (fun _ n ↦ n) := Finset.add_sum_erase _ _ P.2
  have hP0 : 0 < r P := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 P.2)
  have hG : G.IsHomogeneous s := by
    simpa using IsHomogeneous.prod S _ _ fun Q hQ ↦ (hL Q (Finset.ne_of_mem_erase hQ)).pow (r Q)
  have hGP : eval P.1.rep G ≠ 0 := by
    simp only [G, map_prod, map_pow]
    exact Finset.prod_ne_zero_iff.2 fun Q hQ ↦ pow_ne_zero _ (hLP Q (Finset.ne_of_mem_erase hQ))
  obtain ⟨u, hu⟩ := isUnit_chartConditions hG (hi P) hGP (r P)
  obtain ⟨⟨H, hH⟩, hHc⟩ := chartConditions_surjective (d := d - s) (i P)
    (affineChart (i P) P.1) (n := r P) (by omega) (↑u⁻¹ * c)
  rw [LinearMap.domRestrict_apply] at hHc
  rw [mem_homogeneousSubmodule] at hH
  have hF : (G * H).IsHomogeneous d := by
    simpa [show s + (d - s) = d by omega] using hG.mul hH
  refine ⟨⟨G * H, (mem_homogeneousSubmodule _ _).2 hF⟩, funext fun Q ↦ ?_⟩
  rw [multConditions_apply]
  rcases eq_or_ne Q P with rfl | hQP
  · rw [Pi.single_eq_same, chartConditions_mul, ← hu, hHc, Units.mul_inv_cancel_left]
  · rw [Pi.single_eq_of_ne hQP, chartConditions_eq_zero_iff hF (hi Q), mult_mul]
    have hQS : Q.1 ∈ S := Finset.mem_erase.2 ⟨Subtype.coe_ne_coe.2 hQP, Q.2⟩
    have hLQ1 : (1 : ℕ∞) ≤ mult (L Q) Q := by
      rw [Order.one_le_iff_pos, mult_pos_iff_eval_rep]
      exact hLQ Q (Subtype.coe_ne_coe.2 hQP)
    calc (r Q : ℕ∞) = r Q • 1 := by simp
      _ ≤ r Q • mult (L Q) Q := nsmul_le_nsmul_right hLQ1 _
      _ ≤ ∑ Q' ∈ S, r Q' • mult (L Q') Q :=
        Finset.single_le_sum (f := fun Q' ↦ r Q' • mult (L Q') Q) (fun _ _ ↦ zero_le) hQS
      _ = mult G Q := (mult_prod_pow S L r Q).symm
      _ ≤ mult G Q + mult H Q := le_self_add

/-- **The multiplicity conditions are independent.** For points `P` of `ℙ²` with assigned
multiplicities `r P` and `∑_P r_P ≤ d + 1`, the multiplicity conditions of `V(d; r)` on the forms
of degree `d` are onto `∏_P k[X, Y] ⧸ (X, Y)^{r_P}`. -/
theorem multConditions_surjective {r : ℙ k (Fin 3 → k) →₀ ℕ} (hd : r.sum (fun _ n ↦ n) ≤ d + 1)
    {i : ℙ k (Fin 3 → k) → Fin 3} (hi : ∀ P, P ∈ affineOpen (i P)) :
    Function.Surjective (multConditions d r i) := by
  classical
  rw [← LinearMap.range_eq_top, eq_top_iff]
  intro f _
  rw [← Finset.univ_sum_single f]
  exact Submodule.sum_mem _ fun P _ ↦ single_mem_range_multConditions hd hi P (f P)

/-- **Dimension of a linear system with independent conditions.** For points `P` of `ℙ²` with
assigned multiplicities `r P` and `d ≥ ∑_P r_P - 1`, the conditions `m_P(F) ≥ r_P` are
independent: `dim V(d; r) + ∑_P r_P(r_P + 1)/2 = (d + 1)(d + 2)/2`. -/
theorem finrank_linearSystem_add {r : ℙ k (Fin 3 → k) →₀ ℕ} (hd : r.sum (fun _ n ↦ n) ≤ d + 1) :
    finrank k (linearSystem d r) + r.sum (fun _ n ↦ n * (n + 1) / 2) = (d + 1) * (d + 2) / 2 := by
  choose i hi using fun P : ℙ k (Fin 3 → k) ↦ exists_mem_affineOpen P
  rw [← finrank_range_multConditions_add d r hi,
    LinearMap.range_eq_top.2 (multConditions_surjective hd hi), finrank_top,
    finrank_pi_quotient_pow_idealOfVars, add_comm]

/-- For points `P` of `ℙ²` with assigned multiplicities `r P` and `d ≥ ∑_P r_P - 1`, the linear
system `V(d; r)` has dimension `(d + 1)(d + 2)/2 - ∑_P r_P(r_P + 1)/2`; as a linear subvariety of
`ℙ^{d(d+3)/2}`, its dimension is `d(d + 3)/2 - ∑_P r_P(r_P + 1)/2`. -/
theorem finrank_linearSystem_eq {r : ℙ k (Fin 3 → k) →₀ ℕ} (hd : r.sum (fun _ n ↦ n) ≤ d + 1) :
    finrank k (linearSystem d r) = (d + 1) * (d + 2) / 2 - r.sum (fun _ n ↦ n * (n + 1) / 2) := by
  have := finrank_linearSystem_add hd
  omega

/-- **Through any `d(d + 3)/2` points passes a curve of degree `d`.** For finitely many points
of `ℙ²` (the support of `r`, with `r P ≤ 1`), at most `d(d + 3)/2` of them, there is a nonzero
form of degree `d` vanishing at all of them. -/
theorem exists_ne_zero_mem_linearSystem {r : ℙ k (Fin 3 → k) →₀ ℕ} (hr : ∀ P, r P ≤ 1)
    (hcard : r.support.card ≤ d * (d + 3) / 2) : ∃ F ∈ linearSystem d r, F ≠ 0 := by
  have hsum : r.sum (fun _ n ↦ n * (n + 1) / 2) = r.support.card := by
    rw [Finsupp.sum, Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun P hP ↦ ?_
    have := Finsupp.mem_support_iff.1 hP
    obtain h | h : r P = 0 ∨ r P = 1 := by have := hr P; omega
    · exact absurd h this
    · simp [h]
  have hd : d * (d + 3) / 2 + 1 = (d + 1) * (d + 2) / 2 := by
    have h1 : (d + 1) * (d + 2) = d * (d + 3) + 2 := by ring
    rw [h1]
    omega
  have := finrank_linearSystem_ge d r
  rw [hsum] at this
  have hne : linearSystem d r ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at this
    omega
  exact Submodule.exists_mem_ne_zero_of_ne_bot hne

/-- **Dimension of linear systems of plane curves with assigned multiple points.** Over a field
`k`, for `d : ℕ`:

1. the forms of degree `d` in `X, Y, Z` form a space of dimension `(d + 1)(d + 2)/2`, so the
   curves of degree `d` are the points of `ℙ^N`, `N = d(d + 3)/2`;
2. (Lemma) the forms of degree `d` through a point form a hyperplane, and a projective change
   of coordinates `T = [M]` carries `V(d; r)` to `V(d; r ∘ T)` by `F ↦ F^M`; through any
   `d(d + 3)/2` points passes a curve of degree `d`;
3. (a) for a point `P` and `r ≤ d + 1`, the forms with `m_P(F) ≥ r` have codimension
   `r(r + 1)/2`;
4. (b) for assigned multiplicities `r P` at finitely many points, `V(d; r)` has dimension at least
   `(d + 1)(d + 2)/2 - ∑_P r_P(r_P + 1)/2`;
5. (c) if moreover `d ≥ ∑_P r_P - 1`, the dimension is exactly
   `(d + 1)(d + 2)/2 - ∑_P r_P(r_P + 1)/2`.

The dimensions are those of vector spaces; the projective dimensions are one less.

Milestone: *Dimension of linear systems of plane curves with assigned multiple points*. -/
theorem finrank_linearSystem_and_properties (d : ℕ) :
    finrank k (homogeneousSubmodule (Fin 3) k d) = (d + 1) * (d + 2) / 2 ∧
    (∀ P : ℙ k (Fin 3 → k),
      finrank k (linearSystem d (Finsupp.single P 1)) + 1 = (d + 1) * (d + 2) / 2) ∧
    (∀ (M : Matrix (Fin 3) (Fin 3) k) (hM : Function.Injective M.mulVecLin)
      (r : ℙ k (Fin 3 → k) →₀ ℕ) (F : MvPolynomial (Fin 3) k),
      linearSubst M F ∈
          linearSystem d (r.comapDomain (map M.mulVecLin hM) (map_injective _ hM).injOn) ↔
        F ∈ linearSystem d r) ∧
    (∀ r : ℙ k (Fin 3 → k) →₀ ℕ, (∀ P, r P ≤ 1) → r.support.card ≤ d * (d + 3) / 2 →
      ∃ F ∈ linearSystem d r, F ≠ 0) ∧
    (∀ (P : ℙ k (Fin 3 → k)) (r : ℕ), r ≤ d + 1 →
      finrank k (linearSystem d (Finsupp.single P r)) + r * (r + 1) / 2 =
        (d + 1) * (d + 2) / 2) ∧
    (∀ r : ℙ k (Fin 3 → k) →₀ ℕ,
      (d + 1) * (d + 2) / 2 - r.sum (fun _ n ↦ n * (n + 1) / 2) ≤
        finrank k (linearSystem d r)) ∧
    (∀ r : ℙ k (Fin 3 → k) →₀ ℕ, r.sum (fun _ n ↦ n) ≤ d + 1 →
      finrank k (linearSystem d r) =
        (d + 1) * (d + 2) / 2 - r.sum (fun _ n ↦ n * (n + 1) / 2)) :=
  ⟨finrank_homogeneousSubmodule_fin_three d,
    fun P ↦ by simpa using finrank_linearSystem_single_add (d := d) (r := 1) (by omega) P,
    fun _ hM _ _ ↦ linearSubst_mem_linearSystem_iff hM,
    fun _ hr hcard ↦ exists_ne_zero_mem_linearSystem hr hcard,
    fun P _ hr ↦ finrank_linearSystem_single_add hr P,
    finrank_linearSystem_ge d, fun _ hd ↦ finrank_linearSystem_eq hd⟩

/- Two double points impose independent conditions on quartics: `V(4; 2P + 2Q)` has dimension
`15 - 3 - 3 = 9`. -/
example (P Q : ℙ k (Fin 3 → k)) (h : P ≠ Q) :
    finrank k (linearSystem 4 (Finsupp.single P 2 + Finsupp.single Q 2)) = 9 := by
  classical
  have hdisj : Disjoint (Finsupp.single P 2).support (Finsupp.single Q 2).support :=
    (Finsupp.support_single_disjoint two_ne_zero two_ne_zero).2 h
  have hsum (g : ℕ → ℕ) : (Finsupp.single P 2 + Finsupp.single Q 2).sum (fun _ n ↦ g n) =
      g 2 + g 2 := by
    rw [Finsupp.sum, Finsupp.support_add_eq hdisj, Finset.sum_union hdisj]
    simp [Finsupp.single_apply, h, h.symm]
  rw [finrank_linearSystem_eq (by simp only [hsum]; norm_num), hsum]

end PlaneCurves.Projective

end
