/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Adjoint.RiemannRochSpace
public import PlaneCurves.RingTheory.MvPolynomial.Homogeneous

/-!
# The genus of a plane curve with only ordinary multiple points

Let `k` be an algebraically closed field and `C : F = 0` an irreducible projective plane curve of
degree `d` all of whose multiple points are ordinary, with `r_P = m_P(C)`. Its genus, the genus
`g` of the function field `k(C)`, is given by
`2 g = (d - 1)(d - 2) - ∑_P r_P (r_P - 1)`.

The proof is the book's. For a line `L` with `F ∤ L` and `m = d + e` large, the exact sequence
`0 → W_e → V_m → L(E_m) → 0` and the dimension of `V_m` give
`l(E_m) = (m + 1)(m + 2)/2 - (e + 1)(e + 2)/2 - ∑_P r_P (r_P - 1)/2`, while
`deg E_m = m d - ∑_P r_P (r_P - 1)` is large, so `l(E_m) = deg E_m + 1 - g` by Riemann's theorem
(Corollary 3). Comparing the two gives the formula. With `m = d - 3` the same sequence and the
lower bound for `dim V_m` give `l(E_{d-3}) ≥ g`, and `deg E_{d-3} = 2 g - 2`.

## Main results

* `PlaneCurves.Projective.two_mul_genus_eq_sub_degree_adjointDivisor`:
  `2 g = (d - 1)(d - 2) - deg E`.
* `PlaneCurves.Projective.two_mul_genus_eq`: `2 g = (d - 1)(d - 2) - ∑_P r_P (r_P - 1)`.
* `PlaneCurves.Projective.degree_zsmul_formDivisor_sub_adjointDivisor`:
  `deg ((d - 3) div L - E) = 2 g - 2`.
* `PlaneCurves.Projective.genus_le_dim_zsmul_formDivisor_sub_adjointDivisor`:
  `g ≤ l((d - 3) div L - E)`.
* `PlaneCurves.Projective.genus_functionField_of_isNonsingular`: a nonsingular plane curve of
  degree `d` has genus `(d - 1)(d - 2) / 2`.
* `PlaneCurves.Projective.two_mul_genus_eq_spec`: the milestone.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §8.3
-/

public section

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace TauCeti Module
open TauCeti.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization

namespace PlaneCurves.Projective

variable {k : Type*} [Field k] [IsAlgClosed k] {F : MvPolynomial (Fin 3) k} {d : ℕ}
  {hF : F.IsHomogeneous d} [Fact (Irreducible F)]
  (hord : ∀ P, IsMultiplePoint F P → IsOrdinaryMultiplePoint F P)

/-! ### Arithmetic of the sums over the multiple points -/

omit [IsAlgClosed k] [Fact (Irreducible F)] in
/-- `2 ((n + 1)(n + 2)/2) = (n + 1)(n + 2)`. -/
private theorem two_mul_succ_mul_succ_succ_div_two (n : ℕ) :
    2 * ((n + 1) * (n + 2) / 2) = (n + 1) * (n + 2) :=
  Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (n + 1))

omit [IsAlgClosed k] in
/-- Only the multiple points contribute to `∑_P r_P (r_P - 1)`. -/
private theorem support_mult_mul_subset :
    (Function.support fun P : ℙ k (Fin 3 → k) ↦ (mult F P).toNat * ((mult F P).toNat - 1)) ⊆
      {P | IsMultiplePoint F P} := by
  intro P hP
  rw [Function.mem_support] at hP
  rw [Set.mem_ofPred_eq, isMultiplePoint_def, ←
    natCast_toNat_mult (Fact.out : Irreducible F).ne_zero]
  by_contra h
  have h' : ((mult F P).toNat : ℕ∞) < (2 : ℕ) := not_le.1 h
  have : (mult F P).toNat < 2 := by exact_mod_cast h'
  interval_cases (mult F P).toNat <;> simp at hP

omit [IsAlgClosed k] in
/-- `2 ∑_P r_P (r_P - 1)/2 = ∑_P r_P (r_P - 1)`, in `ℤ`. -/
private theorem two_mul_finsum_mult_mul_div_two (hfin : {P | IsMultiplePoint F P}.Finite) :
    2 * ((∑ᶠ P : ℙ k (Fin 3 → k), (mult F P).toNat * ((mult F P).toNat - 1) / 2 : ℕ) : ℤ) =
      ∑ᶠ P : ℙ k (Fin 3 → k), (((mult F P).toNat * ((mult F P).toNat - 1) : ℕ) : ℤ) := by
  have h := (Nat.castAddMonoidHom ℤ).map_finsum (hfin.subset support_mult_mul_subset)
  simp only [Nat.coe_castAddMonoidHom] at h
  rw [← h]
  exact_mod_cast (mul_finsum _ 2).trans (finsum_congr fun P ↦
    Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (mult F P).toNat))

omit [IsAlgClosed k] [Fact (Irreducible F)] in
/-- `∑_P r_P (r_P - 1) ≥ 0`. -/
private theorem finsum_mult_mul_nonneg :
    0 ≤ ∑ᶠ P : ℙ k (Fin 3 → k), (((mult F P).toNat * ((mult F P).toNat - 1) : ℕ) : ℤ) :=
  finsum_nonneg fun _ ↦ Int.natCast_nonneg _

omit [IsAlgClosed k] in
/-- A nonsingular curve has no multiple points, so `∑_P r_P (r_P - 1) = 0`. -/
private theorem finsum_mult_mul_eq_zero_of_isNonsingular
    (hF : F.IsHomogeneous d) (hns : IsNonsingular F) :
    ∑ᶠ P : ℙ k (Fin 3 → k), (((mult F P).toNat * ((mult F P).toNat - 1) : ℕ) : ℤ) = 0 :=
  finsum_eq_zero_of_forall_eq_zero fun P ↦ by
    have : (mult F P).toNat * ((mult F P).toNat - 1) = 0 :=
      Function.notMem_support.1 fun h ↦ hns.not_isMultiplePoint hF P (support_mult_mul_subset h)
    simp [this]

/-! ### The genus formula -/

variable (hF) in
include hord in
/-- **The genus formula**, with the adjoint divisor: if every multiple point of the irreducible
plane curve `C : F = 0` of degree `d` is ordinary, its genus `g` satisfies
`2 g = (d - 1)(d - 2) - deg E`. -/
theorem two_mul_genus_eq_sub_degree_adjointDivisor :
    2 * (genus k (functionField hF) : ℤ) =
      ((d : ℤ) - 1) * ((d : ℤ) - 2) - Divisor.degree (adjointDivisor hF) := by
  have hirr : Irreducible F := Fact.out
  have hfin := finite_setOf_isMultiplePoint_of_irreducible hF hirr
  have hd : d ≠ 0 := hF.degree_ne_zero_of_irreducible hirr
  obtain ⟨c, hc⟩ := exists_forall_dim_eq_degree_add_one_sub_genus
    (functionField.isFunctionField hF) isIntegrallyClosedIn_of_isAlgClosed
  obtain ⟨i, hi⟩ := projectivePlaneCurve.exists_not_dvd_X hirr
  have hL : (X i : MvPolynomial (Fin 3) k).IsHomogeneous 1 := isHomogeneous_X k i
  set E := Divisor.degree (adjointDivisor hF)
  set s := ∑ᶠ P : ℙ k (Fin 3 → k), ((mult F P).toNat - 1)
  set e := s + c.toNat + E.toNat
  have hdeg : Divisor.degree ((d + e) • formDivisor hF hL - adjointDivisor hF) =
      ((d + e : ℕ) : ℤ) * d - E := by
    rw [map_sub, map_nsmul, degree_formDivisor hL hi, nsmul_eq_mul]
    push_cast
    ring
  have hl := hc _ (by
    rw [hdeg]
    have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hd
    have hc' := Int.self_le_toNat c
    have hE' := Int.self_le_toNat E
    have he : (c.toNat : ℤ) + E.toNat ≤ e := by simp only [e]; push_cast; omega
    have : (e : ℤ) ≤ ((d + e : ℕ) : ℤ) * d := by
      push_cast
      nlinarith [mul_nonneg (Int.natCast_nonneg e) (sub_nonneg.2 hd1)]
    omega)
  have h1 := dim_add_finrank_eq_finrank_adjointSubmodule (hF := hF) hord hL hi e
  rw [finrank_adjointSubmodule_eq hirr.ne_zero hfin (m := d + e) (by omega),
    finrank_homogeneousSubmodule_fin_three] at h1
  have hA := two_mul_succ_mul_succ_succ_div_two (d + e)
  have hW := two_mul_succ_mul_succ_succ_div_two e
  have hB := two_mul_finsum_mult_mul_div_two hfin
  rw [← degree_adjointDivisor (hF := hF) hord] at hB
  generalize (d + e + 1) * (d + e + 2) / 2 = A at h1 hA
  generalize (e + 1) * (e + 2) / 2 = W at h1 hW
  generalize ∑ᶠ P : ℙ k (Fin 3 → k), (mult F P).toNat * ((mult F P).toNat - 1) / 2 = B at h1 hB
  have hw : 1 ≤ W := by nlinarith
  have hBA : B ≤ A := by omega
  have h1' : (Divisor.dim ((d + e) • formDivisor hF hL - adjointDivisor hF) : ℤ) + W =
      (A : ℤ) - B := by
    rw [← Nat.cast_sub hBA, ← h1]
    push_cast
    ring
  rw [hl, hdeg] at h1'
  have hA' : (2 : ℤ) * A = (d + e + 1) * (d + e + 2) := by exact_mod_cast hA
  have hW' : (2 : ℤ) * W = (e + 1) * (e + 2) := by exact_mod_cast hW
  push_cast at h1'
  linear_combination -2 * h1' - hA' + hW' + hB

variable (hF) in
include hord in
/-- **The genus formula**: if every multiple point of the irreducible plane curve `C : F = 0` of
degree `d` is ordinary, with `r_P = m_P(C)`, its genus `g` satisfies
`2 g = (d - 1)(d - 2) - ∑_P r_P (r_P - 1)`. -/
theorem two_mul_genus_eq :
    2 * (genus k (functionField hF) : ℤ) = ((d : ℤ) - 1) * ((d : ℤ) - 2) -
      ∑ᶠ P : ℙ k (Fin 3 → k), (((mult F P).toNat * ((mult F P).toNat - 1) : ℕ) : ℤ) := by
  rw [two_mul_genus_eq_sub_degree_adjointDivisor hF hord, degree_adjointDivisor hord]

section Line

variable {L : MvPolynomial (Fin 3) k} (hL : L.IsHomogeneous 1) (hFL : ¬ F ∣ L)
include hord hL hFL

/-- **The degree of `E_{d-3}`**: for a line `L` with `F ∤ L`,
`deg ((d - 3) div L - E) = 2 g - 2`. -/
theorem degree_zsmul_formDivisor_sub_adjointDivisor :
    Divisor.degree (((d : ℤ) - 3) • formDivisor hF hL - adjointDivisor hF) =
      2 * (genus k (functionField hF) : ℤ) - 2 := by
  rw [map_sub, map_zsmul, degree_formDivisor hL hFL,
    two_mul_genus_eq_sub_degree_adjointDivisor hF hord, smul_eq_mul]
  ring

/-- **`l(E_{d-3}) ≥ g`**: for a line `L` with `F ∤ L`, `g ≤ l((d - 3) div L - E)`. -/
theorem genus_le_dim_zsmul_formDivisor_sub_adjointDivisor :
    genus k (functionField hF) ≤
      Divisor.dim (((d : ℤ) - 3) • formDivisor hF hL - adjointDivisor hF) := by
  have hirr : Irreducible F := Fact.out
  have hfin := finite_setOf_isMultiplePoint_of_irreducible hF hirr
  have hg := two_mul_genus_eq hF hord
  have hd : d ≠ 0 := hF.degree_ne_zero_of_irreducible hirr
  have h := finrank_adjointSubmodule_ge hirr.ne_zero hfin (d - 3)
  rw [← two_mul_finsum_mult_mul_div_two hfin] at hg
  generalize ∑ᶠ P : ℙ k (Fin 3 → k), (mult F P).toNat * ((mult F P).toNat - 1) / 2 = B at h hg
  rcases lt_or_ge d 3 with h3 | h3
  · -- for `d = 1, 2`, `(d - 1)(d - 2) = 0`, so `g = 0`
    have : genus k (functionField hF) = 0 := by
      interval_cases d <;> norm_num at hg <;> omega
    simp [this]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h3
  rw [show ((3 + m : ℕ) : ℤ) - 3 = (m : ℤ) by push_cast; ring, natCast_zsmul,
    dim_eq_finrank_adjointSubmodule hord hL hFL (by omega)]
  rw [Nat.add_sub_cancel_left] at h
  have hA := two_mul_succ_mul_succ_succ_div_two m
  generalize (m + 1) * (m + 2) / 2 = A at h hA
  have hA' : (2 : ℤ) * A = (m + 1) * (m + 2) := by exact_mod_cast hA
  have : 2 * ((genus k (functionField hF) : ℤ) + B) = 2 * A := by
    push_cast at hg
    linear_combination hg - hA'
  omega

end Line

/-! ### Nonsingular curves -/

/-- **The genus of a nonsingular plane curve**: the function field of a nonsingular plane curve
of degree `d` has genus `(d - 1)(d - 2) / 2`. -/
theorem genus_functionField_of_isNonsingular (hF : F.IsHomogeneous d) (hns : IsNonsingular F) :
    genus k (functionField hF) = (d - 1) * (d - 2) / 2 := by
  have hg := two_mul_genus_eq hF fun P hP ↦ absurd hP (hns.not_isMultiplePoint hF P)
  rw [finsum_mult_mul_eq_zero_of_isNonsingular hF hns, sub_zero] at hg
  have h : (((d - 1) * (d - 2) : ℕ) : ℤ) = ((d : ℤ) - 1) * ((d : ℤ) - 2) := by
    rcases d with _ | _ | d
    · exact absurd rfl (hF.degree_ne_zero_of_irreducible Fact.out)
    · simp
    · push_cast [Nat.add_sub_cancel, show d + 1 + 1 - 2 = d by omega]
      ring
  rw [← h] at hg
  generalize (d - 1) * (d - 2) = x at hg ⊢
  omega

/-! ### The milestone -/

/-- **The genus formula for plane curves with only ordinary multiple points** (Fulton, §8.3,
Proposition 5 and Corollary 3(b)). Let `k` be algebraically closed and `C : F = 0` an irreducible
projective plane curve of degree `d` all of whose multiple points are ordinary, with
`r_P = m_P(C)`, function field `k(C)` of genus `g` and adjoint divisor `E`. Then

1. `2 g = (d - 1)(d - 2) - ∑_P r_P (r_P - 1)`, the sum running over all points of `ℙ²` (simple
   points and points off `C` contribute `0`);
2. for every line `L` with `F ∤ L`, `E_{d-3} = (d - 3) div L - E` has degree `2 g - 2` and
   `l(E_{d-3}) ≥ g`;
3. in particular, a nonsingular plane curve of degree `d` has `2 g = (d - 1)(d - 2)`: lines and
   conics have genus `0`, cubics genus `1` and quartics genus `3`.

The book states the formula as `g = (d - 1)(d - 2)/2 - ∑_P r_P (r_P - 1)/2`; both sides of the
doubled form are integers. The nonsingular case, in the book's form, is
`PlaneCurves.Projective.genus_functionField_of_isNonsingular`.

Milestone: *Genus formula for plane curves with only ordinary multiple points*. -/
theorem two_mul_genus_eq_spec (hF : F.IsHomogeneous d)
    (hord : ∀ P, IsMultiplePoint F P → IsOrdinaryMultiplePoint F P) :
    2 * (genus k (functionField hF) : ℤ) = ((d : ℤ) - 1) * ((d : ℤ) - 2) -
      ∑ᶠ P : ℙ k (Fin 3 → k), (((mult F P).toNat * ((mult F P).toNat - 1) : ℕ) : ℤ) ∧
    (∀ {L : MvPolynomial (Fin 3) k} (hL : L.IsHomogeneous 1), ¬ F ∣ L →
      Divisor.degree (((d : ℤ) - 3) • formDivisor hF hL - adjointDivisor hF) =
        2 * (genus k (functionField hF) : ℤ) - 2 ∧
      genus k (functionField hF) ≤
        Divisor.dim (((d : ℤ) - 3) • formDivisor hF hL - adjointDivisor hF)) ∧
    (IsNonsingular F → 2 * (genus k (functionField hF) : ℤ) = ((d : ℤ) - 1) * ((d : ℤ) - 2)) :=
  ⟨two_mul_genus_eq hF hord, fun hL hFL ↦
    ⟨degree_zsmul_formDivisor_sub_adjointDivisor hord hL hFL,
      genus_le_dim_zsmul_formDivisor_sub_adjointDivisor hord hL hFL⟩,
    fun hns ↦ by
      rw [two_mul_genus_eq hF hord, finsum_mult_mul_eq_zero_of_isNonsingular hF hns, sub_zero]⟩

end PlaneCurves.Projective

end
