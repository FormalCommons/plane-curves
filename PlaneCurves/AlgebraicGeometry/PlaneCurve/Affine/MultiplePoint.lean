/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.AffineSpace.PlaneZeroLocus
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.Multiplicity
public import PlaneCurves.RingTheory.MvPolynomial.PDeriv
public import PlaneCurves.RingTheory.UniqueFactorizationDomain.Radical

/-!
# Finiteness of the multiple points of a plane curve

Over a perfect field, a plane curve without multiple components has only finitely many multiple
points. Conversely, if `G ^ 2` divides `F`, every zero of `G` is a multiple point of `F`, so a
curve with a multiple component has infinitely many multiple points over an infinite field.

The proof covers the multiple points of `F` lying on an irreducible factor `H`, with `F = H G`,
by the common zeros of `H` and `G` and those of `H` and a nonzero partial derivative `∂H/∂Xᵢ`.
Both pairs are relatively prime, since `H ∤ G` (`F` is squarefree) and `H ∤ ∂H/∂Xᵢ` (by degree),
so both sets are finite. Over an imperfect field the statement fails for points over the
algebraic closure: `X ^ p - t Y ^ p` over `𝔽_p(t)` is irreducible with both partial derivatives
zero.

## Main results

* `PlaneCurves.Affine.IsMultiplePoint.eval_eq_zero_or_eval_pderiv_eq_zero`: a multiple point of
  `H G` on `H` is a zero of `G` or of each partial derivative of `H`.
* `PlaneCurves.Affine.IsMultiplePoint.of_sq_dvd`: if `G ^ 2 ∣ F`, every zero of `G` is a
  multiple point of `F`.
* `PlaneCurves.Affine.finite_setOf_isMultiplePoint_of_squarefree`: over a perfect field, a
  squarefree plane curve has finitely many multiple points.
* `PlaneCurves.Affine.finite_multiple_points`: the two statements together, as in §3.1 of
  Fulton.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §3.1, Problem 3.10
-/

public section

namespace PlaneCurves.Affine

open MvPolynomial

section CommRing

variable {R : Type*} [CommRing R] {F G H : MvPolynomial (Fin 2) R} {P : Fin 2 → R}

/-- If `G ^ 2` divides `F`, every zero of `G` is a multiple point of `F`. -/
theorem IsMultiplePoint.of_sq_dvd (hGF : G ^ 2 ∣ F) (hP : eval P G = 0) :
    IsMultiplePoint F P := by
  obtain ⟨A, rfl⟩ := hGF
  have hG : 1 ≤ G.orderAt P := Order.one_le_iff_pos.2 (orderAt_pos_iff.2 hP)
  rw [isMultiplePoint_def, sq]
  calc (2 : ℕ∞) = 1 + 1 + 0 := by norm_num
    _ ≤ G.orderAt P + G.orderAt P + A.orderAt P := by gcongr; simp
    _ ≤ (G * G * A).orderAt P :=
      (add_le_add_left (le_orderAt_mul G G P) _).trans (le_orderAt_mul _ A P)

variable [NoZeroDivisors R]

/-- A multiple point of `H G` on `H` is a zero of `G` or of the partial derivative `∂H/∂Xᵢ`. -/
theorem IsMultiplePoint.eval_eq_zero_or_eval_pderiv_eq_zero (h : IsMultiplePoint (H * G) P)
    (hH : eval P H = 0) (i : Fin 2) : eval P G = 0 ∨ eval P (pderiv i H) = 0 := by
  have := (isMultiplePoint_iff_eval_pderiv.1 h).2 i
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hH, zero_mul,
    zero_add] at this
  exact mul_eq_zero.1 this

end CommRing

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 2) k}

/-- Relatively prime plane polynomials have finitely many common zeros with coordinates in `k`. -/
private theorem finite_setOf_eval_eq_zero_of_isRelPrime {F G : MvPolynomial (Fin 2) k}
    (h : IsRelPrime F G) : {P : Fin 2 → k | eval P F = 0 ∧ eval P G = 0}.Finite := by
  refine (finite_zeroLocus_span_pair_of_isRelPrime h k).subset fun P hP ↦ ?_
  rw [mem_zeroLocus_iff]
  intro p hp
  obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.1 hp
  simp [hP.1, hP.2]

/-- The multiple points of `F` on an irreducible factor `H` are finitely many, over a perfect
field, if `H ^ 2 ∤ F`. -/
private theorem finite_setOf_isMultiplePoint_of_irreducible_dvd [PerfectField k]
    {H : MvPolynomial (Fin 2) k} (hH : Irreducible H) (hHF : H ∣ F) (hHF2 : ¬H * H ∣ F) :
    {P | eval P H = 0 ∧ IsMultiplePoint F P}.Finite := by
  obtain ⟨G, rfl⟩ := hHF
  obtain ⟨i, hi⟩ := hH.exists_pderiv_ne_zero
  have hG : IsRelPrime H G :=
    hH.isRelPrime_iff_not_dvd.2 fun hHG ↦ hHF2 (mul_dvd_mul_left H hHG)
  have hHi : IsRelPrime H (pderiv i H) :=
    hH.isRelPrime_iff_not_dvd.2 fun hd ↦ hi (pderiv_eq_zero_of_dvd hd)
  refine ((finite_setOf_eval_eq_zero_of_isRelPrime hG).union
    (finite_setOf_eval_eq_zero_of_isRelPrime hHi)).subset fun P hP ↦ ?_
  exact (hP.2.eval_eq_zero_or_eval_pderiv_eq_zero hP.1 i).imp (⟨hP.1, ·⟩) (⟨hP.1, ·⟩)

/-- Over a perfect field, a squarefree plane curve (one without multiple components, for
instance an irreducible one) has only finitely many multiple points. -/
theorem finite_setOf_isMultiplePoint_of_squarefree [PerfectField k] (hF : Squarefree F) :
    {P | IsMultiplePoint F P}.Finite := by
  classical
  have hF0 : F ≠ 0 := hF.ne_zero
  refine ((UniqueFactorizationMonoid.factors F).toFinset.finite_toSet.biUnion
    (t := fun H ↦ {P | eval P H = 0 ∧ IsMultiplePoint F P}) fun H hH ↦ ?_).subset fun P hP ↦ ?_
  · rw [Finset.mem_coe, Multiset.mem_toFinset] at hH
    have hHi := UniqueFactorizationMonoid.irreducible_of_factor H hH
    exact finite_setOf_isMultiplePoint_of_irreducible_dvd hHi
      (UniqueFactorizationMonoid.dvd_of_mem_factors hH)
      fun h ↦ hHi.not_isUnit (hF H h)
  · obtain ⟨q, hq, hqF, hqP⟩ := (RingHom.ker_isPrime (eval P)).exists_irreducible_dvd_mem hF0
      (RingHom.mem_ker.2 (IsMultiplePoint.eval_eq_zero hP))
    obtain ⟨H, hH, hqH⟩ := UniqueFactorizationMonoid.exists_mem_factors_of_dvd hF0 hq hqF
    obtain ⟨u, rfl⟩ := hqH
    refine Set.mem_biUnion (Multiset.mem_toFinset.2 hH) ⟨?_, hP⟩
    rw [RingHom.mem_ker] at hqP
    simp [hqP]

/-- **Finiteness of the multiple points of a reduced plane curve.** Let `k` be a perfect field
(for instance an algebraically closed one) and `F ∈ k[X, Y]`.

1. If `F` is irreducible, `F` has only finitely many multiple points.
2. More generally, the same holds if `F` is squarefree, that is, has no multiple components.
3. Conversely, if `G ^ 2 ∣ F`, then every zero of `G` is a multiple point of `F`.

Milestone: *Finiteness of the multiple points of a reduced plane curve*. -/
theorem finite_multiple_points [PerfectField k] :
    (Irreducible F → {P | IsMultiplePoint F P}.Finite) ∧
    (Squarefree F → {P | IsMultiplePoint F P}.Finite) ∧
    (∀ G : MvPolynomial (Fin 2) k, G ^ 2 ∣ F → ∀ P, eval P G = 0 → IsMultiplePoint F P) :=
  ⟨fun hF ↦ finite_setOf_isMultiplePoint_of_squarefree hF.squarefree,
    finite_setOf_isMultiplePoint_of_squarefree, fun _ hG _ hP ↦ IsMultiplePoint.of_sq_dvd hG hP⟩

/- Squarefreeness is needed: over an infinite field, `X ^ 2` is singular along the line
`X = 0`. -/
example [Infinite k] : {P | IsMultiplePoint (X 0 ^ 2 : MvPolynomial (Fin 2) k) P}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun t : k ↦ ![0, t]) ?_ fun t ↦ ?_
  · intro s t hst
    simpa using congrFun hst 1
  · exact IsMultiplePoint.of_sq_dvd dvd_rfl (by simp)

end PlaneCurves.Affine

end
