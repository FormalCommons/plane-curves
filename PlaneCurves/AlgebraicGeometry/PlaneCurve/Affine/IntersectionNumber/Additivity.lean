/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.IntersectionNumber.Basic

/-!
# Additivity of the local intersection number

Fulton's property (6) of the intersection number of affine plane curves:
`I(P, F ∩ G H) = I(P, F ∩ G) + I(P, F ∩ H)` in `ℕ∞`, over any field and for all polynomials.

## Main results

* `PlaneCurves.Affine.IntersectProperlyAt.mk_algebraMap_mem_nonZeroDivisors`: if `F` and `H`
  intersect properly at `P`, then `H` is a non-zero-divisor on `𝒪_P(𝔸²) ⧸ (F)`.
* `PlaneCurves.Affine.intersectionNumber_mul_right`,
  `PlaneCurves.Affine.intersectionNumber_mul_left`: property (6), in each argument.
* `PlaneCurves.Affine.intersectionNumber_prod_pow_prod_pow`: for `F = ∏ Fᵢ ^ rᵢ` and
  `G = ∏ Gⱼ ^ sⱼ`, `I(P, F ∩ G) = ∑ᵢ ∑ⱼ rᵢ sⱼ I(P, Fᵢ ∩ Gⱼ)`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §3.3
-/

public section

open MvPolynomial IsLocalRing Ideal

namespace PlaneCurves.Affine

variable {k : Type*} [Field k] {F G H : MvPolynomial (Fin 2) k} {P : Fin 2 → k}

/-- If `F` and `H` intersect properly at `P`, then the image of `H` is a non-zero-divisor on
`𝒪_P(𝔸²) ⧸ (F)`. -/
theorem IntersectProperlyAt.mk_algebraMap_mem_nonZeroDivisors (h : IntersectProperlyAt F H P) :
    Ideal.Quotient.mk (Ideal.span {algebraMap _ (AffineSpace.localRing k P) F})
        (algebraMap _ _ H) ∈
      nonZeroDivisors (AffineSpace.localRing k P ⧸
        Ideal.span {algebraMap _ (AffineSpace.localRing k P) F}) := by
  set 𝒪 := AffineSpace.localRing k P
  set S := (vanishingIdeal k {P} : Ideal (MvPolynomial (Fin 2) k)).primeCompl
  by_cases hHP : eval P H ≠ 0
  · exact ((AffineSpace.localRing.isUnit_algebraMap_iff.2 hHP).map _).mem_nonZeroDivisors
  push Not at hHP
  obtain ⟨F', U, rfl, hU, hF'⟩ := exists_eq_mul_eval_ne_zero P (h.ne_zero_left hHP)
  have hUS : U ∈ S := by simpa [S, mem_primeCompl_iff, mem_vanishingIdeal_singleton_iff] using hU
  refine (mem_nonZeroDivisors_iff_right (M₀ := 𝒪 ⧸ Ideal.span {algebraMap _ 𝒪 (F' * U)})).2 ?_
  intro y hy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hy
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  obtain ⟨⟨p, s⟩, rfl⟩ := IsLocalization.mk'_surjective S a
  obtain ⟨b, hb⟩ := hy
  obtain ⟨⟨q, t⟩, rfl⟩ := IsLocalization.mk'_surjective S b
  rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mul_mk'_eq_mk'_of_mul,
    IsLocalization.mk'_eq_iff_eq] at hb
  have hpoly := AffineSpace.localRing.algebraMap_injective k P hb
  have hdvd : F' ∣ p * (H * t) := ⟨U * q * s, by linear_combination hpoly⟩
  have hrel : IsRelPrime F' (H * t) := by
    refine WfDvdMonoid.isRelPrime_of_no_irreducible_factors
      (fun h0 => (h.ne_zero_left hHP) (by rw [h0.1, zero_mul])) fun D hD h1 h2 => ?_
    rcases hD.prime.dvd_or_dvd h2 with h2 | h2
    · exact intersectProperlyAt_def.1 h D hD (h1.mul_right U) h2 (hF' D hD h1)
    · obtain ⟨c, hc⟩ := h2
      have ht := AffineSpace.localRing.eval_ne_zero t
      rw [hc, map_mul, hF' D hD h1, zero_mul] at ht
      exact ht rfl
  obtain ⟨r, rfl⟩ := hrel.dvd_of_dvd_mul_right hdvd
  refine ⟨IsLocalization.mk' 𝒪 r (s * ⟨U, hUS⟩), ?_⟩
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq]
  congr 1
  simp only [Submonoid.coe_mul]
  ring

variable (P) in
/-- A unit curve meets nothing: `I(P, F ∩ 1) = 0`. -/
@[simp]
theorem intersectionNumber_one_right (F : MvPolynomial (Fin 2) k) :
    intersectionNumber P F 1 = 0 :=
  intersectionNumber_eq_zero_of_eval_ne_zero_right (by simp)

variable (P) in
/-- `I(P, 1 ∩ G) = 0`. -/
@[simp]
theorem intersectionNumber_one_left (G : MvPolynomial (Fin 2) k) :
    intersectionNumber P 1 G = 0 :=
  intersectionNumber_eq_zero_of_eval_ne_zero_left (by simp)

/-- **Additivity of local intersection numbers** (Fulton, §3.3, property (6)). Over any field
`k`, for all `F, G, H ∈ k[X, Y]` and `P ∈ k²`, `I(P, F ∩ G H) = I(P, F ∩ G) + I(P, F ∩ H)` in
`ℕ∞`. With `intersectionNumber_mul_left` it gives the factorized form
`intersectionNumber_prod_pow_prod_pow`: if `F = ∏ Fᵢ ^ rᵢ` and `G = ∏ Gⱼ ^ sⱼ`, then
`I(P, F ∩ G) = ∑ᵢ ∑ⱼ rᵢ sⱼ I(P, Fᵢ ∩ Gⱼ)`.

Milestone: *Additivity of local intersection numbers*. -/
theorem intersectionNumber_mul_right (P : Fin 2 → k) (F G H : MvPolynomial (Fin 2) k) :
    intersectionNumber P F (G * H) = intersectionNumber P F G + intersectionNumber P F H := by
  by_cases hG : IntersectProperlyAt F G P
  · by_cases hH : IntersectProperlyAt F H P
    · rw [intersectionNumber_def, map_mul,
        TauCeti.length_quotient_span_pair_mul_eq_add_of_mem_nonZeroDivisors
          hH.mk_algebraMap_mem_nonZeroDivisors]
      simp only [intersectionNumber_def]
    · rw [intersectionNumber_eq_top_iff.2 hH, intersectionNumber_eq_top_iff.2
        fun h => hH (intersectProperlyAt_mul_right_iff.1 h).2, add_top]
  · rw [intersectionNumber_eq_top_iff.2 hG, intersectionNumber_eq_top_iff.2
      fun h => hG (intersectProperlyAt_mul_right_iff.1 h).1, top_add]

/-- **Property (6)** in the first argument: `I(P, F G ∩ H) = I(P, F ∩ H) + I(P, G ∩ H)`. -/
theorem intersectionNumber_mul_left (P : Fin 2 → k) (F G H : MvPolynomial (Fin 2) k) :
    intersectionNumber P (F * G) H = intersectionNumber P F H + intersectionNumber P G H := by
  simp only [intersectionNumber_comm P _ H, intersectionNumber_mul_right]

/-- `I(P, F ∩ Gⁿ) = n I(P, F ∩ G)`. -/
theorem intersectionNumber_pow_right (P : Fin 2 → k) (F G : MvPolynomial (Fin 2) k) (n : ℕ) :
    intersectionNumber P F (G ^ n) = n * intersectionNumber P F G := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, intersectionNumber_mul_right, ih, Nat.cast_succ, add_one_mul]

/-- `I(P, Fⁿ ∩ G) = n I(P, F ∩ G)`. -/
theorem intersectionNumber_pow_left (P : Fin 2 → k) (F G : MvPolynomial (Fin 2) k) (n : ℕ) :
    intersectionNumber P (F ^ n) G = n * intersectionNumber P F G := by
  rw [intersectionNumber_comm, intersectionNumber_pow_right, intersectionNumber_comm]

/-- `I(P, F ∩ ∏ᵢ Gᵢ) = ∑ᵢ I(P, F ∩ Gᵢ)`. -/
theorem intersectionNumber_prod_right {ι : Type*} (P : Fin 2 → k) (F : MvPolynomial (Fin 2) k)
    (s : Finset ι) (G : ι → MvPolynomial (Fin 2) k) :
    intersectionNumber P F (∏ i ∈ s, G i) = ∑ i ∈ s, intersectionNumber P F (G i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih => rw [Finset.prod_cons, Finset.sum_cons, intersectionNumber_mul_right, ih]

/-- `I(P, ∏ᵢ Fᵢ ∩ G) = ∑ᵢ I(P, Fᵢ ∩ G)`. -/
theorem intersectionNumber_prod_left {ι : Type*} (P : Fin 2 → k) (s : Finset ι)
    (F : ι → MvPolynomial (Fin 2) k) (G : MvPolynomial (Fin 2) k) :
    intersectionNumber P (∏ i ∈ s, F i) G = ∑ i ∈ s, intersectionNumber P (F i) G := by
  simp only [intersectionNumber_comm P _ G, intersectionNumber_prod_right]

/-- The intersection number of two factorized curves: if `F = ∏ Fᵢ ^ rᵢ` and `G = ∏ Gⱼ ^ sⱼ`,
then `I(P, F ∩ G) = ∑ᵢ ∑ⱼ rᵢ sⱼ I(P, Fᵢ ∩ Gⱼ)`. -/
theorem intersectionNumber_prod_pow_prod_pow {ι κ : Type*} (P : Fin 2 → k) (s : Finset ι)
    (t : Finset κ) (F : ι → MvPolynomial (Fin 2) k) (G : κ → MvPolynomial (Fin 2) k)
    (r : ι → ℕ) (e : κ → ℕ) :
    intersectionNumber P (∏ i ∈ s, F i ^ r i) (∏ j ∈ t, G j ^ e j) =
      ∑ i ∈ s, ∑ j ∈ t, (r i * e j : ℕ∞) * intersectionNumber P (F i) (G j) := by
  simp only [intersectionNumber_prod_left, intersectionNumber_prod_right,
    intersectionNumber_pow_left, intersectionNumber_pow_right, Finset.mul_sum, mul_assoc,
    mul_left_comm (e _ : ℕ∞)]
  exact Finset.sum_comm

end PlaneCurves.Affine

end
