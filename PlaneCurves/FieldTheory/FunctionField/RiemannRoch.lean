/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Consequences.Clifford
public import TauCeti.FieldTheory.FunctionField.Consequences.HighDegree
public import TauCeti.FieldTheory.FunctionField.Differential.CanonicalDivisor
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Genus

/-!
# Corollaries of Riemann's theorem and Noether's reduction lemma

Let `K / k` be an algebraic function field of one variable, `g` its genus and `ℓ(D)` the
dimension of the Riemann–Roch space of a divisor `D`. Tau Ceti proves Riemann's theorem
`ℓ(D) ≥ deg D + 1 - g` (`TauCeti.Divisor.degree_add_one_sub_genus_le_dim`), its Corollary 3,
equality in large degree (`TauCeti.exists_forall_dim_eq_degree_add_one_sub_genus`), and the
Riemann–Roch theorem. This file adds Corollaries 1 and 2 of Riemann's theorem and Noether's
reduction lemma, in the form of Fulton's §8.3 and §8.6, and the corollaries of the Riemann–Roch
theorem that Tau Ceti does not state.

The reduction lemma is proved by the short route through the Riemann–Roch theorem: for a place `P`
of degree one, `ℓ(D + P) - ℓ(D) = 1 + ℓ(W - D - P) - ℓ(W - D)`, and the last difference is `0`
or `-1`. The book's hypothesis `ℓ(D) > 0` is not needed. Over an algebraically closed field every
place has degree one (`TauCeti.Place.degree_eq_one_of_isAlgClosed_of_isFunctionField`).

## Main results

* `TauCeti.isLeast_genus`: **Riemann's theorem**, the genus is the least integer `g` with
  `ℓ(D) ≥ deg D + 1 - g` for every divisor `D`.
* `TauCeti.Divisor.dim_eq_degree_add_one_sub_genus_of_le`: Corollary 1 to Riemann's theorem, if
  `ℓ(D₀) = deg D₀ + 1 - g` and `D ≡ D' ≥ D₀` then `ℓ(D) = deg D + 1 - g`.
* `TauCeti.exists_forall_genus_eq_degree_zsmul_zeros_sub_dim_add_one`: Corollary 2 to Riemann's
  theorem, `g = deg (r (x)₀) - ℓ(r (x)₀) + 1` for all large `r`.
* `TauCeti.Divisor.IsRiemannRochDivisor.dim_add_ofPoint_eq`: the reduction lemma for any divisor
  `W` satisfying the Riemann–Roch identity.
* `TauCeti.Divisor.dim_add_ofPoint_eq_of_divisorClass_eq_canonicalClass`: **Noether's reduction
  lemma**, for `W` in the canonical class.
* `TauCeti.Divisor.dim_sub_ofPoint_add_one`: Corollary 3 to the Riemann–Roch theorem,
  `ℓ(D - P) = ℓ(D) - 1` if `deg D ≥ 2g`.
* `TauCeti.Divisor.IsRiemannRochDivisor.two_mul_dim_le_degree_add_two`: **Clifford's theorem**
  in the book's form, `2 ℓ(D) ≤ deg D + 2` if `ℓ(D) > 0` and `ℓ(W - D) > 0`.
* `TauCeti.Divisor.IsRiemannRochDivisor.two_mul_dim_sub_dim_eq`: if `D + D' = W`, then
  `2 (ℓ(D) - ℓ(D')) = deg D - deg D'`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §8.3 and §8.6
* [H. Stichtenoth, *Algebraic Function Fields and Codes*][Stichtenoth2009], §1.4 and §1.5
-/

public section

open scoped IntermediateField

namespace TauCeti

open AlgebraicGeometry

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-! ### Riemann's theorem and its corollaries -/

/-- **Riemann's theorem** (Fulton, §8.3): when `k` is algebraically closed in `K`, the genus is the
least integer `g` with `ℓ(D) ≥ deg D + 1 - g` for every divisor `D`. That it is such an integer is
`TauCeti.Divisor.degree_add_one_sub_genus_le_dim`, and that it is the least one follows from
`TauCeti.exists_degree_add_one_sub_dim_eq_genus`. Corollary 1 is
`TauCeti.Divisor.dim_eq_degree_add_one_sub_genus_of_le`, Corollary 2 is
`TauCeti.exists_forall_genus_eq_degree_zsmul_zeros_sub_dim_add_one`, Corollary 3 is
`TauCeti.exists_forall_dim_eq_degree_add_one_sub_genus`, and the genus depends only on `K`
by `TauCeti.genus_eq_of_ringEquiv`.

Milestone: *Riemann's theorem on the nonsingular model of a plane curve*. -/
theorem isLeast_genus (hK : IsFunctionField k K) (hex : IsIntegrallyClosedIn k K) :
    IsLeast {g : ℤ | ∀ D : Divisor k K, Divisor.degree D + 1 - g ≤ Divisor.dim D}
      (genus k K : ℤ) := by
  refine ⟨Divisor.degree_add_one_sub_genus_le_dim hK, fun g hg ↦ ?_⟩
  obtain ⟨A, hA⟩ := exists_degree_add_one_sub_dim_eq_genus hK hex
  have := hg A
  omega

/-- **Corollary 1 to Riemann's theorem** (Fulton, §8.3): if `ℓ(D₀) = deg D₀ + 1 - g`, then
`ℓ(D) = deg D + 1 - g` for every divisor `D` linearly equivalent to a divisor `D' ≥ D₀`. -/
theorem Divisor.dim_eq_degree_add_one_sub_genus_of_le (hK : IsFunctionField k K)
    {D₀ D D' : Divisor k K}
    (hD₀ : (Divisor.dim D₀ : ℤ) = Divisor.degree D₀ + 1 - genus k K)
    (hDD' : (Place.orderSystem hK).LinearlyEquivalent D D') (hle : D₀ ≤ D') :
    (Divisor.dim D : ℤ) = Divisor.degree D + 1 - genus k K := by
  rw [Divisor.dim_eq_of_linearlyEquivalent hK hDD', Divisor.degree_eq_of_linearlyEquivalent hK hDD']
  have := Divisor.dim_le_dim_add_degree_sub hK hle
  have := Divisor.degree_add_one_sub_genus_le_dim hK D'
  omega

/-- **Corollary 2 to Riemann's theorem** (Fulton, §8.3): for a transcendental `x`, the genus is
`deg (r (x)₀) - ℓ(r (x)₀) + 1` for all large `r`, where `(x)₀` is the divisor of zeros of `x`.
When `k` is algebraically closed in `K`, the transcendental elements are those not in `k`. -/
theorem exists_forall_genus_eq_degree_zsmul_zeros_sub_dim_add_one (hK : IsFunctionField k K)
    (hex : IsIntegrallyClosedIn k K) {x : Kˣ} (hx : Transcendental k (x : K)) :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r →
      (genus k K : ℤ) = Divisor.degree ((r : ℤ) • Divisor.zeros hK x) -
        Divisor.dim ((r : ℤ) • Divisor.zeros hK x) + 1 := by
  obtain ⟨c, hc⟩ := exists_forall_dim_eq_degree_add_one_sub_genus hK hex
  have := hK.finiteDimensional_adjoin hx
  have hn : 0 < Module.finrank k⟮(x : K)⟯ K := Module.finrank_pos
  refine ⟨c.toNat, fun r hr ↦ ?_⟩
  have hdeg : Divisor.degree ((r : ℤ) • Divisor.zeros hK x) =
      r * Module.finrank k⟮(x : K)⟯ K := by
    rw [Divisor.degree_zsmul, Divisor.degree_zeros hK x hx]
  have h := hc ((r : ℤ) • Divisor.zeros hK x) (by
    rw [hdeg]
    have : (r : ℤ) ≤ r * Module.finrank k⟮(x : K)⟯ K :=
      le_mul_of_one_le_right (by positivity) (by exact_mod_cast hn)
    omega)
  omega

/-! ### Noether's reduction lemma -/

/-- **The reduction lemma for a Riemann–Roch divisor**: if `W` satisfies the Riemann–Roch identity
`ℓ(E) = deg E + 1 - g₀ + ℓ(W - E)` for every divisor `E`, `P` is a place of degree one and
`ℓ(W - D - P) ≠ ℓ(W - D)`, then `ℓ(D + P) = ℓ(D)`. -/
theorem Divisor.IsRiemannRochDivisor.dim_add_ofPoint_eq (hK : IsFunctionField k K)
    {W : Divisor k K} {g₀ : ℕ} (hW : W.IsRiemannRochDivisor g₀) (D : Divisor k K)
    {P : Place k K} (hP : P.degree = 1)
    (h : Divisor.dim (W - D - WeilDivisor.ofPoint P) ≠ Divisor.dim (W - D)) :
    Divisor.dim (D + WeilDivisor.ofPoint P) = Divisor.dim D := by
  have hD := Divisor.isRiemannRochDivisor_iff.mp hW D
  have hDP := Divisor.isRiemannRochDivisor_iff.mp hW (D + WeilDivisor.ofPoint P)
  rw [Divisor.degree_add, Divisor.degree_ofPoint, hP, ← sub_sub] at hDP
  have hle : Divisor.dim (W - D - WeilDivisor.ofPoint P) ≤ Divisor.dim (W - D) :=
    Divisor.dim_mono hK (sub_le_self _ (WeilDivisor.ofPoint_nonneg P))
  have hge := finrank_riemannRochSpace_add_ofPoint_le hK (W - D - WeilDivisor.ofPoint P) P
    (finiteDimensional_riemannRochSpace hK _)
  rw [sub_add_cancel, hP] at hge
  simp only [← Divisor.dim_def] at hge
  omega

/-- **Noether's reduction lemma** (Fulton, §8.6): let `W` be a canonical divisor of a function
field `K / k` with `k` algebraically closed in `K`, `D` a divisor and `P` a place of degree one.
If `ℓ(W - D - P) ≠ ℓ(W - D)`, then `ℓ(D + P) = ℓ(D)`. The book's hypothesis `ℓ(D) > 0` is not
needed. Over an algebraically closed `k` every place has degree one
(`TauCeti.Place.degree_eq_one_of_isAlgClosed_of_isFunctionField`), and the canonical divisors in
the book's sense, the divisors of nonzero Kähler differentials, are those of the canonical class
(`PlaneCurves.divisorClass_eq_canonicalClass_iff_exists_kaehlerDifferentialDivisor_eq`).

Milestone: *Noether's reduction lemma*. -/
theorem Divisor.dim_add_ofPoint_eq_of_divisorClass_eq_canonicalClass (hK : IsFunctionField k K)
    (hex : IsIntegrallyClosedIn k K) {W : Divisor k K}
    (hW : (Place.orderSystem hK).divisorClass W = canonicalClass hK hex) (D : Divisor k K)
    {P : Place k K} (hP : P.degree = 1)
    (h : Divisor.dim (W - D - WeilDivisor.ofPoint P) ≠ Divisor.dim (W - D)) :
    Divisor.dim (D + WeilDivisor.ofPoint P) = Divisor.dim D :=
  (isRiemannRochDivisor_of_divisorClass_eq_canonicalClass hK hex hW).dim_add_ofPoint_eq hK D hP h

/-! ### Corollaries of the Riemann–Roch theorem -/

/-- **Corollary 3 to the Riemann–Roch theorem** (Fulton, §8.6): if `deg D ≥ 2g`, then
`ℓ(D - P) = ℓ(D) - 1` for every place `P` of degree one. -/
theorem Divisor.dim_sub_ofPoint_add_one (hK : IsFunctionField k K)
    (hex : IsIntegrallyClosedIn k K) {D : Divisor k K}
    (hD : 2 * (genus k K : ℤ) ≤ Divisor.degree D) {P : Place k K} (hP : P.degree = 1) :
    Divisor.dim (D - WeilDivisor.ofPoint P) + 1 = Divisor.dim D := by
  have h1 := Divisor.dim_eq_degree_add_one_sub_genus_of_two_mul_genus_sub_one_le_degree hK hex
    (D := D) (by omega)
  have hdeg : Divisor.degree (D - WeilDivisor.ofPoint P) = Divisor.degree D - 1 := by
    rw [Divisor.degree_sub, Divisor.degree_ofPoint, hP, Nat.cast_one]
  have h2 := Divisor.dim_eq_degree_add_one_sub_genus_of_two_mul_genus_sub_one_le_degree hK hex
    (D := D - WeilDivisor.ofPoint P) (by omega)
  omega

/-- **Clifford's theorem** (Fulton, §8.6, Corollary 4): if `W` is a Riemann–Roch divisor for the
genus, `ℓ(D) > 0` and `ℓ(W - D) > 0`, then `2 ℓ(D) ≤ deg D + 2`. -/
theorem Divisor.IsRiemannRochDivisor.two_mul_dim_le_degree_add_two (hK : IsFunctionField k K)
    (hex : IsIntegrallyClosedIn k K) {W : Divisor k K} (hW : W.IsRiemannRochDivisor (genus k K))
    {D : Divisor k K} (hD : 0 < Divisor.dim D) (hWD : 0 < Divisor.dim (W - D)) :
    2 * (Divisor.dim D : ℤ) ≤ Divisor.degree D + 2 := by
  have h0 : 0 ≤ Divisor.degree D :=
    not_lt.1 fun h ↦ hD.ne' (Divisor.dim_eq_zero_of_degree_neg hK h)
  have h1 : 0 ≤ Divisor.degree (W - D) :=
    not_lt.1 fun h ↦ hWD.ne' (Divisor.dim_eq_zero_of_degree_neg hK h)
  rw [Divisor.degree_sub, hW.degree_eq hK hex] at h1
  exact Divisor.two_mul_dim_le_degree_add_two hK hex h0 (by omega)

/-- **Problem 8.30 of Fulton**: if `W` is a Riemann–Roch divisor and `D + D' = W`, then
`2 (ℓ(D) - ℓ(D')) = deg D - deg D'`. -/
theorem Divisor.IsRiemannRochDivisor.two_mul_dim_sub_dim_eq {W : Divisor k K} {g₀ : ℕ}
    (hW : W.IsRiemannRochDivisor g₀) {D D' : Divisor k K} (h : D + D' = W) :
    2 * ((Divisor.dim D : ℤ) - Divisor.dim D') = Divisor.degree D - Divisor.degree D' := by
  have hD := Divisor.isRiemannRochDivisor_iff.mp hW D
  have hD' := Divisor.isRiemannRochDivisor_iff.mp hW D'
  rw [← h, add_sub_cancel_left] at hD
  rw [← h, add_sub_cancel_right] at hD'
  linear_combination hD - hD'
end TauCeti

end
