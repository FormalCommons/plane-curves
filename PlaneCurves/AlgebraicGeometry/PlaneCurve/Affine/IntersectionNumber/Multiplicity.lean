/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.IntersectionNumber.Basic
public import PlaneCurves.RingTheory.MvPolynomial.BinaryForm.Ideal
public import PlaneCurves.RingTheory.MvPolynomial.LeadingForm
import PlaneCurves.RingTheory.MvPolynomial.Taylor
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# Powers of the maximal ideal in the ideal of two curves

Let `F, G ∈ k[X, Y]` have orders `m` and `n` at `P`, and relatively prime leading forms there.
Then `I_P ^ t ⊆ (F, G)` in the local ring `𝒪_P(𝔸²)` for every `t ≥ m + n - 1`. This is Lemma (a)
in Fulton's proof of property (5) of intersection numbers, done over any field and with
"no common tangent" replaced by "relatively prime leading forms".

The proof: a polynomial `H` of order at least `t` at `P` has degree-`t` Taylor component
`C F_m + D G_n` for forms `C`, `D`, by the binary-form lemma, so `H` is congruent to an element
of `(F, G)` modulo `I_P ^ (t + 1)`. A large power of `I_P` lies in `(F, G) 𝒪_P`, as `(F, G) 𝒪_P` is
`𝔪`-primary, and descending induction concludes.

## Main results

* `PlaneCurves.Affine.intersectProperlyAt_of_isRelPrime_leadingFormAt`: curves with relatively
  prime leading forms at `P` intersect properly at `P`.
* `PlaneCurves.Affine.vanishingIdeal_pow_le_span_pair_sup`: in `k[X, Y]`,
  `I_P ^ t ⊆ (F, G) + I_P ^ (t + 1)` for `m, n ≤ t ≤ m + n - 1`.
* `PlaneCurves.Affine.maximalIdeal_pow_le_span_pair`: `𝔪_P ^ t ⊆ (F, G) 𝒪_P` for
  `t ≥ m + n - 1`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §3.3, p. 39
-/

public section

open MvPolynomial IsLocalRing Ideal

namespace PlaneCurves.Affine

variable {k : Type*} [Field k] {F G : MvPolynomial (Fin 2) k} {P : Fin 2 → k}

/-- Two curves whose leading forms at `P` are relatively prime intersect properly at `P`: a
common component through `P` would make its leading form, of positive degree, divide both. -/
theorem intersectProperlyAt_of_isRelPrime_leadingFormAt
    (h : IsRelPrime (F.leadingFormAt P) (G.leadingFormAt P)) : IntersectProperlyAt F G P := by
  rw [intersectProperlyAt_def]
  rintro H - ⟨F', rfl⟩ ⟨G', rfl⟩ hH
  rw [leadingFormAt_mul, leadingFormAt_mul] at h
  have hu := h (dvd_mul_right _ _) (dvd_mul_right _ _)
  exact (isUnit_leadingFormAt_iff.1 hu).ne_zero hH

/-- The Taylor components of `p * C` in degrees `i ≤ t`, for `C` a form of degree `t - m` and `p`
of order at least `m ≤ t`: they vanish for `i < t`, and the one of degree `t` is
`(p_m) * C`. -/
private theorem homogeneousComponent_taylor_mul {p C : MvPolynomial (Fin 2) k} {m t i : ℕ}
    (hC : C.IsHomogeneous (t - m)) (hm : m ≤ p.orderAt P) (hmt : m ≤ t) (hi : i ≤ t) :
    homogeneousComponent i (taylor P p * C) =
      if i = t then homogeneousComponent m (taylor P p) * C else 0 := by
  rw [hC.homogeneousComponent_mul_right]
  split_ifs with h₁ h₂ h₂
  · rw [show i - (t - m) = m by omega]
  · rw [homogeneousComponent_taylor_eq_zero_of_lt, zero_mul]
    exact lt_of_lt_of_le (by exact_mod_cast (by omega : i - (t - m) < m)) hm
  · omega
  · rfl

/-- If `F` and `G` have orders `m` and `n` at `P` and relatively prime leading forms there, every
polynomial of order at least `t` at `P`, for `m, n ≤ t` and `m + n ≤ t + 1`, is congruent modulo
`I_P ^ (t + 1)` to an element of `(F, G)`. -/
theorem vanishingIdeal_pow_le_span_pair_sup {t : ℕ}
    (hFG : IsRelPrime (F.leadingFormAt P) (G.leadingFormAt P)) (hm : (F.orderAt P).toNat ≤ t)
    (hn : (G.orderAt P).toNat ≤ t) (ht : (F.orderAt P).toNat + (G.orderAt P).toNat ≤ t + 1) :
    vanishingIdeal k {P} ^ t ≤ Ideal.span {F, G} ⊔ vanishingIdeal k {P} ^ (t + 1) := by
  intro H hH
  rw [mem_pow_vanishingIdeal_singleton_iff] at hH
  obtain ⟨C, D, hC, hD, hCD⟩ := IsHomogeneous.exists_eq_mul_add_mul_of_isRelPrime
    (isHomogeneous_leadingFormAt F P) (isHomogeneous_leadingFormAt G P) hFG
    (homogeneousComponent_isHomogeneous t (taylor P H)) ht
  obtain ⟨C', rfl⟩ := taylor_surjective P C
  obtain ⟨D', rfl⟩ := taylor_surjective P D
  have hR : (t + 1 : ℕ) ≤ (H - F * C' - G * D').orderAt P := by
    rw [le_orderAt_iff_homogeneousComponent]
    intro i hi
    rw [show taylor P (H - F * C' - G * D') =
        taylor P H - taylor P F * taylor P C' - taylor P G * taylor P D' by simp,
      map_sub, map_sub,
      homogeneousComponent_taylor_mul hC (ENat.natCast_toNat_le_self _) hm (by omega),
      homogeneousComponent_taylor_mul hD (ENat.natCast_toNat_le_self _) hn (by omega)]
    split_ifs with hit
    · subst hit
      rw [hCD, ← leadingFormAt_def, ← leadingFormAt_def]
      ring
    · rw [homogeneousComponent_taylor_eq_zero_of_lt
        (lt_of_lt_of_le (by exact_mod_cast (by omega : i < t)) hH)]
      simp
  have hspan : F * C' + G * D' ∈ Ideal.span {F, G} :=
    Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
  have : H = (F * C' + G * D') + (H - F * C' - G * D') := by ring
  rw [this]
  exact Submodule.add_mem_sup hspan ((mem_pow_vanishingIdeal_singleton_iff _ _ _).2 hR)

/-- **Powers of the maximal ideal in the ideal of two curves.** Let `F, G ∈ k[X, Y]` have orders
`m` and `n` at `P` and relatively prime leading forms there. Then for every `t ≥ m + n - 1`, the
power `𝔪_P ^ t` of the maximal ideal of `𝒪_P(𝔸²)` lies in the ideal `(F, G) 𝒪_P(𝔸²)`.

Over an algebraically closed field, relatively prime leading forms are the same as no common
tangent at `P`.

Milestone: *Powers of the maximal ideal in the ideal of two curves without common tangents*. -/
theorem maximalIdeal_pow_le_span_pair {t : ℕ}
    (hFG : IsRelPrime (F.leadingFormAt P) (G.leadingFormAt P))
    (ht : (F.orderAt P).toNat + (G.orderAt P).toNat ≤ t + 1) :
    maximalIdeal (AffineSpace.localRing k P) ^ t ≤
      Ideal.span {algebraMap _ (AffineSpace.localRing k P) F, algebraMap _ _ G} := by
  set 𝒪 := AffineSpace.localRing k P
  set J := Ideal.span {algebraMap _ 𝒪 F, algebraMap _ 𝒪 G}
  by_cases hF : eval P F = 0
  swap
  · rw [Ideal.eq_top_of_isUnit_mem J (Ideal.subset_span (Set.mem_insert _ _))
      (AffineSpace.localRing.isUnit_algebraMap_iff.2 hF)]
    exact le_top
  by_cases hG : eval P G = 0
  swap
  · rw [Ideal.eq_top_of_isUnit_mem J (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
      (AffineSpace.localRing.isUnit_algebraMap_iff.2 hG)]
    exact le_top
  have hprop := intersectProperlyAt_of_isRelPrime_leadingFormAt hFG
  -- Both orders are positive, so `m, n ≤ t`.
  have hpos {p : MvPolynomial (Fin 2) k} (hp : p ≠ 0) (hp0 : eval P p = 0) :
      1 ≤ (p.orderAt P).toNat := by
    have h1 := orderAt_pos_iff.2 hp0
    rw [← ENat.natCast_toNat (orderAt_eq_top_iff.not.2 hp)] at h1
    exact_mod_cast h1
  have hm := hpos (hprop.ne_zero_left hG) hF
  have hn := hpos (hprop.ne_zero_right hF) hG
  -- One step: `𝔪 ^ s ≤ J ⊔ 𝔪 ^ (s + 1)` for `s ≥ t`.
  have hstep (s : ℕ) (hs : t ≤ s) : maximalIdeal 𝒪 ^ s ≤ J ⊔ maximalIdeal 𝒪 ^ (s + 1) := by
    rw [← AffineSpace.localRing.map_vanishingIdeal_pow,
      ← AffineSpace.localRing.map_vanishingIdeal_pow,
      Ideal.map_le_iff_le_comap]
    refine (vanishingIdeal_pow_le_span_pair_sup hFG (by omega) (by omega) (by omega)).trans ?_
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_sup, Ideal.map_span, Set.image_pair]
  -- A large power of `𝔪` lies in `J`, which is `𝔪`-primary.
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg_radical
    (hprop.radical_span_eq_maximalIdeal hF hG).ge
    (by rw [hprop.radical_span_eq_maximalIdeal hF hG]; exact IsNoetherian.noetherian _)
  have key (d : ℕ) : ∀ s, t ≤ s → N ≤ s + d → maximalIdeal 𝒪 ^ s ≤ J := by
    induction d with
    | zero => exact fun s _ hs => (Ideal.pow_le_pow_right hs).trans hN
    | succ d ih =>
      exact fun s hs hsd => (hstep s hs).trans (sup_le le_rfl (ih (s + 1) (by omega) (by omega)))
  exact key N t le_rfl (by omega)

/-- **Powers of the ideal of a point in the ideal of two curves.** The form of
`maximalIdeal_pow_le_span_pair` with the ideal `I_P` of `P` extended to `𝒪_P(𝔸²)`. -/
theorem map_vanishingIdeal_pow_le_span_pair {t : ℕ}
    (hFG : IsRelPrime (F.leadingFormAt P) (G.leadingFormAt P))
    (ht : (F.orderAt P).toNat + (G.orderAt P).toNat ≤ t + 1) :
    (vanishingIdeal k {P}).map (algebraMap _ (AffineSpace.localRing k P)) ^ t ≤
      Ideal.span {algebraMap _ (AffineSpace.localRing k P) F, algebraMap _ _ G} := by
  rw [AffineSpace.localRing.map_vanishingIdeal]
  exact maximalIdeal_pow_le_span_pair hFG ht

end PlaneCurves.Affine

end
