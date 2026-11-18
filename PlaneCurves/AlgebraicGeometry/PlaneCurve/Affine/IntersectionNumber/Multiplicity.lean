/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.IntersectionNumber.Basic
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.Tangent
public import PlaneCurves.RingTheory.MvPolynomial.BinaryForm.Ideal
public import PlaneCurves.RingTheory.MvPolynomial.LeadingForm
public import TauCeti.RingTheory.MvPolynomial.LocalOrder
import PlaneCurves.RingTheory.MvPolynomial.PowIdealOfVars
import PlaneCurves.RingTheory.MvPolynomial.Taylor
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Tactic.LinearCombination

/-!
# Intersection numbers and multiplicities

The algebra behind Fulton's property (5) of the intersection number of affine plane curves,
`I(P, F ∩ G) ≥ m_P(F) m_P(G)`, done over any field and with "no common tangent" replaced by
"relatively prime leading forms".

Let `F`, `G` be nonzero polynomials in `k[X, Y]`, `P` a point, `m`, `n` the orders of `F`, `G` at
`P`, and `I_P` the ideal of `P`.

Lemma (a) of Fulton's proof: if the leading forms are relatively prime, then `I_P ^ t ⊆ (F, G)`
in the local ring `𝒪_P(𝔸²)` for every `t ≥ m + n - 1`. A polynomial `H` of order at least `t` at
`P` has degree-`t` Taylor component `C F_m + D G_n` for forms `C`, `D`, by the binary-form lemma,
so `H` is congruent to an element of `(F, G)` modulo `I_P ^ (t + 1)`. A large power of `I_P` lies
in `(F, G) 𝒪_P`, as `(F, G) 𝒪_P` is `𝔪`-primary, and descending induction concludes.

Lemma (b) of Fulton's proof: the leading forms of `F` and `G` at `P` are relatively prime exactly
when `A F + B G ∈ I_P ^ (m + n)` forces `A ∈ I_P ^ n` and `B ∈ I_P ^ m`; that is, when the map
`k[X, Y] ⧸ I_P ^ n × k[X, Y] ⧸ I_P ^ m → k[X, Y] ⧸ I_P ^ (m + n)`, `(A, B) ↦ A F + B G`, is
injective.

Property (5) itself follows Fulton's count. With `I = I_P` and `N = m + n`, the map
`ψ : k[X, Y] ⧸ I ^ n × k[X, Y] ⧸ I ^ m → k[X, Y] ⧸ I ^ N`, `(A, B) ↦ A F + B G`, has cokernel
`k[X, Y] ⧸ ((F, G) + I ^ N)`, whose dimension is therefore `m n + dim ker ψ`. This quotient is
`𝒪_P ⧸ ((F, G) + 𝔪 ^ N)`, a quotient of `𝒪_P ⧸ (F, G)`, so `I(P, F ∩ G) ≥ m n`. If the leading
forms are relatively prime, then `ψ` is injective by Lemma (b) and `𝔪 ^ N ⊆ (F, G)` by Lemma (a),
so equality holds; if not, `ψ` is not injective and the inequality is strict.

## Main results

* `PlaneCurves.Affine.intersectProperlyAt_of_isRelPrime_leadingFormAt`: curves with relatively
  prime leading forms at `P` intersect properly at `P`.
* `PlaneCurves.Affine.vanishingIdeal_pow_le_span_pair_sup`: in `k[X, Y]`,
  `I_P ^ t ⊆ (F, G) + I_P ^ (t + 1)` for `m, n ≤ t ≤ m + n - 1`.
* `PlaneCurves.Affine.maximalIdeal_pow_le_span_pair`: `𝔪_P ^ t ⊆ (F, G) 𝒪_P` for
  `t ≥ m + n - 1`.
* `PlaneCurves.Affine.mem_pow_of_isRelPrime_leadingFormAt`: if the leading forms are relatively
  prime and `A F + B G ∈ I_P ^ (m + n)`, then `A ∈ I_P ^ n` and `B ∈ I_P ^ m`.
* `PlaneCurves.Affine.exists_notMem_pow_of_not_isRelPrime_leadingFormAt`: if they are not, there
  are `A ∉ I_P ^ n` and `B` with `A F + B G ∈ I_P ^ (m + n)`.
* `PlaneCurves.Affine.isRelPrime_leadingFormAt_iff_forall_mem_pow`: the two together.
* `PlaneCurves.Affine.mul_le_finrank_quotient_span_pair_sup_pow`,
  `PlaneCurves.Affine.finrank_quotient_span_pair_sup_pow_eq_mul_iff`: Fulton's dimension count,
  `dim_k k[X, Y] ⧸ ((F, G) + I_P ^ (m + n)) ≥ m n`, with equality iff the leading forms are
  relatively prime.
* `PlaneCurves.Affine.mul_orderAt_le_intersectionNumber`: `I(P, F ∩ G) ≥ m_P(F) m_P(G)` for all
  `F`, `G`, over any field.
* `PlaneCurves.Affine.intersectionNumber_eq_mul_orderAt_iff`: for nonzero `F`, `G`, equality
  holds iff the leading forms are relatively prime.
* `PlaneCurves.Affine.intersectionNumber_eq_one_iff`: `I(P, F ∩ G) = 1` iff `P` is simple on both
  curves with different tangents.
* `PlaneCurves.Affine.isTangentAt_iff_orderAt_lt_intersectionNumber`: a line `L(X - P) = 0`
  through `P` is tangent to `F` at `P` iff `I(P, F ∩ L(X - P)) > m_P(F)`, over any field.
* `PlaneCurves.Affine.isRelPrime_leadingFormAt_iff_not_exists_isTangentAt`: over an algebraically
  closed field, relatively prime leading forms mean no common tangent.
* `PlaneCurves.Affine.mul_orderAt_le_intersectionNumber_and_eq_iff`: property (5), over an
  algebraically closed field.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §3.3, Property (5), pp. 37–39, and Problem 3.19,
  p. 40
-/

public section

open MvPolynomial IsLocalRing Ideal Module

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



/-- The order-theoretic core of Lemma (b): if the leading forms of `F` and `G` at `P` are
relatively prime and `A F + B G` has order at least `m + n` at `P`, then `A` has order at
least `n`. -/
private theorem le_orderAt_of_isRelPrime_leadingFormAt (hF : F ≠ 0)
    (hFG : IsRelPrime (F.leadingFormAt P) (G.leadingFormAt P)) {A B : MvPolynomial (Fin 2) k}
    (h : (((F.orderAt P).toNat + (G.orderAt P).toNat : ℕ) : ℕ∞) ≤ (A * F + B * G).orderAt P) :
    ((G.orderAt P).toNat : ℕ∞) ≤ A.orderAt P := by
  by_contra! hlt
  have hA : A ≠ 0 := by
    rintro rfl
    simp at hlt
  have hAfin : A.orderAt P ≠ ⊤ := orderAt_eq_top_iff.not.2 hA
  have hFfin : F.orderAt P ≠ ⊤ := orderAt_eq_top_iff.not.2 hF
  have hAF : (A * F).orderAt P < (A * F + B * G).orderAt P := by
    refine lt_of_lt_of_le ?_ h
    obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.1 hAfin
    obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.1 hFfin
    simp only [orderAt_mul, ← hr, ← hs, ENat.toNat_natCast] at hlt ⊢
    norm_cast at hlt ⊢
    omega
  have hLF := (orderAt_eq_and_leadingFormAt_eq_neg_of_orderAt_lt_orderAt_add hAF).2
  rw [leadingFormAt_mul, leadingFormAt_mul] at hLF
  -- `G_n` divides `A_r F_m`, hence `A_r`, which has smaller degree.
  have hdvd : G.leadingFormAt P ∣ A.leadingFormAt P :=
    hFG.symm.dvd_of_dvd_mul_right ⟨-B.leadingFormAt P, by linear_combination hLF⟩
  obtain ⟨c, hc⟩ := hdvd
  have hA₀ := leadingFormAt_ne_zero (a := P) hA
  have hdeg := (isHomogeneous_leadingFormAt A P).totalDegree hA₀
  rw [hc] at hA₀ hdeg
  rw [totalDegree_mul_of_isDomain (left_ne_zero_of_mul hA₀) (right_ne_zero_of_mul hA₀),
    (isHomogeneous_leadingFormAt G P).totalDegree (left_ne_zero_of_mul hA₀)] at hdeg
  rw [← ENat.natCast_toNat hAfin] at hlt
  norm_cast at hlt
  omega

/-- **Lemma (b) of Fulton's proof of property (5).** Let `F`, `G` be nonzero polynomials in
`k[X, Y]` with orders `m`, `n` at `P`, whose leading forms at `P` are relatively prime. If
`A F + B G ∈ I_P ^ (m + n)`, then `A ∈ I_P ^ n` and `B ∈ I_P ^ m`. -/
theorem mem_pow_of_isRelPrime_leadingFormAt (hF : F ≠ 0) (hG : G ≠ 0)
    (hFG : IsRelPrime (F.leadingFormAt P) (G.leadingFormAt P)) {A B : MvPolynomial (Fin 2) k}
    (h : A * F + B * G ∈ vanishingIdeal k {P} ^ ((F.orderAt P).toNat + (G.orderAt P).toNat)) :
    A ∈ vanishingIdeal k {P} ^ (G.orderAt P).toNat ∧
      B ∈ vanishingIdeal k {P} ^ (F.orderAt P).toNat := by
  simp only [mem_pow_vanishingIdeal_singleton_iff] at h ⊢
  have h' : (((G.orderAt P).toNat + (F.orderAt P).toNat : ℕ) : ℕ∞) ≤
      (B * G + A * F).orderAt P := by
    rwa [Nat.add_comm, add_comm (B * G)]
  exact ⟨le_orderAt_of_isRelPrime_leadingFormAt hF hFG h,
    le_orderAt_of_isRelPrime_leadingFormAt hG hFG.symm h'⟩

/-- A nonzero form that is not relatively prime to another form has positive degree. -/
private theorem one_le_of_not_isRelPrime {L M : MvPolynomial (Fin 2) k} {d : ℕ}
    (hL : L.IsHomogeneous d) (hL₀ : L ≠ 0) (hLM : ¬IsRelPrime L M) : 1 ≤ d := by
  by_contra! hd
  obtain rfl : d = 0 := by omega
  have h0 := hL.totalDegree hL₀
  rw [totalDegree_eq_zero_iff_eq_C] at h0
  have hc : L.coeff 0 ≠ 0 := fun h ↦ hL₀ (by rw [h0, h, C_0])
  apply hLM
  rw [h0]
  exact ((isUnit_iff_ne_zero.mpr hc).map C).isRelPrime_left

/-- **The converse of Lemma (b) of Fulton's proof of property (5).** Let `F`, `G` be nonzero
polynomials in `k[X, Y]` with orders `m`, `n` at `P`, whose leading forms at `P` are not
relatively prime. Then there are `A ∉ I_P ^ n` and `B` with `A F + B G ∈ I_P ^ (m + n)`. -/
theorem exists_notMem_pow_of_not_isRelPrime_leadingFormAt (hF : F ≠ 0) (hG : G ≠ 0)
    (hFG : ¬IsRelPrime (F.leadingFormAt P) (G.leadingFormAt P)) :
    ∃ A B : MvPolynomial (Fin 2) k, A ∉ vanishingIdeal k {P} ^ (G.orderAt P).toNat ∧
      A * F + B * G ∈ vanishingIdeal k {P} ^ ((F.orderAt P).toNat + (G.orderAt P).toNat) := by
  set m := (F.orderAt P).toNat
  set n := (G.orderAt P).toNat
  have hFm := isHomogeneous_leadingFormAt F P
  have hGn := isHomogeneous_leadingFormAt G P
  have hFm₀ := leadingFormAt_ne_zero (a := P) hF
  have hGn₀ := leadingFormAt_ne_zero (a := P) hG
  have hm := one_le_of_not_isRelPrime hFm hFm₀ hFG
  have hn := one_le_of_not_isRelPrime hGn hGn₀ (fun h ↦ hFG h.symm)
  obtain ⟨A', B', hA', hB', hB'₀, hAB⟩ :=
    hFm.exists_mul_eq_mul_of_not_isRelPrime hGn hFm₀ hGn₀ hFG
  -- Shift `B'` and `-A'` back from the origin to `P`.
  refine ⟨taylor (-P) B', taylor (-P) (-A'), ?_, ?_⟩
  · rw [mem_pow_vanishingIdeal_singleton_iff, orderAt_taylor, add_neg_cancel,
      hB'.orderAt_zero hB'₀]
    norm_cast
    omega
  · rw [mem_pow_vanishingIdeal_singleton_iff, show ∀ x : MvPolynomial (Fin 2) k,
      x.orderAt P = (taylor P x).orderAt 0 from fun x ↦ by rw [orderAt_taylor, zero_add]]
    have hsplit : taylor P (taylor (-P) B' * F + taylor (-P) (-A') * G) =
        B' * (taylor P F - F.leadingFormAt P) + -A' * (taylor P G - G.leadingFormAt P) := by
      simp only [map_add, map_mul, map_neg, taylor_taylor, add_neg_cancel, taylor_zero]
      linear_combination hAB
    rw [hsplit]
    refine le_trans ?_ (min_orderAt_le_orderAt_add _ _ 0)
    refine le_min ((le_orderAt_mul _ _ 0).trans' ?_) ((le_orderAt_mul _ _ 0).trans' ?_)
    · refine le_trans ?_ (add_le_add hB'.natCast_le_orderAt_zero
        (orderAt_taylor_sub_leadingFormAt F P))
      norm_cast
      omega
    · rw [orderAt_neg]
      refine le_trans ?_ (add_le_add hA'.natCast_le_orderAt_zero
        (orderAt_taylor_sub_leadingFormAt G P))
      norm_cast
      omega

/-- **Lemma (b) of Fulton's proof of property (5), with its converse.** For nonzero `F`, `G` in
`k[X, Y]` with orders `m`, `n` at `P`, the leading forms of `F` and `G` at `P` are relatively
prime if and only if `A F + B G ∈ I_P ^ (m + n)` implies `A ∈ I_P ^ n` and `B ∈ I_P ^ m`. -/
theorem isRelPrime_leadingFormAt_iff_forall_mem_pow (hF : F ≠ 0) (hG : G ≠ 0) :
    IsRelPrime (F.leadingFormAt P) (G.leadingFormAt P) ↔
      ∀ A B : MvPolynomial (Fin 2) k,
        A * F + B * G ∈ vanishingIdeal k {P} ^ ((F.orderAt P).toNat + (G.orderAt P).toNat) →
          A ∈ vanishingIdeal k {P} ^ (G.orderAt P).toNat ∧
            B ∈ vanishingIdeal k {P} ^ (F.orderAt P).toNat := by
  refine ⟨fun h A B ↦ mem_pow_of_isRelPrime_leadingFormAt hF hG h, fun h ↦ ?_⟩
  by_contra hFG
  obtain ⟨A, B, hA, hAB⟩ := exists_notMem_pow_of_not_isRelPrime_leadingFormAt hF hG hFG
  exact hA (h A B hAB).1

/-! ### Property (5) -/

private theorem choose_two_add (a b : ℕ) :
    (a + b + 1).choose 2 = (a + 1).choose 2 + (b + 1).choose 2 + a * b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [show a + (b + 1) + 1 = a + b + 1 + 1 by ring, Nat.choose_succ_succ' (a + b + 1) 1, ih,
      Nat.choose_succ_succ' (b + 1) 1, Nat.choose_one_right, Nat.choose_one_right]
    ring

variable (P) in
/-- Multiplication by `F ∈ I_P ^ m`, as a `k`-linear map `k[X, Y] ⧸ I_P ^ n → k[X, Y] ⧸ I_P ^ r`
for `r = m + n`. -/
private noncomputable def mulQuot (F : MvPolynomial (Fin 2) k) {m : ℕ}
    (hF : F ∈ vanishingIdeal k {P} ^ m) (n r : ℕ) (hr : m + n = r) :
    (MvPolynomial (Fin 2) k ⧸ vanishingIdeal k {P} ^ n) →ₗ[k]
      MvPolynomial (Fin 2) k ⧸ vanishingIdeal k {P} ^ r :=
  ((vanishingIdeal k {P} ^ n).mapQ (vanishingIdeal k {P} ^ r)
    (LinearMap.mulRight _ F) fun x hx ↦ by
      rw [Submodule.mem_comap, LinearMap.mulRight_apply, ← hr, pow_add]
      exact mul_comm F x ▸ Ideal.mul_mem_mul hF hx).restrictScalars k

private theorem mulQuot_mk {m : ℕ} (hF : F ∈ vanishingIdeal k {P} ^ m) (n r : ℕ)
    (hr : m + n = r) (A : MvPolynomial (Fin 2) k) :
    mulQuot P F hF n r hr (Ideal.Quotient.mk _ A) = Ideal.Quotient.mk _ (A * F) :=
  rfl

variable (P) in
/-- Fulton's map `ψ : k[X, Y] ⧸ I_P ^ n × k[X, Y] ⧸ I_P ^ m → k[X, Y] ⧸ I_P ^ (m + n)`,
`(A, B) ↦ A F + B G`, for `F ∈ I_P ^ m` and `G ∈ I_P ^ n`. -/
private noncomputable def mulAddMul {m n : ℕ} (hF : F ∈ vanishingIdeal k {P} ^ m)
    (hG : G ∈ vanishingIdeal k {P} ^ n) :
    (MvPolynomial (Fin 2) k ⧸ vanishingIdeal k {P} ^ n) ×
        (MvPolynomial (Fin 2) k ⧸ vanishingIdeal k {P} ^ m) →ₗ[k]
      MvPolynomial (Fin 2) k ⧸ vanishingIdeal k {P} ^ (m + n) :=
  (mulQuot P F hF n (m + n) rfl).coprod (mulQuot P G hG m (m + n) (add_comm n m))

private theorem mulAddMul_mk {m n : ℕ} (hF : F ∈ vanishingIdeal k {P} ^ m)
    (hG : G ∈ vanishingIdeal k {P} ^ n) (A B : MvPolynomial (Fin 2) k) :
    mulAddMul P hF hG (Ideal.Quotient.mk _ A, Ideal.Quotient.mk _ B) =
      Ideal.Quotient.mk _ (A * F + B * G) := by
  rw [map_add]
  rfl

private theorem range_mulAddMul {m n : ℕ} (hF : F ∈ vanishingIdeal k {P} ^ m)
    (hG : G ∈ vanishingIdeal k {P} ^ n) :
    LinearMap.range (mulAddMul P hF hG) =
      ((Ideal.span {F, G}).map (Ideal.Quotient.mk (vanishingIdeal k {P} ^ (m + n)))).restrictScalars
        k := by
  ext x
  rw [Submodule.restrictScalars_mem, Ideal.map_span, Set.image_pair, Ideal.mem_span_pair,
    LinearMap.mem_range]
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    obtain ⟨A, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨B, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨Ideal.Quotient.mk _ A, Ideal.Quotient.mk _ B, by rw [mulAddMul_mk]; simp⟩
  · rintro ⟨a, b, rfl⟩
    obtain ⟨A, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨B, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨(Ideal.Quotient.mk _ A, Ideal.Quotient.mk _ B), by rw [mulAddMul_mk]; simp⟩

private theorem injective_mulAddMul_iff {m n : ℕ} (hF : F ∈ vanishingIdeal k {P} ^ m)
    (hG : G ∈ vanishingIdeal k {P} ^ n) :
    Function.Injective (mulAddMul P hF hG) ↔ ∀ A B : MvPolynomial (Fin 2) k,
      A * F + B * G ∈ vanishingIdeal k {P} ^ (m + n) →
        A ∈ vanishingIdeal k {P} ^ n ∧ B ∈ vanishingIdeal k {P} ^ m := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  constructor
  · intro h A B hAB
    have := h (Ideal.Quotient.mk _ A, Ideal.Quotient.mk _ B)
      (by rw [mulAddMul_mk]; exact Ideal.Quotient.eq_zero_iff_mem.2 hAB)
    simp only [Prod.mk_eq_zero, Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  · rintro h ⟨a, b⟩ hab
    obtain ⟨A, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨B, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [mulAddMul_mk, Ideal.Quotient.eq_zero_iff_mem] at hab
    simp only [Prod.mk_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact h A B hab

private theorem finrank_quotient_pow (r : ℕ) :
    finrank k (MvPolynomial (Fin 2) k ⧸ vanishingIdeal k {P} ^ r) = (r + 1).choose 2 := by
  rw [finrank_quotient_pow_vanishingIdeal_singleton P (.inr inferInstance), Fintype.card_fin]
  rfl

private theorem finrank_quotient_span_pair_sup_pow_eq {m n : ℕ}
    (hF : F ∈ vanishingIdeal k {P} ^ m) (hG : G ∈ vanishingIdeal k {P} ^ n) :
    finrank k (MvPolynomial (Fin 2) k ⧸ Ideal.span {F, G} ⊔ vanishingIdeal k {P} ^ (m + n)) =
      m * n + finrank k (LinearMap.ker (mulAddMul P hF hG)) := by
  set J := Ideal.span {F, G}
  set I := vanishingIdeal k {P} ^ (m + n)
  have e : (MvPolynomial (Fin 2) k ⧸ J ⊔ I) ≃ₗ[k] _ ⧸ LinearMap.range (mulAddMul P hF hG) :=
    ((Ideal.quotientEquivAlgOfEq k (sup_comm J I)).trans
      (DoubleQuot.quotQuotEquivQuotSupₐ k I J).symm).toLinearEquiv.trans <|
    (Submodule.Quotient.restrictScalarsEquiv k (J.map (Ideal.Quotient.mkₐ k I))).symm.trans
      (Submodule.quotEquivOfEq _ _ (by exact (range_mulAddMul hF hG).symm))
  have h₁ := (LinearMap.range (mulAddMul P hF hG)).finrank_quotient_add_finrank
  have h₂ := LinearMap.finrank_range_add_finrank_ker (mulAddMul P hF hG)
  rw [Module.finrank_prod, finrank_quotient_pow, finrank_quotient_pow] at h₂
  rw [finrank_quotient_pow] at h₁
  have h₃ := choose_two_add m n
  rw [e.finrank_eq]
  linarith

/-- **Fulton's dimension count.** For `F ∈ I_P ^ m` and `G ∈ I_P ^ n`,
`dim_k k[X, Y] ⧸ ((F, G) + I_P ^ (m + n)) ≥ m n`. -/
theorem mul_le_finrank_quotient_span_pair_sup_pow {m n : ℕ}
    (hF : F ∈ vanishingIdeal k {P} ^ m) (hG : G ∈ vanishingIdeal k {P} ^ n) :
    m * n ≤
      finrank k (MvPolynomial (Fin 2) k ⧸ Ideal.span {F, G} ⊔ vanishingIdeal k {P} ^ (m + n)) := by
  rw [finrank_quotient_span_pair_sup_pow_eq hF hG]
  exact Nat.le_add_right _ _

/-- **Fulton's dimension count, the equality case.** For nonzero `F`, `G` with orders `m`, `n`
at `P`, `dim_k k[X, Y] ⧸ ((F, G) + I_P ^ (m + n)) = m n` iff the leading forms of `F` and `G` at
`P` are relatively prime. -/
theorem finrank_quotient_span_pair_sup_pow_eq_mul_iff (hF : F ≠ 0) (hG : G ≠ 0) :
    finrank k (MvPolynomial (Fin 2) k ⧸
        Ideal.span {F, G} ⊔ vanishingIdeal k {P} ^ ((F.orderAt P).toNat + (G.orderAt P).toNat)) =
      (F.orderAt P).toNat * (G.orderAt P).toNat ↔
      IsRelPrime (F.leadingFormAt P) (G.leadingFormAt P) := by
  have hFm := (mem_pow_vanishingIdeal_singleton_iff F P _).2 (ENat.natCast_toNat_le_self _)
  have hGn := (mem_pow_vanishingIdeal_singleton_iff G P _).2 (ENat.natCast_toNat_le_self _)
  rw [finrank_quotient_span_pair_sup_pow_eq hFm hGn, Nat.add_eq_left, Submodule.finrank_eq_zero,
    LinearMap.ker_eq_bot, injective_mulAddMul_iff,
    isRelPrime_leadingFormAt_iff_forall_mem_pow hF hG]

variable (P) in
/-- `dim_k k[X, Y] ⧸ ((F, G) + I_P ^ r) ≤ I(P, F ∩ G)`: the quotient is a quotient of
`𝒪_P(𝔸²) ⧸ (F, G)`, with equality when `𝔪_P ^ r ⊆ (F, G) 𝒪_P(𝔸²)`. -/
theorem finrank_quotient_span_pair_sup_pow_le_intersectionNumber (F G : MvPolynomial (Fin 2) k)
    (r : ℕ) :
    (finrank k (MvPolynomial (Fin 2) k ⧸ Ideal.span {F, G} ⊔ vanishingIdeal k {P} ^ r) : ℕ∞) ≤
      intersectionNumber P F G := by
  rw [← Module.length_eq_finrank, ← AffineSpace.localRing.length_quotient_map_sup_maximalIdeal_pow,
    intersectionNumber_eq_length_restrictScalars, Ideal.map_span, Set.image_pair]
  exact Module.length_le_of_surjective
    (Ideal.Quotient.factorₐ k le_sup_left).toLinearMap
    (Ideal.Quotient.factor_surjective le_sup_left)

/-- If `𝔪_P ^ r ⊆ (F, G) 𝒪_P(𝔸²)`, then `I(P, F ∩ G) = dim_k k[X, Y] ⧸ ((F, G) + I_P ^ r)`. -/
theorem finrank_quotient_span_pair_sup_pow_eq_intersectionNumber {r : ℕ}
    (h : maximalIdeal (AffineSpace.localRing k P) ^ r ≤
      Ideal.span {algebraMap _ (AffineSpace.localRing k P) F, algebraMap _ _ G}) :
    (finrank k (MvPolynomial (Fin 2) k ⧸ Ideal.span {F, G} ⊔ vanishingIdeal k {P} ^ r) : ℕ∞) =
      intersectionNumber P F G := by
  rw [← Module.length_eq_finrank, ← AffineSpace.localRing.length_quotient_map_sup_maximalIdeal_pow,
    intersectionNumber_eq_length_restrictScalars, Ideal.map_span, Set.image_pair, sup_eq_left.2 h]

/-- For nonzero `F`, `G`, `I(P, F ∩ G) ≥ m n` for the orders `m`, `n` at `P`, with equality iff
the leading forms are relatively prime. -/
private theorem mul_toNat_le_intersectionNumber_and_eq_iff (hF : F ≠ 0) (hG : G ≠ 0) :
    (((F.orderAt P).toNat * (G.orderAt P).toNat : ℕ) : ℕ∞) ≤ intersectionNumber P F G ∧
      (intersectionNumber P F G = ((F.orderAt P).toNat * (G.orderAt P).toNat : ℕ) ↔
        IsRelPrime (F.leadingFormAt P) (G.leadingFormAt P)) := by
  have hFm := (mem_pow_vanishingIdeal_singleton_iff F P _).2 (ENat.natCast_toNat_le_self _)
  have hGn := (mem_pow_vanishingIdeal_singleton_iff G P _).2 (ENat.natCast_toNat_le_self _)
  have hle := (Nat.cast_le.2 (mul_le_finrank_quotient_span_pair_sup_pow hFm hGn)).trans
    (finrank_quotient_span_pair_sup_pow_le_intersectionNumber P F G _)
  refine ⟨hle, fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← finrank_quotient_span_pair_sup_pow_eq_mul_iff hF hG]
    refine le_antisymm ?_ (mul_le_finrank_quotient_span_pair_sup_pow hFm hGn)
    exact_mod_cast h ▸ finrank_quotient_span_pair_sup_pow_le_intersectionNumber P F G _
  · rw [← finrank_quotient_span_pair_sup_pow_eq_intersectionNumber
      (maximalIdeal_pow_le_span_pair h le_self_add),
    (finrank_quotient_span_pair_sup_pow_eq_mul_iff hF hG).2 h]

private theorem orderAt_mul_orderAt_zero_left_le (G : MvPolynomial (Fin 2) k) :
    (0 : MvPolynomial (Fin 2) k).orderAt P * G.orderAt P ≤ intersectionNumber P 0 G := by
  by_cases hG : eval P G = 0
  · rw [intersectionNumber_zero_left_eq_top_iff.2 hG]
    exact le_top
  · rw [orderAt_eq_zero_iff.2 hG, mul_zero]
    exact zero_le

/-- **Intersection number and multiplicities.** `I(P, F ∩ G) ≥ m_P(F) m_P(G)`, over any field and
for all `F`, `G`. -/
theorem mul_orderAt_le_intersectionNumber (P : Fin 2 → k) (F G : MvPolynomial (Fin 2) k) :
    F.orderAt P * G.orderAt P ≤ intersectionNumber P F G := by
  rcases eq_or_ne F 0 with rfl | hF
  · exact orderAt_mul_orderAt_zero_left_le G
  rcases eq_or_ne G 0 with rfl | hG
  · rw [mul_comm, intersectionNumber_comm]
    exact orderAt_mul_orderAt_zero_left_le F
  rw [← ENat.natCast_toNat (orderAt_eq_top_iff.not.2 hF),
    ← ENat.natCast_toNat (orderAt_eq_top_iff.not.2 hG), ← Nat.cast_mul]
  exact (mul_toNat_le_intersectionNumber_and_eq_iff hF hG).1

/-- **The equality case of property (5)**, over any field: for nonzero `F` and `G`,
`I(P, F ∩ G) = m_P(F) m_P(G)` iff the leading forms of `F` and `G` at `P` are relatively
prime. -/
theorem intersectionNumber_eq_mul_orderAt_iff (hF : F ≠ 0) (hG : G ≠ 0) :
    intersectionNumber P F G = F.orderAt P * G.orderAt P ↔
      IsRelPrime (F.leadingFormAt P) (G.leadingFormAt P) := by
  rw [← ENat.natCast_toNat (orderAt_eq_top_iff.not.2 hF),
    ← ENat.natCast_toNat (orderAt_eq_top_iff.not.2 hG), ← Nat.cast_mul]
  exact (mul_toNat_le_intersectionNumber_and_eq_iff hF hG).2

/-- At simple points of `F` and `G`, the leading forms are relatively prime iff they are not
associated, that is, iff the tangents differ. -/
theorem IsSimplePoint.isRelPrime_leadingFormAt_iff (hF : IsSimplePoint F P)
    (hG : IsSimplePoint G P) :
    IsRelPrime (F.leadingFormAt P) (G.leadingFormAt P) ↔
      ¬Associated (F.leadingFormAt P) (G.leadingFormAt P) := by
  have hFi := hF.isTangentAt_leadingFormAt.prime.irreducible
  have hGi := hG.isTangentAt_leadingFormAt.prime.irreducible
  rw [hFi.isRelPrime_iff_not_dvd]
  exact not_congr ⟨fun h ↦ hFi.associated_of_dvd hGi h, Associated.dvd⟩

/-- **Transversal intersection.** `I(P, F ∩ G) = 1` iff `P` is a simple point of `F` and of `G`
and the tangents there differ, that is, the leading forms are not associated. -/
theorem intersectionNumber_eq_one_iff :
    intersectionNumber P F G = 1 ↔ IsSimplePoint F P ∧ IsSimplePoint G P ∧
      ¬Associated (F.leadingFormAt P) (G.leadingFormAt P) := by
  constructor
  · intro h
    have hprop : IntersectProperlyAt F G P := intersectionNumber_ne_top_iff.1 (by simp [h])
    have hP : eval P F = 0 ∧ eval P G = 0 := by
      have := mt intersectionNumber_eq_zero_iff.2 (by rw [h]; exact one_ne_zero)
      push Not at this
      exact this
    have hF := hprop.ne_zero_left hP.2
    have hG := hprop.ne_zero_right hP.1
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (orderAt_eq_top_iff.not.2 hF)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (orderAt_eq_top_iff.not.2 hG)
    have hm1 := orderAt_pos_iff.2 hP.1
    have hn1 := orderAt_pos_iff.2 hP.2
    have hle := mul_orderAt_le_intersectionNumber P F G
    rw [← hm, ← hn, h] at hle
    rw [← hm] at hm1
    rw [← hn] at hn1
    norm_cast at hm1 hn1 hle
    have hm' : m = 1 := by nlinarith
    have hn' : n = 1 := by nlinarith
    subst hm' hn'
    have hFs := isSimplePoint_iff_orderAt_eq_one.2 hm.symm
    have hGs := isSimplePoint_iff_orderAt_eq_one.2 hn.symm
    refine ⟨hFs, hGs, (hFs.isRelPrime_leadingFormAt_iff hGs).1 ?_⟩
    rw [← intersectionNumber_eq_mul_orderAt_iff hF hG, h, ← hm, ← hn]
    rfl
  · rintro ⟨hF, hG, h⟩
    rw [← (hF.isRelPrime_leadingFormAt_iff hG), ← intersectionNumber_eq_mul_orderAt_iff hF.ne_zero
      hG.ne_zero, isSimplePoint_iff_orderAt_eq_one.1 hF, isSimplePoint_iff_orderAt_eq_one.1 hG,
      mul_one] at h
    exact h

/-- **Tangency of a line detected by the intersection number** (Fulton, Problem 3.19). Let `F` be
a nonzero polynomial in `k[X, Y]`, `P ∈ k²`, and `L` a nonzero linear form, so that
`L(X - P) = 0` is a line through `P`. Then `L` is tangent to `F` at `P` iff
`I(P, F ∩ L(X - P)) > m_P(F)`. This covers the degenerate cases: if the line is a component of
`F`, then `I = ∞` and it is tangent; if `P ∉ F`, then `I = 0 = m_P(F)` and it is not.

Milestone: *Tangency of a line detected by the intersection number*. -/
theorem isTangentAt_iff_orderAt_lt_intersectionNumber {L : MvPolynomial (Fin 2) k} (hF : F ≠ 0)
    (hL : L.IsHomogeneous 1) (hL₀ : L ≠ 0) :
    IsTangentAt F P L ↔ F.orderAt P < intersectionNumber P F (taylor (-P) L) := by
  have hℓ : taylor (-P) L ≠ 0 := taylor_eq_zero.not.2 hL₀
  have hord : (taylor (-P) L).orderAt P = 1 := by
    rw [orderAt_taylor, add_neg_cancel, hL.orderAt_zero hL₀, Nat.cast_one]
  have hlead : (taylor (-P) L).leadingFormAt P = L := by
    rw [leadingFormAt_taylor, add_neg_cancel, hL.leadingFormAt_zero]
  have hle := mul_orderAt_le_intersectionNumber P F (taylor (-P) L)
  have heq := intersectionNumber_eq_mul_orderAt_iff (P := P) hF hℓ
  rw [hord, mul_one] at hle heq
  rw [hlead, isRelPrime_comm, (irreducible_of_isHomogeneous_one hL hL₀).isRelPrime_iff_not_dvd]
    at heq
  rw [hle.lt_iff_ne, ne_comm, Ne, heq, not_not, isTangentAt_def]
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨hL, hL₀, h⟩⟩

section IsAlgClosed

variable [IsAlgClosed k]

/-- Over an algebraically closed field, the leading forms of `F ≠ 0` and `G` at `P` are
relatively prime iff `F` and `G` have no common tangent at `P`. -/
theorem isRelPrime_leadingFormAt_iff_not_exists_isTangentAt (hF : F ≠ 0) :
    IsRelPrime (F.leadingFormAt P) (G.leadingFormAt P) ↔
      ¬∃ L, IsTangentAt F P L ∧ IsTangentAt G P L := by
  refine ⟨fun h ⟨L, hLF, hLG⟩ ↦ hLF.prime.not_isUnit (h hLF.dvd hLG.dvd), fun h ↦ ?_⟩
  refine WfDvdMonoid.isRelPrime_of_no_irreducible_factors
    (fun h0 ↦ leadingFormAt_ne_zero hF h0.1) fun p hp hpF hpG ↦ h ?_
  obtain ⟨ε, hε, u, -, hu, heq⟩ := exists_leadingFormAt_eq_C_mul_prod (P := P) hF
  rw [heq] at hpF
  rcases hp.prime.dvd_or_dvd hpF with hpε | hpu
  · exact (hp.not_isUnit (isUnit_of_dvd_unit hpε ((isUnit_iff_ne_zero.2 hε).map C))).elim
  obtain ⟨L, hL, hpL⟩ := hp.prime.exists_mem_multiset_dvd hpu
  have hLp := (hp.associated_of_dvd (hu L hL).prime.irreducible hpL).symm.dvd
  exact ⟨L, hu L hL, isTangentAt_def.2 ⟨(hu L hL).isHomogeneous, (hu L hL).ne_zero, hLp.trans hpG⟩⟩

/-- **Intersection number is at least the product of the multiplicities** (Fulton's property
(5)). Let `k` be algebraically closed, `F`, `G` nonzero in `k[X, Y]` and `P ∈ k²`. Then
`I(P, F ∩ G) ≥ m_P(F) m_P(G)`, with equality iff `F` and `G` have no tangent line in common at
`P`.

Milestone: *Intersection number is at least the product of the multiplicities*. -/
theorem mul_orderAt_le_intersectionNumber_and_eq_iff (hF : F ≠ 0) (hG : G ≠ 0) :
    F.orderAt P * G.orderAt P ≤ intersectionNumber P F G ∧
      (intersectionNumber P F G = F.orderAt P * G.orderAt P ↔
        ¬∃ L, IsTangentAt F P L ∧ IsTangentAt G P L) :=
  ⟨mul_orderAt_le_intersectionNumber P F G, (intersectionNumber_eq_mul_orderAt_iff hF hG).trans
    (isRelPrime_leadingFormAt_iff_not_exists_isTangentAt hF)⟩

end IsAlgClosed

end PlaneCurves.Affine

end
