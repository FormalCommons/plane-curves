/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.RingTheory.MvPolynomial.BinaryForm.Ideal
public import PlaneCurves.RingTheory.MvPolynomial.LeadingForm
public import TauCeti.RingTheory.MvPolynomial.LocalOrder
import Mathlib.Tactic.LinearCombination

/-!
# Intersection numbers and multiplicities

The algebra behind Fulton's property (5) of the intersection number of affine plane curves,
`I(P, F ∩ G) ≥ m_P(F) m_P(G)`.

Let `F`, `G` be nonzero polynomials in `k[X, Y]`, `P` a point, `m`, `n` the orders of `F`, `G` at
`P`, and `I_P` the ideal of `P`. Lemma (b) of Fulton's proof says that the leading forms of `F`
and `G` at `P` are relatively prime exactly when `A F + B G ∈ I_P ^ (m + n)` forces
`A ∈ I_P ^ n` and `B ∈ I_P ^ m`; that is, when the map
`k[X, Y] ⧸ I_P ^ n × k[X, Y] ⧸ I_P ^ m → k[X, Y] ⧸ I_P ^ (m + n)`, `(A, B) ↦ A F + B G`, is
injective.

## Main results

* `PlaneCurves.Affine.mem_pow_of_isRelPrime_leadingFormAt`: if the leading forms are relatively
  prime and `A F + B G ∈ I_P ^ (m + n)`, then `A ∈ I_P ^ n` and `B ∈ I_P ^ m`.
* `PlaneCurves.Affine.exists_notMem_pow_of_not_isRelPrime_leadingFormAt`: if they are not, there
  are `A ∉ I_P ^ n` and `B` with `A F + B G ∈ I_P ^ (m + n)`.
* `PlaneCurves.Affine.isRelPrime_leadingFormAt_iff_forall_mem_pow`: the two together.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §3.3, p. 39
-/

public section

open MvPolynomial

namespace PlaneCurves.Affine

variable {k : Type*} [Field k] {F G : MvPolynomial (Fin 2) k} {P : Fin 2 → k}

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

end PlaneCurves.Affine

end
