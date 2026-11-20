/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal

/-!
# Radicals of principal ideals in unique factorization domains

In a unique factorization domain, the radical of a principal ideal `(a)`, `a ≠ 0`, is
determined by the irreducible factors of `a`, and it is `(b)` for every squarefree `b` with
the same irreducible factors. These statements need no `NormalizationMonoid`, unlike Mathlib's
`Ideal.radical_span_singleton_eq_span_radical`.

## Main results

* `UniqueFactorizationMonoid.exists_dvd_pow_iff`: `b ∣ aⁿ` for some `n` if and only if every
  irreducible factor of `b` divides `a`.
* `UniqueFactorizationMonoid.squarefree_prod_of_irreducible`: a product of pairwise
  non-associated irreducible elements is squarefree.
* `Squarefree.nodup_factors`, `Squarefree.not_dvd_of_mem_erase_factors`: conversely, the
  irreducible factors of a squarefree element are pairwise distinct, and none divides another.
* `Squarefree.pairwise_isRelPrime_toFinset_factors`, `Squarefree.associated_prod_toFinset_factors`:
  the distinct irreducible factors of a squarefree element are pairwise relatively prime, and their
  product is associated to it.
* `UniqueFactorizationMonoid.dvd_mul_prod_pow_iff`: the irreducible factors of `u ∏ fᵢ^{eᵢ}`.
* `Ideal.mem_radical_span_singleton_iff`, `Ideal.radical_span_singleton_eq_iff`,
  `Ideal.radical_span_singleton_eq_span`: the radical of a principal ideal.
* `Ideal.IsPrime.exists_irreducible_dvd_mem`: a prime ideal containing `a ≠ 0` contains an
  irreducible factor of `a`; `Ideal.IsPrime.eq_span_singleton_of_le`: a nonzero prime ideal inside
  `(p)`, `p` irreducible, is `(p)`.
-/

public section

open Ideal

namespace UniqueFactorizationMonoid

variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]

/-- In a unique factorization monoid, for `b ≠ 0`, some power of `a` is divisible by `b` if and
only if every irreducible factor of `b` divides `a`. -/
theorem exists_dvd_pow_iff {a b : R} (hb : b ≠ 0) :
    (∃ n, b ∣ a ^ n) ↔ ∀ p, Irreducible p → p ∣ b → p ∣ a := by
  refine ⟨fun ⟨n, hn⟩ p hp hpb => hp.prime.dvd_of_dvd_pow (hpb.trans hn), fun h => ?_⟩
  induction b using induction_on_prime with
  | h₁ => exact absurd rfl hb
  | h₂ x hx => exact ⟨0, by simpa using hx.dvd⟩
  | h₃ x p _ hp ih =>
    obtain ⟨n, hn⟩ := ih (right_ne_zero_of_mul hb) fun q hq hqx =>
      h q hq (dvd_mul_of_dvd_right hqx _)
    exact ⟨n + 1, pow_succ' a n ▸ mul_dvd_mul (h p hp.irreducible (dvd_mul_right _ _)) hn⟩

end UniqueFactorizationMonoid

namespace Ideal

variable {R : Type*} [CommSemiring R] [UniqueFactorizationMonoid R]

/-- In a unique factorization domain, for `b ≠ 0`, `a` lies in the radical of `(b)` if and only
if every irreducible factor of `b` divides `a`. -/
theorem mem_radical_span_singleton_iff {a b : R} (hb : b ≠ 0) :
    a ∈ (span {b}).radical ↔ ∀ p, Irreducible p → p ∣ b → p ∣ a := by
  simp_rw [mem_radical_iff, mem_span_singleton]
  exact UniqueFactorizationMonoid.exists_dvd_pow_iff hb

/-- In a unique factorization domain, the radicals of `(a)` and `(b)`, for `a, b ≠ 0`, agree if
and only if `a` and `b` have the same irreducible factors. -/
theorem radical_span_singleton_eq_iff {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    (span {a}).radical = (span {b}).radical ↔ ∀ p, Irreducible p → (p ∣ a ↔ p ∣ b) := by
  refine ⟨fun h p hp => ⟨fun hpa => ?_, fun hpb => ?_⟩, fun h => ?_⟩
  · exact (mem_radical_span_singleton_iff ha).1
      (h ▸ le_radical (mem_span_singleton_self b)) p hp hpa
  · exact (mem_radical_span_singleton_iff hb).1
      (h ▸ le_radical (mem_span_singleton_self a)) p hp hpb
  · ext x
    rw [mem_radical_span_singleton_iff ha, mem_radical_span_singleton_iff hb]
    exact forall_congr' fun p => imp_congr_right fun hp => imp_congr_left (h p hp)

/-- In a unique factorization domain, if `a ≠ 0` and `b` is squarefree with the same irreducible
factors as `a`, then the radical of `(a)` is `(b)`. -/
theorem radical_span_singleton_eq_span {a b : R} (ha : a ≠ 0) (hb : Squarefree b)
    (h : ∀ p, Irreducible p → (p ∣ a ↔ p ∣ b)) : (span {a}).radical = span {b} := by
  nontriviality R
  rw [(radical_span_singleton_eq_iff ha hb.ne_zero).2 h,
    (isRadical_iff_span_singleton.1 hb.isRadical).radical]

end Ideal

namespace UniqueFactorizationMonoid

variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]
variable {ι : Type*} {s : Finset ι} {f : ι → R}

/-- A product of pairwise non-associated irreducible elements is squarefree. -/
theorem squarefree_prod_of_irreducible (hf : ∀ i ∈ s, Irreducible (f i))
    (hs : (s : Set ι).Pairwise fun i j => ¬Associated (f i) (f j)) :
    Squarefree (∏ i ∈ s, f i) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun i hi j hj hij => ?_)
    fun i hi => (hf i hi).squarefree
  exact (hf i hi).isRelPrime_iff_not_dvd.2 fun hd => hs hi hj hij ((hf i hi).associated_of_dvd
    (hf j hj) hd)

/-- An irreducible `p` divides `u ∏ fᵢ^{eᵢ}`, for a unit `u` and exponents `eᵢ ≠ 0`, if and only
if it divides `∏ fᵢ`. -/
theorem dvd_mul_prod_pow_iff {u p : R} (hu : IsUnit u) (hp : Irreducible p) {e : ι → ℕ}
    (he : ∀ i ∈ s, e i ≠ 0) : p ∣ u * ∏ i ∈ s, f i ^ e i ↔ p ∣ ∏ i ∈ s, f i := by
  rw [hu.dvd_mul_left, hp.prime.dvd_finsetProd_iff, hp.prime.dvd_finsetProd_iff]
  exact exists_congr fun i => and_congr_right fun hi =>
    ⟨hp.prime.dvd_of_dvd_pow, fun h => h.trans (dvd_pow_self _ (he i hi))⟩

end UniqueFactorizationMonoid

namespace Squarefree

open UniqueFactorizationMonoid

variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]

/-- In the multiset of irreducible factors of a squarefree element `x`, no factor divides another
member of the multiset: otherwise the square of that factor would divide `x`. -/
theorem not_dvd_of_mem_erase_factors [DecidableEq R] {x p q : R} (hx : Squarefree x)
    (hp : p ∈ factors x) (hq : q ∈ (factors x).erase p) : ¬p ∣ q := by
  intro hpq
  have hdvd : p * p ∣ x := ((mul_dvd_mul_left p hpq).trans (by
    rw [← Multiset.prod_erase hp]
    exact mul_dvd_mul_left p (Multiset.dvd_prod hq))).trans
    (factors_prod (ne_zero_of_mem_factors hp)).dvd
  exact (irreducible_of_factor p hp).not_isUnit (hx p hdvd)

/-- The irreducible factors of a squarefree element are pairwise distinct. Unlike Mathlib's
`UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors`, this needs no
`NormalizationMonoid`. -/
theorem nodup_factors {x : R} (hx : Squarefree x) : (factors x).Nodup := by
  classical
  refine Multiset.nodup_iff_count_le_one.2 fun p ↦ ?_
  by_contra! h
  have hp : 0 < (factors x).count p := by omega
  have hp' : 0 < ((factors x).erase p).count p := by rw [Multiset.count_erase_self]; omega
  exact hx.not_dvd_of_mem_erase_factors (Multiset.count_pos.1 hp) (Multiset.count_pos.1 hp')
    dvd_rfl

/-- The distinct irreducible factors of a squarefree element are pairwise relatively prime. -/
theorem pairwise_isRelPrime_toFinset_factors [DecidableEq R] {x : R} (hx : Squarefree x) :
    ((factors x).toFinset : Set R).Pairwise IsRelPrime := by
  intro p hp q hq hpq
  rw [Finset.mem_coe, Multiset.mem_toFinset] at hp hq
  exact (irreducible_of_factor p hp).isRelPrime_iff_not_dvd.2 <|
    hx.not_dvd_of_mem_erase_factors hp ((Multiset.mem_erase_of_ne hpq.symm).2 hq)

/-- A squarefree element is associated to the product of its distinct irreducible factors. -/
theorem associated_prod_toFinset_factors [DecidableEq R] {x : R} (hx : Squarefree x) :
    Associated (∏ q ∈ (factors x).toFinset, q) x := by
  nontriviality R
  rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    Multiset.dedup_eq_self.2 hx.nodup_factors, Multiset.map_id']
  exact factors_prod hx.ne_zero

end Squarefree

namespace Ideal

variable {R : Type*} [CommSemiring R] [UniqueFactorizationMonoid R]

/-- In a unique factorization domain, a prime ideal that contains `a ≠ 0` contains an
irreducible factor of `a`. -/
theorem IsPrime.exists_irreducible_dvd_mem {P : Ideal R} (hP : P.IsPrime) {a : R} (ha : a ≠ 0)
    (haP : a ∈ P) : ∃ p, Irreducible p ∧ p ∣ a ∧ p ∈ P := by
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod ha
  have : (UniqueFactorizationMonoid.factors a).prod ∈ P := by
    have := P.mul_mem_right (↑u⁻¹ : R) haP
    rwa [← hu, mul_assoc, Units.mul_inv, mul_one] at this
  obtain ⟨p, hp, hpP⟩ := (hP.multiset_prod_mem_iff_exists_mem _).1 this
  exact ⟨p, UniqueFactorizationMonoid.irreducible_of_factor p hp,
    UniqueFactorizationMonoid.dvd_of_mem_factors hp, hpP⟩

/-- In a unique factorization domain, a nonzero prime ideal contained in the principal ideal of
an irreducible element `p` is `(p)`. -/
theorem IsPrime.eq_span_singleton_of_le {P : Ideal R} (hP : P.IsPrime) (hP0 : P ≠ ⊥) {p : R}
    (hp : Irreducible p) (h : P ≤ span {p}) : P = span {p} := by
  obtain ⟨q, hqP, hq⟩ := hP.exists_mem_prime_of_ne_bot hP0
  obtain ⟨c, hc⟩ := hp.dvd_symm (UniqueFactorizationMonoid.irreducible_iff_prime.2 hq)
    (mem_span_singleton.1 (h hqP))
  exact h.antisymm ((span_singleton_le_iff_mem P).2 (hc ▸ P.mul_mem_right c hqP))

end Ideal

end
