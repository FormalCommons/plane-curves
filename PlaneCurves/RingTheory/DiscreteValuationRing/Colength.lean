/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import PlaneCurves.RingTheory.LocalRing.Length

/-!
# Order equals colength in a discrete valuation ring

Let `R` be a discrete valuation ring with maximal ideal `𝔪` and uniformizer `t`, which is an
algebra over a field `k` such that `k → R/𝔪` is surjective (hence an isomorphism). This file
proves:

* `IsDiscreteValuationRing.existsUnique_sub_sum_mem_maximalIdeal_pow`: every `z ∈ R` has
  unique `λ₀, …, λₙ₋₁ ∈ k` with `z - (λ₀ + λ₁ t + ⋯ + λₙ₋₁ tⁿ⁻¹) ∈ 𝔪ⁿ = (tⁿ)`, the truncated
  expansion of `z` in `t`;
* `IsDiscreteValuationRing.finrank_pow_maximalIdeal_quotient` and
  `IsDiscreteValuationRing.finrank_quotient_pow_maximalIdeal`: `dim_k 𝔪ⁿ/𝔪ⁿ⁺¹ = 1` and
  `dim_k R/𝔪ⁿ = n`;
* `IsDiscreteValuationRing.addVal_eq_coe_iff_span_singleton_eq`: `ord z = n ↔ (z) = 𝔪ⁿ`;
* `IsDiscreteValuationRing.length_quotient_span_singleton_eq_addVal`: `ord z = dim_k R/(z)`,
  as an equality in `ℕ∞` that also holds for `z = 0`, where both sides are `⊤`;
* `IsDiscreteValuationRing.existsUnique_and_finrank_and_addVal_eq_length`: all of these
  together, with the unique `λ ∈ k` such that `z - λ ∈ 𝔪`.

Without the field `k`, the length forms `length_R R/𝔪ⁿ = n` and `length_R R/(z) = ord z` are
Mathlib's `IsDiscreteValuationRing.length_quotient_pow_maximalIdeal` and `Ring.ord_eq_addVal`.
This file passes from lengths over `R` to lengths over `k`, and finds the unique `λ ∈ k`, by
the results on local algebras in `PlaneCurves.RingTheory.LocalRing.Length`:
`IsLocalRing.length_eq_length_of_surjective_algebraMap_residueField` and
`IsLocalRing.existsUnique_sub_algebraMap_mem_maximalIdeal`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §2.5, Problem 2.30 and §2.10, Problem 2.50
-/

public section

open Ideal IsLocalRing

namespace IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- In a discrete valuation ring with uniformizer `t`, `x ∈ 𝔪ⁿ` if and only if `tⁿ ∣ x`. -/
theorem mem_maximalIdeal_pow_iff {t : R} (ht : Irreducible t) {n : ℕ} {x : R} :
    x ∈ IsLocalRing.maximalIdeal R ^ n ↔ t ^ n ∣ x := by
  rw [ht.maximalIdeal_eq, span_singleton_pow, mem_span_singleton]

/-- In a discrete valuation ring, `ord z = n` if and only if `(z) = 𝔪ⁿ`. -/
theorem addVal_eq_coe_iff_span_singleton_eq (z : R) (n : ℕ) :
    addVal R z = n ↔ span {z} = IsLocalRing.maximalIdeal R ^ n := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  rw [hϖ.maximalIdeal_eq, span_singleton_pow, span_singleton_eq_span_singleton,
    ← addVal_eq_iff_associated, addVal_pow, addVal_uniformizer hϖ, nsmul_one]

/-- In a discrete valuation ring, `𝔪ⁿ/𝔪ⁿ⁺¹` (written `𝔪ⁿ ⧸ 𝔪 • ⊤`, as in
`Ideal.quotEquivPowQuotPowSucc`) has length one. -/
theorem length_pow_maximalIdeal_quotient (n : ℕ) :
    Module.length R (↥(IsLocalRing.maximalIdeal R ^ n) ⧸
      (IsLocalRing.maximalIdeal R • ⊤ : Submodule R ↥(IsLocalRing.maximalIdeal R ^ n))) = 1 := by
  rw [← (quotEquivPowQuotPowSucc (IsPrincipalIdealRing.principal _) (not_a_field R)
    n).length_eq, ← pow_one (IsLocalRing.maximalIdeal R), length_quotient_pow_maximalIdeal,
    Nat.cast_one]

section Field

variable {k : Type*} [Field k] [Algebra k R]

/-- In a discrete valuation ring whose residue field is `k`, `dim_k 𝔪ⁿ/𝔪ⁿ⁺¹ = 1`. -/
theorem finrank_pow_maximalIdeal_quotient
    (h : Function.Surjective (algebraMap k (ResidueField R))) (n : ℕ) :
    Module.finrank k (↥(IsLocalRing.maximalIdeal R ^ n) ⧸
      (IsLocalRing.maximalIdeal R • ⊤ : Submodule R ↥(IsLocalRing.maximalIdeal R ^ n))) = 1 := by
  rw [Module.finrank_eq_toNat_length,
    length_eq_length_of_surjective_algebraMap_residueField _ h,
    length_pow_maximalIdeal_quotient]
  rfl

/-- In a discrete valuation ring whose residue field is `k`, `dim_k R/𝔪ⁿ = n`. -/
theorem finrank_quotient_pow_maximalIdeal
    (h : Function.Surjective (algebraMap k (ResidueField R))) (n : ℕ) :
    Module.finrank k (R ⧸ IsLocalRing.maximalIdeal R ^ n) = n := by
  rw [Module.finrank_eq_toNat_length,
    length_eq_length_of_surjective_algebraMap_residueField _ h,
    length_quotient_pow_maximalIdeal, ENat.toNat_natCast]

/-- **Order equals colength.** In a discrete valuation ring whose residue field is `k`, the
order of `z` is `dim_k R/(z)`: `ℓ_k(R/(z)) = ord z` in `ℕ∞`, both sides being `⊤` for `z = 0`. -/
theorem length_quotient_span_singleton_eq_addVal
    (h : Function.Surjective (algebraMap k (ResidueField R))) (z : R) :
    Module.length k (R ⧸ span {z}) = addVal R z := by
  rw [length_eq_length_of_surjective_algebraMap_residueField _ h, ← Ring.ord_eq_addVal]
  rfl

/-- In a discrete valuation ring whose residue field is `k`, a nonzero `z` has order
`dim_k R/(z)`. -/
theorem finrank_quotient_span_singleton
    (h : Function.Surjective (algebraMap k (ResidueField R))) {z : R} (hz : z ≠ 0) :
    (Module.finrank k (R ⧸ span {z}) : ℕ∞) = addVal R z := by
  rw [Module.finrank_eq_toNat_length, length_quotient_span_singleton_eq_addVal h,
    ENat.natCast_toNat (by simpa [addVal_eq_top_iff] using hz)]

/-- In a discrete valuation ring with uniformizer `t`, a sum `c₀ + c₁ t + ⋯ + cₙ₋₁ tⁿ⁻¹` with
coefficients in a field `k ⊆ R` lies in `𝔪ⁿ` if and only if all the coefficients are zero. -/
theorem sum_algebraMap_mul_pow_mem_maximalIdeal_pow_iff {t : R} (ht : Irreducible t) {n : ℕ}
    (c : Fin n → k) :
    ∑ i, algebraMap k R (c i) * t ^ (i : ℕ) ∈ IsLocalRing.maximalIdeal R ^ n ↔ c = 0 := by
  induction n with
  | zero => simp [Subsingleton.elim c 0]
  | succ n ih =>
    refine ⟨fun hc ↦ ?_, fun hc ↦ by simp [hc]⟩
    have hsum : ∑ i, algebraMap k R (c i) * t ^ (i : ℕ) =
        algebraMap k R (c 0) + t * ∑ i : Fin n, algebraMap k R (c i.succ) * t ^ (i : ℕ) := by
      rw [Fin.sum_univ_succ, Finset.mul_sum]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
      congr 1
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [hsum] at hc
    have ht_mem : t ∈ IsLocalRing.maximalIdeal R := by
      rw [ht.maximalIdeal_eq]; exact mem_span_singleton_self t
    have h0 : c 0 = 0 := by
      have := Ideal.pow_le_self n.succ_ne_zero hc
      rwa [Ideal.add_mem_iff_left _ (Ideal.mul_mem_right _ _ ht_mem),
        algebraMap_mem_maximalIdeal_iff] at this
    rw [h0, map_zero, zero_add, mem_maximalIdeal_pow_iff ht, pow_succ',
      mul_dvd_mul_iff_left ht.ne_zero, ← mem_maximalIdeal_pow_iff ht, ih] at hc
    ext i
    cases i using Fin.cases with
    | zero => exact h0
    | succ i => exact congr_fun hc i

/-- In a discrete valuation ring with uniformizer `t` whose residue field is `k`, every `z`
has a truncated expansion `z - (c₀ + c₁ t + ⋯ + cₙ₋₁ tⁿ⁻¹) ∈ 𝔪ⁿ` with coefficients in `k`. -/
theorem exists_sub_sum_mem_maximalIdeal_pow
    (h : Function.Surjective (algebraMap k (ResidueField R))) {t : R} (ht : Irreducible t)
    (n : ℕ) (z : R) :
    ∃ c : Fin n → k, z - ∑ i, algebraMap k R (c i) * t ^ (i : ℕ) ∈
      IsLocalRing.maximalIdeal R ^ n := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨w, hw⟩ := (mem_maximalIdeal_pow_iff ht).mp hc
    obtain ⟨d, hd, -⟩ := existsUnique_sub_algebraMap_mem_maximalIdeal h w
    obtain ⟨w', hw'⟩ := (mem_maximalIdeal_pow_iff ht (n := 1)).mp (by simpa using hd)
    refine ⟨Fin.snoc c d, (mem_maximalIdeal_pow_iff ht).mpr ⟨w', ?_⟩⟩
    simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc,
      Fin.val_last]
    linear_combination hw + t ^ n * hw'

/-- **Truncated expansions.** In a discrete valuation ring with uniformizer `t` whose residue
field is `k`, every `z` has unique `c₀, …, cₙ₋₁ ∈ k` with
`z - (c₀ + c₁ t + ⋯ + cₙ₋₁ tⁿ⁻¹) ∈ 𝔪ⁿ`, that is, `z = c₀ + c₁ t + ⋯ + cₙ₋₁ tⁿ⁻¹ + zₙ tⁿ` for
some `zₙ ∈ R`, unique since `t ≠ 0`. -/
theorem existsUnique_sub_sum_mem_maximalIdeal_pow
    (h : Function.Surjective (algebraMap k (ResidueField R))) {t : R} (ht : Irreducible t)
    (n : ℕ) (z : R) :
    ∃! c : Fin n → k, z - ∑ i, algebraMap k R (c i) * t ^ (i : ℕ) ∈
      IsLocalRing.maximalIdeal R ^ n := by
  obtain ⟨c, hc⟩ := exists_sub_sum_mem_maximalIdeal_pow h ht n z
  refine ⟨c, hc, fun d hd ↦ ?_⟩
  have hz : ∑ i, algebraMap k R ((d - c) i) * t ^ (i : ℕ) ∈ IsLocalRing.maximalIdeal R ^ n := by
    convert sub_mem hc hd using 1
    simp only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  exact sub_eq_zero.mp ((sum_algebraMap_mul_pow_mem_maximalIdeal_pow_iff ht (d - c)).mp hz)

/-- **Order equals colength.** Let `R` be a discrete valuation ring with maximal ideal `𝔪` and
uniformizer `t`, whose residue field is `k`. Then:

* (a) every `z ∈ R` has a unique `c ∈ k` with `z - c ∈ 𝔪`, and unique `c₀, …, cₙ₋₁ ∈ k` with
  `z - (c₀ + c₁ t + ⋯ + cₙ₋₁ tⁿ⁻¹) ∈ 𝔪ⁿ`;
* (b) `dim_k 𝔪ⁿ/𝔪ⁿ⁺¹ = 1` and `dim_k R/𝔪ⁿ = n`;
* (c) `ord z = n` if and only if `(z) = 𝔪ⁿ`, and `ℓ_k(R/(z)) = ord z` in `ℕ∞` (both `⊤` for
  `z = 0`), so that `dim_k R/(z) = ord z` for `z ≠ 0`.

Milestone: *Order equals colength in a discrete valuation ring with residue field k*. -/
theorem existsUnique_and_finrank_and_addVal_eq_length
    (h : Function.Surjective (algebraMap k (ResidueField R))) {t : R} (ht : Irreducible t) :
    ((∀ z : R, ∃! c : k, z - algebraMap k R c ∈ IsLocalRing.maximalIdeal R) ∧
      ∀ (n : ℕ) (z : R), ∃! c : Fin n → k, z - ∑ i, algebraMap k R (c i) * t ^ (i : ℕ) ∈
        IsLocalRing.maximalIdeal R ^ n) ∧
    ((∀ n : ℕ, Module.finrank k (↥(IsLocalRing.maximalIdeal R ^ n) ⧸
      (IsLocalRing.maximalIdeal R • ⊤ : Submodule R ↥(IsLocalRing.maximalIdeal R ^ n))) = 1) ∧
      ∀ n : ℕ, Module.finrank k (R ⧸ IsLocalRing.maximalIdeal R ^ n) = n) ∧
    ((∀ (z : R) (n : ℕ), addVal R z = n ↔ span {z} = IsLocalRing.maximalIdeal R ^ n) ∧
      (∀ z : R, Module.length k (R ⧸ span {z}) = addVal R z) ∧
      ∀ z : R, z ≠ 0 → (Module.finrank k (R ⧸ span {z}) : ℕ∞) = addVal R z) :=
  ⟨⟨existsUnique_sub_algebraMap_mem_maximalIdeal h,
      existsUnique_sub_sum_mem_maximalIdeal_pow h ht⟩,
    ⟨finrank_pow_maximalIdeal_quotient h, finrank_quotient_pow_maximalIdeal h⟩,
    ⟨addVal_eq_coe_iff_span_singleton_eq, length_quotient_span_singleton_eq_addVal h,
      fun _ ↦ finrank_quotient_span_singleton h⟩⟩

end Field

end IsDiscreteValuationRing
