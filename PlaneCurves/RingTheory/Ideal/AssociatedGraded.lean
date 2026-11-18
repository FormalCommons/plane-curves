/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Ideal.Colon
public import TauCeti.RingTheory.Ideal.AssociatedGraded

/-!
# Colon ideals of powers, and dimensions of quotients by powers of an ideal

For an ideal `I` whose associated graded ring `gr_I R` is a domain, and `f ∈ I ^ m \ I ^ (m + 1)`,
the colon ideal `(I ^ n : f)` is `I ^ (n - m)`. Over a field `k`, the dimensions of the quotients
of a `k`-algebra by an ideal, by the ideal and an element, and by the colon ideal are related
through the exact sequence `0 → A ⧸ (I : f) → A ⧸ I → A ⧸ (I + (f)) → 0`, and the dimension of
the graded piece `I ^ n ⧸ I ^ (n + 1)` is the difference of those of `A ⧸ I ^ (n + 1)` and
`A ⧸ I ^ n`.

## Main definitions

* `DoubleQuot.quotQuotPowEquivQuotSupₐ`: `(A ⧸ I) ⧸ (J (A ⧸ I)) ^ n ≅ A ⧸ (I ⊔ J ^ n)`.

## Main results

* `Ideal.colon_pow_span_singleton`: `(I ^ n : f) = I ^ (n - m)` when `gr_I R` is a domain and
  `f` has exact `I`-adic order `m`.
* `Ideal.finrank_quotient_eq_finrank_quotient_sup_add`:
  `dim_k A ⧸ I = dim_k A ⧸ (I ⊔ (f)) + dim_k A ⧸ (I : f)`.
* `Ideal.finrank_quotient_pow_succ`:
  `dim_k A ⧸ I ^ (n + 1) = dim_k A ⧸ I ^ n + dim_k I ^ n ⧸ I ^ (n + 1)`.
-/

public section

open Module

namespace Ideal

variable {R : Type*} [CommRing R] {I : Ideal R}

/-- If the associated graded ring of `I` has no zero divisors and `f ∈ I ^ m \ I ^ (m + 1)`, then
`g f ∈ I ^ n` iff `g ∈ I ^ (n - m)`: the colon ideal `(I ^ n : f)` is `I ^ (n - m)`. -/
theorem colon_pow_span_singleton [NoZeroDivisors I.AssociatedGraded] {f : R} {m : ℕ}
    (hf : f ∈ I ^ m) (hf' : f ∉ I ^ (m + 1)) (n : ℕ) :
    (I ^ n).colon (span {f}) = I ^ (n - m) := by
  ext g
  rw [mem_colon_span_singleton]
  refine ⟨fun h ↦ ?_, fun h ↦ pow_le_pow_right (by omega) (mul_mem_pow_add h hf)⟩
  by_contra hg
  classical
  have hex : ∃ j, g ∉ I ^ (j + 1) := ⟨n - m - 1, by
    rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero fun h0 ↦ hg (by simp [h0]))]⟩
  obtain ⟨j, hj', hj⟩ : ∃ j, g ∉ I ^ (j + 1) ∧ g ∈ I ^ j := by
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    rcases h0 : Nat.find hex with _ | j
    · simp
    · simpa using Nat.find_min hex (h0 ▸ Nat.lt_succ_self j)
  have hle : j + 1 ≤ n - m := by
    by_contra hlt
    exact hg (pow_le_pow_right (by omega) hj)
  exact AssociatedGraded.mul_notMem_pow_succ hj hj' hf hf'
    (pow_le_pow_right (by omega) h)

end Ideal

namespace Ideal

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

/-- For an ideal `I` of a `k`-algebra `A` with `A ⧸ I` finite-dimensional and `f ∈ A`, the exact
sequence `0 → A ⧸ (I : f) → A ⧸ I → A ⧸ (I ⊔ (f)) → 0`, the first map being multiplication by
`f`, gives `dim_k A ⧸ I = dim_k A ⧸ (I ⊔ (f)) + dim_k A ⧸ (I : f)`. -/
theorem finrank_quotient_eq_finrank_quotient_sup_add (I : Ideal A) (f : A)
    [Module.Finite k (A ⧸ I)] :
    finrank k (A ⧸ I) = finrank k (A ⧸ (I ⊔ span {f})) + finrank k (A ⧸ I.colon (span {f})) := by
  let ψ : (A ⧸ I) →ₗ[k] A ⧸ (I ⊔ span {f}) := (Quotient.factorₐ k le_sup_left).toLinearMap
  let φ : A →ₗ[k] A ⧸ I := (Quotient.mkₐ k I).toLinearMap ∘ₗ LinearMap.mulRight k f
  have hker : LinearMap.ker φ = (I.colon (span {f})).restrictScalars k := by
    ext g
    simp only [LinearMap.mem_ker, Submodule.restrictScalars_mem, mem_colon_span_singleton, φ,
      LinearMap.comp_apply, AlgHom.toLinearMap_apply, Quotient.mkₐ_eq_mk,
      LinearMap.mulRight_apply, Quotient.eq_zero_iff_mem]
  have hrange : LinearMap.range φ = LinearMap.ker ψ := by
    ext x
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective x
    simp only [LinearMap.mem_range, LinearMap.mem_ker, ψ, φ, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, Quotient.mkₐ_eq_mk, LinearMap.mulRight_apply,
      Quotient.factorₐ_apply, Quotient.factor_mk, Quotient.eq_zero_iff_mem, Quotient.eq]
    rw [sup_comm, mem_span_singleton_sup]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, x - y * f, by simpa using I.neg_mem hy, by ring⟩
    · rintro ⟨a, b, hb, rfl⟩
      exact ⟨a, by simpa using I.neg_mem hb⟩
  rw [← LinearMap.finrank_range_add_finrank_ker ψ,
    LinearMap.range_eq_top.2 (Quotient.factor_surjective le_sup_left), finrank_top,
    ← hrange, ← (φ.quotKerEquivRange).finrank_eq, hker,
    (Submodule.Quotient.restrictScalarsEquiv k _).finrank_eq]

/-- `dim_k A ⧸ I ^ (n + 1) = dim_k A ⧸ I ^ n + dim_k I ^ n ⧸ I ^ (n + 1)`, from the exact sequence
`0 → I ^ n ⧸ I ^ (n + 1) → A ⧸ I ^ (n + 1) → A ⧸ I ^ n → 0`. -/
theorem finrank_quotient_pow_succ (I : Ideal A) (n : ℕ) [Module.Finite k (A ⧸ I ^ (n + 1))] :
    finrank k (A ⧸ I ^ (n + 1)) = finrank k (A ⧸ I ^ n) + finrank k (I.GradedPiece n) := by
  have hle : I ^ (n + 1) ≤ I ^ n := pow_le_pow_right n.le_succ
  let ψ : (A ⧸ I ^ (n + 1)) →ₗ[k] A ⧸ I ^ n := (Quotient.factorₐ k hle).toLinearMap
  let φ : ↥(I ^ n) →ₗ[A] A ⧸ I ^ (n + 1) := (I ^ (n + 1)).mkQ ∘ₗ (I ^ n).subtype
  have hker : Submodule.comap (I ^ n).subtype (I ^ (n + 1)) = LinearMap.ker φ := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hrange : (LinearMap.range φ).restrictScalars k = LinearMap.ker ψ := by
    ext x
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective x
    simp only [Submodule.restrictScalars_mem, LinearMap.mem_range, LinearMap.mem_ker, ψ, φ,
      LinearMap.comp_apply, AlgHom.toLinearMap_apply, Submodule.mkQ_apply,
      Submodule.subtype_apply, Quotient.factorₐ_apply, Quotient.factor_mk,
      Quotient.eq_zero_iff_mem]
    refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun h ↦ ⟨⟨x, h⟩, rfl⟩⟩
    rw [Quotient.mk_eq_mk, Quotient.eq] at hy
    simpa using sub_mem y.2 (hle hy)
  rw [← LinearMap.finrank_range_add_finrank_ker ψ,
    LinearMap.range_eq_top.2 (Quotient.factor_surjective hle), finrank_top, ← hrange,
    ((Submodule.quotEquivOfEq _ _ hker).restrictScalars k).finrank_eq,
    (φ.quotKerEquivRange.restrictScalars k).finrank_eq]
  rfl

end Ideal

namespace DoubleQuot

variable (R : Type*) {A : Type*} [CommSemiring R] [CommRing A] [Algebra R A]

/-- The quotient of `A ⧸ I` by the `n`-th power of the image of `J` is `A ⧸ (I ⊔ J ^ n)`. -/
noncomputable def quotQuotPowEquivQuotSupₐ (I J : Ideal A) (n : ℕ) :
    ((A ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ^ n) ≃ₐ[R] A ⧸ I ⊔ J ^ n :=
  (Ideal.quotientEquivAlgOfEq R (by rw [← Ideal.map_pow]; rfl)).trans
    (quotQuotEquivQuotSupₐ R I (J ^ n))

theorem quotQuotPowEquivQuotSupₐ_def (I J : Ideal A) (n : ℕ) :
    quotQuotPowEquivQuotSupₐ R I J n =
      (Ideal.quotientEquivAlgOfEq R (by rw [← Ideal.map_pow]; rfl)).trans
        (quotQuotEquivQuotSupₐ R I (J ^ n)) :=
  (rfl)

@[simp]
theorem quotQuotPowEquivQuotSupₐ_mk (I J : Ideal A) (n : ℕ) (x : A) :
    quotQuotPowEquivQuotSupₐ R I J n (Ideal.Quotient.mk _ (Ideal.Quotient.mk I x)) =
      Ideal.Quotient.mk _ x :=
  (rfl)

end DoubleQuot
