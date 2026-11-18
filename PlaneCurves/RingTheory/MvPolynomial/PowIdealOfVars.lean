/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Nullstellensatz
public import TauCeti.RingTheory.MvPolynomial.OrderAt
public import PlaneCurves.RingTheory.MvPolynomial.BinaryForm.Basis
import TauCeti.RingTheory.MvPolynomial.Ideal

/-!
# Polynomials modulo a power of the ideal of a point

Let `I = (X₁, …, Xₙ)` be the ideal of the variables (`MvPolynomial.idealOfVars`) and `I_P` the
ideal of a point `P` (`MvPolynomial.vanishingIdeal k {P}`). The residues of the monomials of
degree `< m` form a basis of `R[X₁, …, Xₙ] ⧸ I ^ m`, which therefore has dimension
`(m + n - 1).choose n`; the Taylor shift at `P` carries `I_P ^ m` to `I ^ m`, so the same holds
for `k[X₁, …, Xₙ] ⧸ I_P ^ m`.

## Main definitions and results

* `MvPolynomial.restrictSupportEquivQuotientPowIdealOfVars`: the polynomials supported in degrees
  `< m` map isomorphically onto `R[X] ⧸ I ^ m`.
* `MvPolynomial.quotientPowIdealOfVarsBasis`: the basis of `R[X] ⧸ I ^ m` given by the residues
  of the monomials of degree `< m`.
* `MvPolynomial.finrank_quotient_pow_idealOfVars`: `dim R[X] ⧸ I ^ m = (m + n - 1).choose n`.
* `MvPolynomial.map_taylor_vanishingIdeal_singleton`: the Taylor shift at `P` carries `I_P` to
  `I`.
* `MvPolynomial.finrank_quotient_pow_vanishingIdeal_singleton`:
  `dim k[X] ⧸ I_P ^ m = (m + n - 1).choose n`.
* `MvPolynomial.finrank_homogeneousSubmodule_and_finrank_quotient_pow_vanishingIdeal_singleton`:
  the monomial bases and dimensions of the spaces of forms, the bases of products of linear forms
  in `k[X, Y]`, the description of `I ^ m`, the monomial basis and dimension of `k[X] ⧸ I ^ m`,
  and the dimension of `k[X] ⧸ I_P ^ m`, together.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §2.6, Problems 2.35 and 2.36; §2.8, Example and
  Problem 2.46
-/

public section

namespace MvPolynomial

open Finset

section CommRing

variable {σ R : Type*} [CommRing R]

private lemma bijective_mkₐ_comp_subtype (m : ℕ) :
    Function.Bijective ((Ideal.Quotient.mkₐ R (idealOfVars σ R ^ m)).toLinearMap ∘ₗ
      (restrictSupport R {d : σ →₀ ℕ | d.degree < m}).subtype) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun ⟨p, hp⟩ h ↦ ?_, fun q ↦ ?_⟩
  · rw [mem_restrictSupport_iff] at hp
    replace h : p ∈ idealOfVars σ R ^ m := by simpa [Ideal.Quotient.eq_zero_iff_mem] using h
    rw [mem_pow_idealOfVars_iff] at h
    ext1
    simp only [ZeroMemClass.coe_zero, ← support_eq_empty, Finset.eq_empty_iff_forall_notMem]
    exact fun d hd ↦ (h d hd).not_gt (hp hd)
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  induction p using MvPolynomial.induction_on' with
  | monomial d r =>
    by_cases hd : d.degree < m
    · exact ⟨⟨monomial d r, (monomial_mem_restrictSupport R).2 (.inl hd)⟩, rfl⟩
    · refine ⟨0, ?_⟩
      rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem, mem_pow_idealOfVars_iff]
      intro x hx
      rw [(support_monomial_subset hx : x ∈ ({d} : Finset _)) |> Finset.mem_singleton.1]
      exact not_lt.1 hd
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨a + b, by simp only [map_add, ha, hb]⟩

/-- The polynomials supported in degrees `< m` map isomorphically onto `R[X] ⧸ I ^ m`, where
`I = (X₁, …, Xₙ)`, by taking residues. -/
noncomputable def restrictSupportEquivQuotientPowIdealOfVars (m : ℕ) :
    restrictSupport R {d : σ →₀ ℕ | d.degree < m} ≃ₗ[R]
      MvPolynomial σ R ⧸ idealOfVars σ R ^ m :=
  LinearEquiv.ofBijective _ (bijective_mkₐ_comp_subtype m)

@[simp]
theorem restrictSupportEquivQuotientPowIdealOfVars_apply (m : ℕ)
    (p : restrictSupport R {d : σ →₀ ℕ | d.degree < m}) :
    restrictSupportEquivQuotientPowIdealOfVars m p = Ideal.Quotient.mk _ (p : MvPolynomial σ R) :=
  (rfl)

/-- The residues of the monomials of degree `< m` form a basis of `R[X] ⧸ I ^ m`, where
`I = (X₁, …, Xₙ)`. -/
noncomputable def quotientPowIdealOfVarsBasis (m : ℕ) :
    Module.Basis {d : σ →₀ ℕ | d.degree < m} R (MvPolynomial σ R ⧸ idealOfVars σ R ^ m) :=
  (basisRestrictSupport R _).map (restrictSupportEquivQuotientPowIdealOfVars m)

@[simp]
theorem quotientPowIdealOfVarsBasis_apply (m : ℕ) (d : {d : σ →₀ ℕ | d.degree < m}) :
    quotientPowIdealOfVarsBasis m d = Ideal.Quotient.mk _ (monomial (d : σ →₀ ℕ) (1 : R)) := by
  simp [quotientPowIdealOfVarsBasis, basisRestrictSupport_apply_coe]

/-- The polynomials supported in degrees `< m + 1` are those of total degree `≤ m`. -/
theorem restrictSupport_degree_lt_succ (m : ℕ) :
    restrictSupport R {d : σ →₀ ℕ | d.degree < m + 1} = restrictTotalDegree σ R m := by
  simp only [restrictTotalDegree, Nat.lt_succ_iff]
  rfl

instance [Finite σ] (m : ℕ) : Module.Finite R (MvPolynomial σ R ⧸ idealOfVars σ R ^ m) := by
  have : Module.Finite R (restrictSupport R {d : σ →₀ ℕ | d.degree < m + 1}) := by
    rw [restrictSupport_degree_lt_succ]
    infer_instance
  have := Module.Finite.equiv (restrictSupportEquivQuotientPowIdealOfVars (R := R) (σ := σ) (m + 1))
  exact Module.Finite.of_surjective
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ m))).toLinearMap
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ m)))

/-- `R[X₁, …, Xₙ] ⧸ I ^ (m + 1)`, for `I = (X₁, …, Xₙ)`, has dimension `(m + n).choose n`. -/
theorem finrank_quotient_pow_idealOfVars_succ [Fintype σ] [StrongRankCondition R] (m : ℕ) :
    Module.finrank R (MvPolynomial σ R ⧸ idealOfVars σ R ^ (m + 1)) =
      (m + Fintype.card σ).choose (Fintype.card σ) := by
  rw [← (restrictSupportEquivQuotientPowIdealOfVars (m + 1)).finrank_eq,
    restrictSupport_degree_lt_succ, TauCeti.finrank_restrictTotalDegree]

/-- `R[X₁, …, Xₙ] ⧸ I ^ m`, for `I = (X₁, …, Xₙ)`, has dimension `(m + n - 1).choose n`, unless
`m = n = 0` (when the quotient is `0` and the formula gives `1`). -/
theorem finrank_quotient_pow_idealOfVars [Fintype σ] [StrongRankCondition R] {m : ℕ}
    (h : m ≠ 0 ∨ Nonempty σ) :
    Module.finrank R (MvPolynomial σ R ⧸ idealOfVars σ R ^ m) =
      (m + Fintype.card σ - 1).choose (Fintype.card σ) := by
  rcases m with _ | m
  · have hσ : 0 < Fintype.card σ := Fintype.card_pos_iff.2 (h.resolve_left (by simp))
    rw [pow_zero, Ideal.one_eq_top, Nat.choose_eq_zero_of_lt (by omega)]
    exact Module.finrank_zero_of_subsingleton
  · rw [finrank_quotient_pow_idealOfVars_succ]
    congr 1
    omega

end CommRing

section Field

variable {σ k : Type*} [Field k]

/-- The Taylor shift at `P`, `f ↦ f(X + P)`, carries the ideal of `P` to the ideal of the
variables. -/
theorem map_taylor_vanishingIdeal_singleton (P : σ → k) :
    (vanishingIdeal k {P}).map (taylor P) = idealOfVars σ k := by
  have hker : vanishingIdeal k {P} = (idealOfVars σ k).comap (taylor P) := by
    ext g
    rw [mem_vanishingIdeal_singleton_iff, Ideal.mem_comap, ← ker_constantCoeff,
      RingHom.mem_ker, constantCoeff_taylor]
    exact Iff.rfl
  rw [hker, Ideal.map_comap_of_surjective _ fun g ↦ ⟨taylor (-P) g, by simp [taylor_taylor]⟩]

/-- `k[X₁, …, Xₙ] ⧸ I_P ^ m`, for the ideal `I_P` of a point `P`, has dimension
`(m + n - 1).choose n`, unless `m = n = 0` (when the quotient is `0` and the formula gives
`1`). -/
theorem finrank_quotient_pow_vanishingIdeal_singleton [Fintype σ] (P : σ → k) {m : ℕ}
    (h : m ≠ 0 ∨ Nonempty σ) :
    Module.finrank k (MvPolynomial σ k ⧸ vanishingIdeal k {P} ^ m) =
      (m + Fintype.card σ - 1).choose (Fintype.card σ) := by
  let e : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k := AlgEquiv.ofBijective (taylor P)
    ⟨taylor_injective P, fun g ↦ ⟨taylor (-P) g, by simp [taylor_taylor]⟩⟩
  rw [(Ideal.quotientEquivAlg _ (idealOfVars σ k ^ m) e (by
    rw [Ideal.map_pow]
    exact congrArg (· ^ m) (map_taylor_vanishingIdeal_singleton P).symm)).toLinearEquiv.finrank_eq,
    finrank_quotient_pow_idealOfVars h]

/-- **Dimensions of spaces of forms and of `k[X] ⧸ I_P ^ m`.** Let `k` be a field and
`I = (X₁, …, Xₙ)`.
(a) The monomials of degree `d` form a basis of the forms of degree `d` in `n` variables, which
therefore form a space of dimension `n.multichoose d`, that is `(d + n - 1).choose (n - 1)`.
(b) If `L₀, L₁, …` and `M₀, M₁, …` are linear forms in `k[X, Y]` and no `Lᵢ` is zero or
proportional to an `Mⱼ`, the products `L₀ ⋯ L_{i-1} M₀ ⋯ M_{d-i-1}`, `0 ≤ i ≤ d`, form a basis
of the forms of degree `d`.
(c) `I ^ m` consists of the polynomials with no terms of degree `< m`, the residues of the
monomials of degree `< m` form a basis of `k[X₁, …, Xₙ] ⧸ I ^ m`, and this space has dimension
`(m + n - 1).choose n`, unless `m = n = 0`; the same dimension holds for `k[X₁, …, Xₙ] ⧸ I_P ^ m`,
for the ideal `I_P` of any point `P` of `kⁿ`.

Milestone: *Dimensions of spaces of forms and of polynomials modulo a power of the ideal of a
point*. -/
theorem finrank_homogeneousSubmodule_and_finrank_quotient_pow_vanishingIdeal_singleton
    [Fintype σ] :
    (∀ d, ∃ b : Module.Basis {s : σ →₀ ℕ // s.degree = d} k (homogeneousSubmodule σ k d),
      ∀ s, (b s : MvPolynomial σ k) = monomial s.1 1) ∧
    (∀ d, Module.finrank k (homogeneousSubmodule σ k d) = (Fintype.card σ).multichoose d) ∧
    (∀ L M : ℕ → MvPolynomial (Fin 2) k, (∀ i, (L i).IsHomogeneous 1) →
      (∀ j, (M j).IsHomogeneous 1) → (∀ i j, LinearIndependent k ![L i, M j]) → ∀ d,
      ∃ b : Module.Basis (Fin (d + 1)) k (homogeneousSubmodule (Fin 2) k d), ∀ i,
        (b i : MvPolynomial (Fin 2) k) = (∏ l ∈ range i, L l) * ∏ l ∈ range (d - i), M l) ∧
    (∀ (m : ℕ) (p : MvPolynomial σ k),
      p ∈ idealOfVars σ k ^ m ↔ ∀ x ∈ p.support, m ≤ x.degree) ∧
    (∀ m : ℕ, ∃ b : Module.Basis {d : σ →₀ ℕ | d.degree < m} k
        (MvPolynomial σ k ⧸ idealOfVars σ k ^ m),
      ∀ d, b d = Ideal.Quotient.mk _ (monomial (d : σ →₀ ℕ) (1 : k))) ∧
    (∀ m : ℕ, (m ≠ 0 ∨ Nonempty σ) →
      Module.finrank k (MvPolynomial σ k ⧸ idealOfVars σ k ^ m) =
        (m + Fintype.card σ - 1).choose (Fintype.card σ)) ∧
    (∀ (P : σ → k) (m : ℕ), (m ≠ 0 ∨ Nonempty σ) →
      Module.finrank k (MvPolynomial σ k ⧸ vanishingIdeal k {P} ^ m) =
        (m + Fintype.card σ - 1).choose (Fintype.card σ)) :=
  ⟨fun d ↦ ⟨TauCeti.homogeneousMonomialBasis d, TauCeti.coe_homogeneousMonomialBasis d⟩,
    TauCeti.finrank_homogeneousSubmodule_eq_multichoose σ k,
    fun _ _ hL hM hLM d ↦ ⟨basisProdMulProd hL hM hLM d, coe_basisProdMulProd_apply hL hM hLM d⟩,
    mem_pow_idealOfVars_iff,
    fun m ↦ ⟨quotientPowIdealOfVarsBasis m, quotientPowIdealOfVarsBasis_apply m⟩,
    fun _ h ↦ finrank_quotient_pow_idealOfVars h,
    fun P _ h ↦ finrank_quotient_pow_vanishingIdeal_singleton P h⟩

/-- The hypothesis `m ≠ 0 ∨ Nonempty σ` is needed: with no variables, `k ⧸ I_P ^ 0 = 0`, while
`(0 + 0 - 1).choose 0 = 1`. -/
example (P : Fin 0 → k) :
    Module.finrank k (MvPolynomial (Fin 0) k ⧸ vanishingIdeal k {P} ^ 0) ≠
      (0 + Fintype.card (Fin 0) - 1).choose (Fintype.card (Fin 0)) := by
  rw [pow_zero, Ideal.one_eq_top, Module.finrank_zero_of_subsingleton]
  simp

end Field

end MvPolynomial

end
