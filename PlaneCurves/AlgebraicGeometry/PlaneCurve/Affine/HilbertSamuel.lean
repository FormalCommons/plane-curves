/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.RingTheory.RegularLocalRing.AssociatedGraded
public import PlaneCurves.AlgebraicGeometry.AffineSpace.LocalRing
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.Multiplicity
public import PlaneCurves.RingTheory.Ideal.AssociatedGraded
public import PlaneCurves.RingTheory.DiscreteValuationRing.Colength
public import PlaneCurves.RingTheory.MvPolynomial.Taylor
public import PlaneCurves.RingTheory.Length
public import PlaneCurves.RingTheory.MvPolynomial.PowIdealOfVars

/-!
# The Hilbert–Samuel function of a plane curve at a point

For `F ∈ k[X₁, …, Xₙ]` and a point `P`, let `𝒪 = 𝒪_P(𝔸ⁿ)`, `𝔪` its maximal ideal, `f` the image
of `F` in `𝒪` and `m = m_P(F)`. Since the associated graded ring of the regular local ring `𝒪` is a
domain, `(𝔪ʲ : f) = 𝔪ʲ⁻ᵐ`, so the sequence `0 → 𝒪 ⧸ 𝔪ʲ⁻ᵐ → 𝒪 ⧸ 𝔪ʲ → 𝒪 ⧸ (𝔪ʲ, f) → 0` is exact
and `dim_k 𝒪 ⧸ (𝔪ʲ, f)` is a difference of two dimensions of `k[X] ⧸ I_P ^ j`.

For a plane curve, with `𝔪` now the image of the maximal ideal in `𝒪_P(𝔸²) ⧸ (F)` (the maximal
ideal of the local ring of the curve when `F(P) = 0`), this gives
`dim_k 𝔪ⁿ / 𝔪ⁿ⁺¹ = min (n + 1, m_P(F))` for every `F` and every `n`, as Fulton remarks after
Theorem 2 of §3.2. Its consequences are Theorem 2 of §3.2 and Problems 3.13 and 3.24(a).

The local ring of the curve is `𝒪_P(𝔸²) ⧸ (F)`, as in `DESIGN.md`; for irreducible `F` it is
Fulton's `𝒪_P(F)` (`AffineSpace.localRing.quotient_iso`). The pieces `𝔪ⁿ / 𝔪ⁿ⁺¹` are Tau Ceti's
`Ideal.GradedPiece`.

## Main results

* `PlaneCurves.AffineSpace.localRing.colon_maximalIdeal_pow_span_singleton`:
  `(𝔪ʲ : f) = 𝔪ʲ⁻ᵐ` in `𝒪_P(𝔸ⁿ)`.
* `PlaneCurves.AffineSpace.localRing.finrank_quotient_map_maximalIdeal_pow_add`:
  `dim_k (𝒪 ⧸ (f)) ⧸ 𝔪ʲ + dim_k k[X] ⧸ I_P ^ (j - m) = dim_k k[X] ⧸ I_P ^ j`.
* `PlaneCurves.Affine.finrank_gradedPiece`: `dim_k 𝔪ⁿ / 𝔪ⁿ⁺¹ = min (n + 1, m_P(F))`.
* `PlaneCurves.Affine.finrank_quotient_pow_of_orderAt_le`:
  `dim_k 𝒪 ⧸ 𝔪ⁿ = n m - m (m - 1) / 2` for `n ≥ m`.
* `PlaneCurves.Affine.orderAt_eq_of_ringEquiv`: isomorphic local rings of plane curves give
  equal multiplicities.
* `PlaneCurves.Affine.exists_linearEquiv_gradedPiece_one`: Problem 3.24(a).
* `PlaneCurves.Affine.finrank_gradedPiece_and_finrank_quotient_pow_and_orderAt_eq_of_ringEquiv`:
  the multiplicity of a plane curve is determined by its local ring.
* `PlaneCurves.Affine.finrank_gradedPiece_of_lt_orderAt_and_exists_linearEquiv`: the embedding
  dimension of a plane curve at a point.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §3.2, Theorem 2 and Problem 3.13; §3.3,
  Problem 3.24(a)
-/

public section

open Module MvPolynomial IsLocalRing Ideal

namespace PlaneCurves

namespace AffineSpace.localRing

variable {k : Type*} [Field k] {σ : Type*} {P : σ → k}

/-- `𝒪_P(𝔸ᵈ) ⧸ 𝔪 ^ n` is finite-dimensional over `k`. -/
instance finite_quotient_maximalIdeal_pow [Finite σ] (n : ℕ) :
    Module.Finite k (localRing k P ⧸ maximalIdeal (localRing k P) ^ n) := by
  have := Fintype.ofFinite σ
  refine .equiv (((Ideal.quotientEquivAlg (vanishingIdeal k {P} ^ n) (idealOfVars σ k ^ n)
    (taylorAlgEquiv P) ?_).symm.trans (quotientPowAlgEquiv P n)).toLinearEquiv)
  have h := map_taylor_vanishingIdeal_singleton P
  rw [← toAlgHom_taylorAlgEquiv] at h
  rw [Ideal.map_pow]
  exact congrArg (· ^ n) h.symm

/-- `dim_k 𝒪_P(𝔸ᵈ) ⧸ 𝔪 ^ n = (n + d - 1).choose d`, the dimension of `k[X₁, …, X_d] ⧸ I_P ^ n`. -/
theorem finrank_quotient_maximalIdeal_pow [Fintype σ] [Nonempty σ] (n : ℕ) :
    finrank k (localRing k P ⧸ maximalIdeal (localRing k P) ^ n) =
      (n + Fintype.card σ - 1).choose (Fintype.card σ) := by
  rw [← (quotientPowAlgEquiv P n).toLinearEquiv.finrank_eq,
    finrank_quotient_pow_vanishingIdeal_singleton P (.inr ‹_›)]

/-- In `𝒪_P(𝔸ᵈ)`, `(𝔪 ^ n : F) = 𝔪 ^ (n - m)` for `m = m_P(F)`: `G F ∈ 𝔪 ^ n` iff
`G ∈ 𝔪 ^ (n - m)`, since the leading forms of `F` and `G` multiply. -/
theorem colon_maximalIdeal_pow_span_singleton [Finite σ] {F : MvPolynomial σ k} {m : ℕ}
    (hm : F.orderAt P = m) (n : ℕ) :
    (maximalIdeal (localRing k P) ^ n).colon (span {algebraMap _ (localRing k P) F}) =
      maximalIdeal (localRing k P) ^ (n - m) :=
  colon_pow_span_singleton (algebraMap_mem_maximalIdeal_pow_iff.2 hm.ge)
    (fun h ↦ (algebraMap_mem_maximalIdeal_pow_iff.1 h).not_gt
      (by rw [hm]; exact_mod_cast Nat.lt_succ_self m)) n

/-- The exact sequence `0 → 𝒪 ⧸ 𝔪 ^ (n - m) → 𝒪 ⧸ 𝔪 ^ n → 𝒪 ⧸ ((F) + 𝔪 ^ n) → 0` of `𝒪 = 𝒪_P(𝔸ᵈ)`,
for `m = m_P(F)`, the first map being multiplication by `F`. -/
theorem finrank_quotient_sup_add [Finite σ] {F : MvPolynomial σ k} {m : ℕ}
    (hm : F.orderAt P = m) (n : ℕ) :
    finrank k (localRing k P ⧸ (span {algebraMap _ (localRing k P) F} ⊔
        maximalIdeal (localRing k P) ^ n)) +
      finrank k (localRing k P ⧸ maximalIdeal (localRing k P) ^ (n - m)) =
      finrank k (localRing k P ⧸ maximalIdeal (localRing k P) ^ n) := by
  rw [← colon_maximalIdeal_pow_span_singleton hm n, sup_comm]
  exact (finrank_quotient_eq_finrank_quotient_sup_add _ _).symm

/-- `(𝒪_P(𝔸ᵈ) ⧸ (F)) ⧸ 𝔪 ^ n` is finite-dimensional over `k`, for `𝔪` the image of the maximal
ideal. -/
instance finite_quotient_map_maximalIdeal_pow [Finite σ] (F : MvPolynomial σ k) (n : ℕ) :
    Module.Finite k ((localRing k P ⧸ span {algebraMap _ (localRing k P) F}) ⧸
      (maximalIdeal (localRing k P)).map (Ideal.Quotient.mk _) ^ n) :=
  have : Module.Finite k (localRing k P ⧸ (span {algebraMap _ (localRing k P) F} ⊔
      maximalIdeal (localRing k P) ^ n)) :=
    .of_surjective (Ideal.Quotient.factorₐ k le_sup_right).toLinearMap
      (Ideal.Quotient.factor_surjective le_sup_right)
  .equiv (DoubleQuot.quotQuotPowEquivQuotSupₐ k (span {algebraMap _ (localRing k P) F})
      (maximalIdeal (localRing k P)) n).symm.toLinearEquiv

/-- For `m = m_P(F)` finite and `𝔪` the image of the maximal ideal in `𝒪 = 𝒪_P(𝔸ᵈ) ⧸ (F)`,
`dim_k 𝒪 ⧸ 𝔪 ^ n + dim_k k[X] ⧸ I_P ^ (n - m) = dim_k k[X] ⧸ I_P ^ n`. -/
theorem finrank_quotient_map_maximalIdeal_pow_add [Fintype σ] [Nonempty σ]
    {F : MvPolynomial σ k} {m : ℕ} (hm : F.orderAt P = m) (n : ℕ) :
    finrank k ((localRing k P ⧸ span {algebraMap _ (localRing k P) F}) ⧸
        (maximalIdeal (localRing k P)).map (Ideal.Quotient.mk _) ^ n) +
      (n - m + Fintype.card σ - 1).choose (Fintype.card σ) =
      (n + Fintype.card σ - 1).choose (Fintype.card σ) := by
  rw [(DoubleQuot.quotQuotPowEquivQuotSupₐ k (span {algebraMap _ (localRing k P) F})
      (maximalIdeal (localRing k P)) n).toLinearEquiv.finrank_eq,
    ← finrank_quotient_maximalIdeal_pow (k := k) (P := P),
    ← finrank_quotient_maximalIdeal_pow (k := k) (P := P),
    finrank_quotient_sup_add hm]

/-- For `F = 0`, `dim_k 𝒪_P(𝔸ᵈ) ⧸ 𝔪 ^ n = dim_k k[X] ⧸ I_P ^ n`. -/
theorem finrank_quotient_map_maximalIdeal_pow_of_eq_zero [Fintype σ] [Nonempty σ] (n : ℕ) :
    finrank k ((localRing k P ⧸ span {algebraMap _ (localRing k P) (0 : MvPolynomial σ k)}) ⧸
        (maximalIdeal (localRing k P)).map (Ideal.Quotient.mk _) ^ n) =
      (n + Fintype.card σ - 1).choose (Fintype.card σ) := by
  rw [(DoubleQuot.quotQuotPowEquivQuotSupₐ k
      (span {algebraMap _ (localRing k P) (0 : MvPolynomial σ k)}) (maximalIdeal (localRing k P))
      n).toLinearEquiv.finrank_eq,
    ← finrank_quotient_maximalIdeal_pow (k := k) (P := P), map_zero, span_singleton_eq_bot.2 rfl,
    bot_sup_eq]

end AffineSpace.localRing

namespace Affine

open AffineSpace localRing

variable {k : Type*} [Field k]

/-- `(j + 2).choose 2 = (j + 1).choose 2 + (j + 1)`. -/
private theorem choose_two_succ (j : ℕ) : (j + 1 + 1).choose 2 = (j + 1).choose 2 + (j + 1) := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]

/-- `dim_k 𝒪 ⧸ 𝔪ⁿ + (n - m + 1).choose 2 = (n + 1).choose 2` for a plane curve. -/
private theorem finrank_quotient_pow_add (F : MvPolynomial (Fin 2) k) (P : Fin 2 → k) {m : ℕ}
    (hm : F.orderAt P = m) (n : ℕ) :
    finrank k ((localRing k P ⧸ span {algebraMap _ (localRing k P) F}) ⧸
        (maximalIdeal (localRing k P)).map (Ideal.Quotient.mk _) ^ n) +
      (n - m + 1).choose 2 = (n + 1).choose 2 := by
  simpa using finrank_quotient_map_maximalIdeal_pow_add hm n

/-- **Dimensions of `𝔪ⁿ / 𝔪ⁿ⁺¹` for a plane curve.** For every `F ∈ k[X, Y]` and `P ∈ k²`, let
`𝒪 = 𝒪_P(𝔸²) ⧸ (F)` and `𝔪` the image in `𝒪` of the maximal ideal of `𝒪_P(𝔸²)` (the maximal
ideal of `𝒪` when `F(P) = 0`). Then `dim_k 𝔪ⁿ / 𝔪ⁿ⁺¹ = min (n + 1, m_P(F))` for all `n`. -/
theorem finrank_gradedPiece (F : MvPolynomial (Fin 2) k) (P : Fin 2 → k) (n : ℕ) :
    (finrank k (((maximalIdeal (localRing k P)).map (Ideal.Quotient.mk
      (span {algebraMap _ (localRing k P) F}))).GradedPiece n) : ℕ∞) =
      min (n + 1 : ℕ∞) (F.orderAt P) := by
  have h := finrank_quotient_pow_succ (k := k)
    ((maximalIdeal (localRing k P)).map (Ideal.Quotient.mk
      (span {algebraMap _ (localRing k P) F}))) n
  obtain hm | ⟨m, hm⟩ : F.orderAt P = ⊤ ∨ ∃ m : ℕ, F.orderAt P = m := by
    cases F.orderAt P using ENat.recTopCoe <;> simp
  · rw [hm]
    rw [orderAt_eq_top_iff] at hm
    subst hm
    have h1 := finrank_quotient_map_maximalIdeal_pow_of_eq_zero (k := k) (P := P) n
    have h2 := finrank_quotient_map_maximalIdeal_pow_of_eq_zero (k := k) (P := P) (n + 1)
    rw [Fintype.card_fin, show n + 2 - 1 = n + 1 by omega] at h1
    rw [Fintype.card_fin, show n + 1 + 2 - 1 = n + 1 + 1 by omega] at h2
    rw [min_eq_left le_top]
    have := choose_two_succ n
    exact_mod_cast (by omega : _ = n + 1)
  · have h1 := finrank_quotient_pow_add F P hm n
    have h2 := finrank_quotient_pow_add F P hm (n + 1)
    have := choose_two_succ n
    rw [hm, show min (n + 1 : ℕ∞) m = ((min (n + 1) m : ℕ) : ℕ∞) from rfl,
      Nat.cast_inj]
    rcases lt_or_ge n m with hnm | hnm
    · rw [Nat.sub_eq_zero_of_le hnm.le] at h1
      rw [Nat.sub_eq_zero_of_le hnm] at h2
      omega
    · rw [Nat.sub_add_comm hnm, choose_two_succ] at h2
      omega

/-- `(m + j + 1).choose 2 = (j + 1).choose 2 + (m * j + (m + 1).choose 2)`. -/
private theorem choose_two_add (m j : ℕ) :
    (m + j + 1).choose 2 = (j + 1).choose 2 + (m * j + (m + 1).choose 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + j + 1 = m + j + 1 + 1 by omega, choose_two_succ, ih, choose_two_succ]
    ring

/-- `m * m = 2 * m.choose 2 + m`. -/
private theorem mul_self_eq_two_mul_choose_two_add (m : ℕ) : m * m = 2 * m.choose 2 + m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    linarith

/-- For `n ≥ m = m_P(F)`, `dim_k 𝒪 ⧸ 𝔪ⁿ = n m - m (m - 1) / 2`, where `𝒪 = 𝒪_P(𝔸²) ⧸ (F)` and `𝔪`
is the image of the maximal ideal of `𝒪_P(𝔸²)`. -/
theorem finrank_quotient_pow_of_orderAt_le {F : MvPolynomial (Fin 2) k} {P : Fin 2 → k} {m n : ℕ}
    (hm : F.orderAt P = m) (hn : m ≤ n) :
    finrank k ((localRing k P ⧸ span {algebraMap _ (localRing k P) F}) ⧸
      (maximalIdeal (localRing k P)).map (Ideal.Quotient.mk _) ^ n) = n * m - m * (m - 1) / 2 := by
  have h := finrank_quotient_pow_add F P hm n
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_sub_cancel_left, choose_two_add] at h
  rw [← Nat.choose_two_right, add_mul, mul_self_eq_two_mul_choose_two_add, mul_comm j m]
  rw [show (m + 1).choose 2 = m.choose 2 + m by
    rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]] at h
  generalize m * j = t at *
  omega

/-- `ℕ∞`-valued invariants agreeing after truncation at every `n + 1` are equal. -/
private theorem eq_of_forall_min_eq {a b : ℕ∞}
    (h : ∀ n : ℕ, min (n + 1 : ℕ∞) a = min (n + 1 : ℕ∞) b) : a = b := by
  induction a using ENat.recTopCoe <;> induction b using ENat.recTopCoe
  · rfl
  · rename_i b
    have := h b
    rw [min_eq_left le_top, min_eq_right (by norm_cast; omega)] at this
    norm_cast at this
    omega
  · rename_i a
    have := h a
    rw [min_eq_left le_top, min_eq_right (by norm_cast; omega)] at this
    norm_cast at this
    omega
  · rename_i a b
    have := h (max a b)
    rw [min_eq_right (by norm_cast; omega), min_eq_right (by norm_cast; omega)] at this
    exact this

variable {F : MvPolynomial (Fin 2) k} {P : Fin 2 → k}

/-- For `F(P) = 0`, the image of the maximal ideal of `𝒪_P(𝔸²)` in `𝒪_P(𝔸²) ⧸ (F)` is its maximal
ideal, and `ℓ(𝒪 ⧸ 𝔪ⁿ) = dim_k 𝒪 ⧸ 𝔪ⁿ`. -/
private theorem length_eq_finrank (hF : eval P F = 0) :
    ∃ _ : IsLocalRing (localRing k P ⧸ span {algebraMap _ (localRing k P) F}), ∀ n : ℕ,
      Module.length (localRing k P ⧸ span {algebraMap _ (localRing k P) F})
        ((localRing k P ⧸ span {algebraMap _ (localRing k P) F}) ⧸
          maximalIdeal (localRing k P ⧸ span {algebraMap _ (localRing k P) F}) ^ n) =
        finrank k ((localRing k P ⧸ span {algebraMap _ (localRing k P) F}) ⧸
          (maximalIdeal (localRing k P)).map (Ideal.Quotient.mk _) ^ n) := by
  have hI : span {F} ≤ vanishingIdeal k {P} :=
    span_le.2 (Set.singleton_subset_iff.2 ((mem_vanishingIdeal_singleton_iff P F).2 hF))
  have hJ : (span {F}).map (algebraMap _ (localRing k P)) = span {algebraMap _ _ F} := by
    rw [Ideal.map_span, Set.image_singleton]
  obtain ⟨hloc, hres⟩ : ∃ _ : IsLocalRing (localRing k P ⧸ span {algebraMap _ (localRing k P) F}),
      Function.Bijective (algebraMap k
        (ResidueField (localRing k P ⧸ span {algebraMap _ (localRing k P) F}))) := by
    rw [← hJ]
    have := isLocalRing_quotient hI
    refine ⟨this, ?_⟩
    convert (quotientResidueFieldAlgEquiv P _ hI).symm.bijective
    ext c
    exact ((quotientResidueFieldAlgEquiv P _ hI).symm.commutes c).symm
  refine ⟨hloc, fun n ↦ ?_⟩
  rw [← IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective,
    ← IsLocalRing.length_eq_length_of_surjective_algebraMap_residueField _ hres.2,
    Module.length_eq_finrank]

/-- **The multiplicity is determined by the local ring.** If `F(P) = 0`, `G(Q) = 0` and the local
rings `𝒪_P(𝔸²) ⧸ (F)` and `𝒪_Q(𝔸²) ⧸ (G)` are isomorphic as rings, then `m_P(F) = m_Q(G)`. -/
theorem orderAt_eq_of_ringEquiv {G : MvPolynomial (Fin 2) k} {Q : Fin 2 → k}
    (hF : eval P F = 0) (hG : eval Q G = 0)
    (e : (localRing k P ⧸ span {algebraMap _ (localRing k P) F}) ≃+*
      (localRing k Q ⧸ span {algebraMap _ (localRing k Q) G})) :
    F.orderAt P = G.orderAt Q := by
  obtain ⟨_, hFn⟩ := length_eq_finrank hF
  obtain ⟨_, hGn⟩ := length_eq_finrank hG
  have hd (n : ℕ) : finrank k ((localRing k P ⧸ span {algebraMap _ (localRing k P) F}) ⧸
        (maximalIdeal (localRing k P)).map (Ideal.Quotient.mk _) ^ n) =
      finrank k ((localRing k Q ⧸ span {algebraMap _ (localRing k Q) G}) ⧸
        (maximalIdeal (localRing k Q)).map (Ideal.Quotient.mk _) ^ n) := by
    have h := IsLocalRing.length_quotient_maximalIdeal_pow_eq_of_ringEquiv
      (R := localRing k P ⧸ span {algebraMap _ (localRing k P) F})
      (S := localRing k Q ⧸ span {algebraMap _ (localRing k Q) G}) e n
    rw [hFn, hGn] at h
    exact_mod_cast h
  refine eq_of_forall_min_eq fun n ↦ ?_
  rw [← finrank_gradedPiece, ← finrank_gradedPiece, Nat.cast_inj]
  have h1 := finrank_quotient_pow_succ (k := k)
    ((maximalIdeal (localRing k P)).map (Ideal.Quotient.mk
      (span {algebraMap _ (localRing k P) F}))) n
  have h2 := finrank_quotient_pow_succ (k := k)
    ((maximalIdeal (localRing k Q)).map (Ideal.Quotient.mk
      (span {algebraMap _ (localRing k Q) G}))) n
  have := hd n
  have := hd (n + 1)
  omega

/-- `dim_k 𝔪ⁿ / 𝔪ⁿ⁺¹ = n + 1` for `n < m_P(F)`, where `𝔪` is the image of the maximal ideal of
`𝒪_P(𝔸²)` in `𝒪_P(𝔸²) ⧸ (F)`. -/
theorem finrank_gradedPiece_of_lt_orderAt {n : ℕ} (hn : (n : ℕ∞) < F.orderAt P) :
    finrank k (((maximalIdeal (localRing k P)).map (Ideal.Quotient.mk
      (span {algebraMap _ (localRing k P) F}))).GradedPiece n) = n + 1 := by
  have h := finrank_gradedPiece F P n
  rw [min_eq_left (Order.add_one_le_of_lt hn)] at h
  exact_mod_cast h

/-- `dim_k 𝔪ⁿ / 𝔪ⁿ⁺¹ = m_P(F)` for `n + 1 ≥ m_P(F)`, where `𝔪` is the image of the maximal ideal
of `𝒪_P(𝔸²)` in `𝒪_P(𝔸²) ⧸ (F)`. -/
theorem finrank_gradedPiece_of_orderAt_le {m n : ℕ} (hm : F.orderAt P = m) (hn : m ≤ n + 1) :
    finrank k (((maximalIdeal (localRing k P)).map (Ideal.Quotient.mk
      (span {algebraMap _ (localRing k P) F}))).GradedPiece n) = m := by
  have h := finrank_gradedPiece F P n
  rw [hm, min_eq_right (by exact_mod_cast hn)] at h
  exact_mod_cast h

/-- At a simple point, `dim_k 𝔪 / 𝔪² = 1`. -/
theorem IsSimplePoint.finrank_gradedPiece_one (h : IsSimplePoint F P) :
    finrank k (((maximalIdeal (localRing k P)).map (Ideal.Quotient.mk
      (span {algebraMap _ (localRing k P) F}))).GradedPiece 1) = 1 :=
  finrank_gradedPiece_of_orderAt_le (isSimplePoint_iff_orderAt_eq_one.1 h) (by omega)

/-- At a multiple point, `dim_k 𝔪 / 𝔪² = 2`. -/
theorem IsMultiplePoint.finrank_gradedPiece_one (h : IsMultiplePoint F P) :
    finrank k (((maximalIdeal (localRing k P)).map (Ideal.Quotient.mk
      (span {algebraMap _ (localRing k P) F}))).GradedPiece 1) = 2 :=
  finrank_gradedPiece_of_lt_orderAt (lt_of_lt_of_le (by norm_num : ((1 : ℕ) : ℕ∞) < 2)
    (isMultiplePoint_def.1 h))

/-- A linear map `g : V → 𝔪` with `g⁻¹(𝔪²) = 0` induces an isomorphism of `V` onto `𝔫 / 𝔫²`, for
`𝔫` the image of `𝔪` in `R ⧸ I` with `I ⊆ 𝔪²`, when the dimensions agree. -/
private theorem exists_linearEquiv_gradedPiece_one_of_le {R V : Type*} [CommRing R] [Algebra k R]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] {𝔪 I : Ideal R} (hI : I ≤ 𝔪 ^ 2)
    (g : V →ₗ[k] R) (hg : ∀ v, g v ∈ 𝔪) (hg2 : ∀ v, g v ∈ 𝔪 ^ 2 → v = 0)
    [FiniteDimensional k ((𝔪.map (Ideal.Quotient.mk I)).GradedPiece 1)]
    (hdim : finrank k V = finrank k ((𝔪.map (Ideal.Quotient.mk I)).GradedPiece 1)) :
    ∃ e : V ≃ₗ[k] (𝔪.map (Ideal.Quotient.mk I)).GradedPiece 1,
      ∀ (v : V) (x : ↥(𝔪.map (Ideal.Quotient.mk I) ^ 1)),
        (x : R ⧸ I) = Ideal.Quotient.mk I (g v) → e v = Submodule.Quotient.mk x := by
  have mem (v : V) : Ideal.Quotient.mk I (g v) ∈ 𝔪.map (Ideal.Quotient.mk I) ^ 1 := by
    rw [pow_one]
    exact Ideal.mem_map_of_mem _ (hg v)
  let φ : V →ₗ[k] (𝔪.map (Ideal.Quotient.mk I)).GradedPiece 1 :=
    { toFun := fun v ↦ Submodule.Quotient.mk ⟨_, mem v⟩
      map_add' := fun v w ↦ by
        rw [← Submodule.Quotient.mk_add]
        congr 1
        ext
        simp
      map_smul' := fun c v ↦ by
        rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
        congr 1
        ext
        simp [Algebra.smul_def] }
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun v hv ↦ hg2 v ?_
    rw [LinearMap.coe_mk, AddHom.coe_mk, gradedPiece_mk_eq_zero_iff, ← Ideal.map_pow,
      Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hv
    obtain ⟨y, hy, hyv⟩ := hv
    rw [Ideal.Quotient.eq] at hyv
    simpa using sub_mem hy (hI hyv)
  refine ⟨LinearMap.linearEquivOfInjective φ hinj hdim, fun v x hx ↦ ?_⟩
  rw [LinearMap.linearEquivOfInjective_apply]
  exact congrArg _ (Subtype.ext hx.symm)

/-- **Problem 3.24(a).** If `m_0(F) ≥ 2`, the linear forms `aX + bY` map isomorphically onto
`𝔪 / 𝔪²`, where `𝔪` is the image of the maximal ideal of `𝒪_0(𝔸²)` in `𝒪_0(𝔸²) ⧸ (F)`. -/
theorem exists_linearEquiv_gradedPiece_one {F : MvPolynomial (Fin 2) k}
    (hF : 2 ≤ F.orderAt 0) :
    ∃ e : homogeneousSubmodule (Fin 2) k 1 ≃ₗ[k]
        ((maximalIdeal (localRing k (0 : Fin 2 → k))).map (Ideal.Quotient.mk
          (span {algebraMap _ (localRing k (0 : Fin 2 → k)) F}))).GradedPiece 1,
      ∀ (L : homogeneousSubmodule (Fin 2) k 1) (x : ↥((maximalIdeal
          (localRing k (0 : Fin 2 → k))).map (Ideal.Quotient.mk
            (span {algebraMap _ (localRing k (0 : Fin 2 → k)) F})) ^ 1)),
        (x : localRing k 0 ⧸ span {algebraMap _ (localRing k (0 : Fin 2 → k)) F}) =
          Ideal.Quotient.mk _ (algebraMap _ _ (L : MvPolynomial (Fin 2) k)) →
        e L = Submodule.Quotient.mk x := by
  have h2 := (isMultiplePoint_def.2 hF).finrank_gradedPiece_one
  have hV : finrank k (homogeneousSubmodule (Fin 2) k 1) = 2 := by
    rw [TauCeti.finrank_homogeneousSubmodule_eq_multichoose, Fintype.card_fin,
      Nat.multichoose_one_right]
  have := Module.finite_of_finrank_eq_succ h2
  have := Module.finite_of_finrank_eq_succ hV
  refine exists_linearEquiv_gradedPiece_one_of_le
    (span_le.2 (Set.singleton_subset_iff.2 (algebraMap_mem_maximalIdeal_pow_iff.2 hF)))
    ((IsScalarTower.toAlgHom k (MvPolynomial (Fin 2) k) (localRing k 0)).toLinearMap ∘ₗ
      (homogeneousSubmodule (Fin 2) k 1).subtype) (fun L ↦ ?_) (fun L hL ↦ ?_) (hV.trans h2.symm)
  · have h0 : eval 0 (L : MvPolynomial (Fin 2) k) = 0 := by
      rw [eval_zero, constantCoeff_eq]
      exact L.2.coeff_eq_zero (by simp)
    simpa using algebraMap_mem_maximalIdeal_pow_iff (r := 1).2
      (Order.one_le_iff_pos.2 (orderAt_pos_iff.2 h0))
  · by_contra hL0
    have hne : (L : MvPolynomial (Fin 2) k) ≠ 0 := fun h ↦ hL0 (Subtype.ext h)
    have h1 := orderAt_le_totalDegree hne 0
    rw [L.2.totalDegree hne] at h1
    have := algebraMap_mem_maximalIdeal_pow_iff.1 hL
    have : (2 : ℕ∞) ≤ 1 := this.trans h1
    norm_num at this

/-- **Embedding dimension of a plane curve at a point** (Problems 3.13 and 3.24(a)). Let
`F ∈ k[X, Y]`, `P ∈ k²`, `𝒪 = 𝒪_P(𝔸²) ⧸ (F)` (the local ring of the curve `F` at `P`; for
irreducible `F` it is `𝒪_P(F)`, by `AffineSpace.localRing.quotient_iso`) and `𝔪` the image in `𝒪`
of the maximal ideal of `𝒪_P(𝔸²)`, which is the maximal ideal of `𝒪` when `F(P) = 0`.

* `dim_k 𝔪ⁿ / 𝔪ⁿ⁺¹ = n + 1` for `0 ≤ n < m_P(F)`;
* `dim_k 𝔪 / 𝔪² = 1` if `P` is a simple point of `F`, and `2` if it is a multiple point;
* if `m_0(F) > 1`, the linear forms `aX + bY` map isomorphically onto `𝔪 / 𝔪²` at `P = 0`.

Milestone: *Embedding dimension of a plane curve at a point*. -/
theorem finrank_gradedPiece_of_lt_orderAt_and_exists_linearEquiv (F : MvPolynomial (Fin 2) k)
    (P : Fin 2 → k) :
    (∀ n : ℕ, (n : ℕ∞) < F.orderAt P →
      finrank k (((maximalIdeal (localRing k P)).map (Ideal.Quotient.mk
        (span {algebraMap _ (localRing k P) F}))).GradedPiece n) = n + 1) ∧
    (IsSimplePoint F P → finrank k (((maximalIdeal (localRing k P)).map (Ideal.Quotient.mk
        (span {algebraMap _ (localRing k P) F}))).GradedPiece 1) = 1) ∧
    (IsMultiplePoint F P → finrank k (((maximalIdeal (localRing k P)).map (Ideal.Quotient.mk
        (span {algebraMap _ (localRing k P) F}))).GradedPiece 1) = 2) ∧
    (2 ≤ F.orderAt 0 →
      ∃ e : homogeneousSubmodule (Fin 2) k 1 ≃ₗ[k]
          ((maximalIdeal (localRing k (0 : Fin 2 → k))).map (Ideal.Quotient.mk
            (span {algebraMap _ (localRing k (0 : Fin 2 → k)) F}))).GradedPiece 1,
        ∀ (L : homogeneousSubmodule (Fin 2) k 1) (x : ↥((maximalIdeal
            (localRing k (0 : Fin 2 → k))).map (Ideal.Quotient.mk
              (span {algebraMap _ (localRing k (0 : Fin 2 → k)) F})) ^ 1)),
          (x : localRing k 0 ⧸ span {algebraMap _ (localRing k (0 : Fin 2 → k)) F}) =
            Ideal.Quotient.mk _ (algebraMap _ _ (L : MvPolynomial (Fin 2) k)) →
          e L = Submodule.Quotient.mk x) :=
  ⟨fun _ ↦ finrank_gradedPiece_of_lt_orderAt, IsSimplePoint.finrank_gradedPiece_one,
    IsMultiplePoint.finrank_gradedPiece_one, exists_linearEquiv_gradedPiece_one⟩

/-- **Multiplicity of a plane curve is determined by its local ring** (Theorem 2 of §3.2). Let
`F ∈ k[X, Y]` and `P ∈ k²` with `m = m_P(F)` finite (that is, `F ≠ 0`), `𝒪 = 𝒪_P(𝔸²) ⧸ (F)` (the
local ring of the curve `F` at `P`; for irreducible `F` it is `𝒪_P(F)`, by
`AffineSpace.localRing.quotient_iso`) and `𝔪` the image in `𝒪` of the maximal ideal of `𝒪_P(𝔸²)`,
which is the maximal ideal of `𝒪` when `F(P) = 0`.

* `dim_k 𝔪ⁿ / 𝔪ⁿ⁺¹ = m` for all `n ≥ m - 1`, in particular for `n ≥ m`;
* `dim_k 𝒪 / 𝔪ⁿ = n m - m (m - 1) / 2` for all `n ≥ m`;
* if `F(P) = 0`, `G(Q) = 0` and `𝒪 ≅ 𝒪_Q(𝔸²) ⧸ (G)` as rings, then `m_Q(G) = m`.

The general formula `dim_k 𝔪ⁿ / 𝔪ⁿ⁺¹ = min (n + 1, m_P(F))` is `finrank_gradedPiece`.

Milestone: *Multiplicity of a plane curve is determined by its local ring*. -/
theorem finrank_gradedPiece_and_finrank_quotient_pow_and_orderAt_eq_of_ringEquiv {m : ℕ}
    (hm : F.orderAt P = m) :
    (∀ n : ℕ, m ≤ n + 1 →
      finrank k (((maximalIdeal (localRing k P)).map (Ideal.Quotient.mk
        (span {algebraMap _ (localRing k P) F}))).GradedPiece n) = m) ∧
    (∀ n : ℕ, m ≤ n →
      finrank k ((localRing k P ⧸ span {algebraMap _ (localRing k P) F}) ⧸
        (maximalIdeal (localRing k P)).map (Ideal.Quotient.mk _) ^ n) =
        n * m - m * (m - 1) / 2) ∧
    (eval P F = 0 → ∀ (G : MvPolynomial (Fin 2) k) (Q : Fin 2 → k), eval Q G = 0 →
      Nonempty ((localRing k P ⧸ span {algebraMap _ (localRing k P) F}) ≃+*
        (localRing k Q ⧸ span {algebraMap _ (localRing k Q) G})) → G.orderAt Q = m) :=
  ⟨fun _ ↦ finrank_gradedPiece_of_orderAt_le hm, fun _ ↦ finrank_quotient_pow_of_orderAt_le hm,
    fun hF _ _ hG ⟨e⟩ ↦ (orderAt_eq_of_ringEquiv hF hG e).symm.trans hm⟩

end Affine

end PlaneCurves
