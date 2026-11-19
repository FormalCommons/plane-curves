/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import PlaneCurves.Algebra.MvPolynomial.SetVarZero
public import PlaneCurves.RingTheory.MvPolynomial.Homogenize.Ideal
public import PlaneCurves.RingTheory.MvPolynomial.HilbertFunction
public import PlaneCurves.RingTheory.Regular.IsRelPrime
public import TauCeti.RingTheory.GradedAlgebra.HilbertSeries.RegularSequence
public import TauCeti.RingTheory.MvPolynomial.Finrank
import Mathlib.Tactic.LinearCombination

/-!
# The quotient of a polynomial ring by two coprime polynomials

Let `k` be a field and `R = k[X_i : i ∈ σ]`. This file proves the three algebraic facts about
`Γ = R/(F, G)` on which Fulton's proof of Bézout's theorem rests (Fulton, §5.3).

* **Step 1.** If `F` and `G` are coprime forms of degrees `m` and `n` in `k[X, Y, Z]`, then
  `dim_k Γ_d = mn` for every `d ≥ m + n - 2`. Coprimality makes `F, G` a regular sequence, which
  is what makes Fulton's sequence `0 → R_{d-m-n} → R_{d-m} × R_{d-n} → R_d → Γ_d → 0` exact; the
  dimension count is Tau Ceti's Hilbert series of a quotient by a homogeneous regular sequence,
  `H_Γ(t) = H_R(t) (1 - t^m) (1 - t^n)`.
* **Step 2.** If `F` and `G` become coprime when the variable `X i` is set to zero, then
  multiplication by `X i` is injective on `Γ`: `X i * H ∈ (F, G)` implies `H ∈ (F, G)`. Neither
  homogeneity nor finiteness of `σ` is needed.
* **Step 3.** If moreover `F` and `G` are coprime forms of degrees `m` and `n` in `k[X, Y, Z]`,
  then dehomogenizing at `X i = 1` identifies `Γ_d` with `k[X, Y]/(F_*, G_*)` for `d ≥ m + n`,
  so `dim_k k[X, Y]/(F_*, G_*) = mn`.

## Main results

* `MvPolynomial.finrank_quotientPiece_span_pair_fin_three`: Step 1.
* `MvPolynomial.X_mul_mem_span_pair_iff`: Step 2.
* `MvPolynomial.mem_span_pair_of_dehomogenize_mem`: a form whose dehomogenization lies in
  `(F_*, G_*)` lies in `(F, G)`, under the hypothesis of Step 2.
* `MvPolynomial.finrank_quotient_span_pair_dehomogenize`: Step 3.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.3
-/

public section

open TauCeti TauCeti.GradedAlgebra

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {σ k : Type*} [Field k]

/-- Twice the number of monomials of degree `d - j` in three variables, read as `0` when
`d < j`, is `(d - j + 2)(d - j + 1)` whenever `j ≤ d + 2`. -/
private theorem two_mul_ite_multichoose_three {d j : ℕ} (hj : j ≤ d + 2) :
    2 * (if j ≤ d then ((3 : ℕ).multichoose (d - j) : ℤ) else 0) =
      ((d : ℤ) - j + 2) * ((d : ℤ) - j + 1) := by
  split_ifs with h
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
    have h₂ := Nat.two_mul_multichoose_three e
    rw [Nat.add_sub_cancel_left]
    have := congrArg (fun x : ℕ ↦ (x : ℤ)) h₂
    push_cast at this ⊢
    linear_combination this
  · obtain ⟨i, hi, rfl⟩ : ∃ i : ℕ, i < 2 ∧ j = d + 1 + i := ⟨j - d - 1, by omega, by omega⟩
    interval_cases i <;> push_cast <;> ring

/-- **Step 1 of Fulton's proof of Bézout's theorem.** If `F` and `G` are coprime forms of degrees
`m` and `n` in `k[X, Y, Z]`, then the degree-`d` piece of `k[X, Y, Z]/(F, G)` has dimension `mn`
for every `d ≥ m + n - 2`. -/
theorem finrank_quotientPiece_span_pair_fin_three {F G : MvPolynomial (Fin 3) k} {m n d : ℕ}
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) (hFG : IsRelPrime F G)
    (hd : m + n ≤ d + 2) :
    Module.finrank k (quotientPiece (homogeneousSubmodule (Fin 3) k) (Ideal.span {F, G}) d) =
      m * n := by
  have hc := finrank_quotientPiece_span_pair hF hG hFG d
  simp only [Fintype.card_fin] at hc
  have h₀ := two_mul_ite_multichoose_three (d := d) (j := 0) (by omega)
  have h₁ := two_mul_ite_multichoose_three (d := d) (j := m) (by omega)
  have h₂ := two_mul_ite_multichoose_three (d := d) (j := n) (by omega)
  have h₃ := two_mul_ite_multichoose_three (d := d) (j := m + n) (by omega)
  simp only [zero_le, ite_true, Nat.sub_zero] at h₀
  have : (Module.finrank k (quotientPiece (homogeneousSubmodule (Fin 3) k)
      (Ideal.span {F, G}) d) : ℤ) = m * n := by
    refine mul_left_cancel₀ (two_ne_zero (α := ℤ)) ?_
    push_cast at h₀ h₃
    linear_combination 2 * hc + h₀ - h₁ - h₂ + h₃
  exact_mod_cast this

/-- **Step 2 of Fulton's proof of Bézout's theorem.** If the polynomials `F` and `G` stay coprime
when the variable `X i` is set to zero, then multiplication by `X i` is injective on
`k[X]/(F, G)`: `X i * H ∈ (F, G)` if and only if `H ∈ (F, G)`. For forms `F`, `G` in
`k[X, Y, Z]` and `X i = Z` the hypothesis says that `F(X, Y, 0)` and `G(X, Y, 0)` are coprime. -/
theorem X_mul_mem_span_pair_iff [DecidableEq σ] {i : σ} {F G H : MvPolynomial σ k}
    (hFG : IsRelPrime (bind₁ (Function.update X i 0) F) (bind₁ (Function.update X i 0) G)) :
    X i * H ∈ Ideal.span {F, G} ↔ H ∈ Ideal.span {F, G} := by
  refine ⟨fun h ↦ ?_, fun h ↦ Ideal.mul_mem_left _ _ h⟩
  set φ := bind₁ (Function.update X i (0 : MvPolynomial σ k))
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp h
  have hφ : φ a * φ F + φ b * φ G = 0 := by
    simpa [φ] using congrArg φ hab
  obtain ⟨c, hac, hbc⟩ := hFG.exists_eq_mul_of_mul_add_mul_eq_zero hφ
  have hac' : φ a = φ G * φ c := by
    simpa [φ] using congrArg φ hac
  have hbc' : φ b = -(φ F * φ c) := by
    simpa [φ] using congrArg φ hbc
  have hφφ (p : MvPolynomial σ k) : φ (φ p) = φ p := bind₁_update_X_zero_bind₁_update_X_zero i p
  obtain ⟨a', ha'⟩ : X i ∣ a - φ c * G := X_dvd_of_bind₁_update_X_zero_eq_zero <| by
    change φ _ = 0
    rw [map_sub, map_mul, hφφ, hac']
    ring
  obtain ⟨b', hb'⟩ : X i ∣ b + φ c * F := X_dvd_of_bind₁_update_X_zero_eq_zero <| by
    change φ _ = 0
    rw [map_add, map_mul, hφφ, hbc']
    ring
  have hH : X i * H = X i * (a' * F + b' * G) := by
    rw [← hab]
    linear_combination F * ha' + G * hb'
  rw [mul_left_cancel₀ (X_ne_zero i) hH]
  exact Ideal.mem_span_pair.mpr ⟨a', b', rfl⟩

/-- Under the hypothesis of Step 2 for `X i`, a form `H` whose dehomogenization `H_*` lies in
`(F_*, G_*)`, for forms `F` and `G`, lies in `(F, G)`. -/
theorem mem_span_pair_of_dehomogenize_mem {n : ℕ} {i : Fin (n + 1)}
    {F G H : MvPolynomial (Fin (n + 1)) k} {m e d : ℕ} (hF : F.IsHomogeneous m)
    (hG : G.IsHomogeneous e) (hH : H.IsHomogeneous d)
    (hFG : IsRelPrime (bind₁ (Function.update X i 0) F) (bind₁ (Function.update X i 0) G))
    (h : dehomogenize i H ∈ Ideal.span {dehomogenize i F, dehomogenize i G}) :
    H ∈ Ideal.span {F, G} := by
  obtain ⟨r, hr⟩ := exists_X_pow_mul_mem_span_pair_of_dehomogenize_mem hF hG hH h
  induction r with
  | zero => simpa using hr
  | succ r ih => exact ih ((X_mul_mem_span_pair_iff hFG).1 (by rwa [pow_succ', mul_assoc] at hr))

/-- **Step 3 of Fulton's proof of Bézout's theorem.** Let `F` and `G` be coprime forms of degrees
`m` and `n` in `k[X, Y, Z]` that stay coprime when the variable `X i` is set to zero. Then the
dehomogenizations `F_*` and `G_*` at `X i = 1` satisfy `dim_k k[X, Y]/(F_*, G_*) = mn`.
Dehomogenizing maps `Γ_d` injectively into `k[X, Y]/(F_*, G_*)` (Step 2), the images increase
with `d`, they have dimension `mn` for `d ≥ m + n` (Step 1), and every class is in one of them. -/
theorem finrank_quotient_span_pair_dehomogenize {F G : MvPolynomial (Fin 3) k} {m n : ℕ}
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) (hFG : IsRelPrime F G) {i : Fin 3}
    (hi : IsRelPrime (bind₁ (Function.update X i 0) F) (bind₁ (Function.update X i 0) G)) :
    Module.finrank k (MvPolynomial (Fin 2) k ⧸
      Ideal.span {dehomogenize i F, dehomogenize i G}) = m * n := by
  classical
  set J := Ideal.span {dehomogenize i F, dehomogenize i G}
  set I := Ideal.span {F, G}
  have hIJ : I ≤ J.comap (dehomogenize i) := Ideal.span_le.2 <| by
    rintro _ (rfl | rfl)
    exacts [Ideal.subset_span (by simp), Ideal.subset_span (by simp)]
  set ψ := (Ideal.quotientMapₐ J (dehomogenize i) hIJ).toLinearMap
  set W : ℕ → Submodule k (MvPolynomial (Fin 2) k ⧸ J) := fun d ↦
    (quotientPiece (homogeneousSubmodule (Fin 3) k) I d).map ψ
  have hp {d : ℕ} {x : MvPolynomial (Fin 3) k ⧸ I} :
      x ∈ quotientPiece (homogeneousSubmodule (Fin 3) k) I d ↔
        ∃ H, H.IsHomogeneous d ∧ Ideal.Quotient.mk I H = x := by
    rw [quotientPiece_def, Submodule.mem_map]
    rfl
  have hW {d : ℕ} {H : MvPolynomial (Fin 3) k} (hH : H.IsHomogeneous d) :
      Ideal.Quotient.mk J (dehomogenize i H) ∈ W d :=
    ⟨Ideal.Quotient.mk I H, hp.2 ⟨H, hH, rfl⟩, rfl⟩
  have hmono : Monotone W := by
    refine monotone_nat_of_le_succ fun d ↦ ?_
    rintro _ ⟨_, hx, rfl⟩
    obtain ⟨H, hH, rfl⟩ := hp.1 hx
    have h := hW (d := d + 1) (by simpa [add_comm] using (isHomogeneous_X k i).mul hH)
    simpa [ψ] using h
  have hrank {d : ℕ} (hd : m + n ≤ d + 2) : Module.finrank k (W d) = m * n := by
    set p := quotientPiece (homogeneousSubmodule (Fin 3) k) I d
    have hinj : Function.Injective (ψ ∘ₗ p.subtype) := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      rintro ⟨_, hx'⟩ hx
      obtain ⟨H, hH, rfl⟩ := hp.1 hx'
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
        Submodule.coe_subtype] at hx
      have : dehomogenize i H ∈ J := Ideal.Quotient.eq_zero_iff_mem.1 hx
      simpa [Submodule.mem_bot, Subtype.ext_iff] using
        Ideal.Quotient.eq_zero_iff_mem.2 (mem_span_pair_of_dehomogenize_mem hF hG hH hi this)
    rw [← finrank_quotientPiece_span_pair_fin_three hF hG hFG hd,
      (LinearEquiv.ofInjective _ hinj).finrank_eq, LinearMap.range_comp,
      Submodule.range_subtype]
  have hconst (j : ℕ) : W (m + n + j) = W (m + n) :=
    (Submodule.eq_of_le_of_finrank_eq (hmono (by omega))
      (by rw [hrank (by omega), hrank (by omega)])).symm
  have htop : W (m + n) = ⊤ := by
    refine eq_top_iff.2 fun a _ ↦ ?_
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective a
    have ha := hW (isHomogeneous_homogenize i h.totalDegree h)
    rw [dehomogenize_homogenize le_rfl] at ha
    exact hconst h.totalDegree ▸ hmono (by omega) ha
  rw [← finrank_top, ← htop, hrank (by omega)]

end MvPolynomial

end
