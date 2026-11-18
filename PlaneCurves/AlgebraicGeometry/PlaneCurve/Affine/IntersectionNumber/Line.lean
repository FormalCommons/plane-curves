/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.RingTheory.MvPolynomial.LineRestriction
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.IntersectionNumber.Additivity
public import PlaneCurves.RingTheory.MvPolynomial.LinearSubst
public import PlaneCurves.RingTheory.MvPolynomial.Taylor

/-!
# The intersection of a plane curve with a line

Let `L` be the line through `a ∈ k²` with direction `v ≠ 0`, the points `a + t v`, with equation
`ℓ = v₁ (X - a₀) - v₀ (Y - a₁)`, and let `F` be a plane curve of which `L` is not a component.
The restriction `G(T) = F(a + T v) ∈ k[T]` of `F` to `L` is then nonzero, its roots `t` are the
parameters of the points of `L ∩ V(F)`, and the intersection number of `L` and `F` at `a + t v`
is the multiplicity of `t` as a root of `G` (Problem 3.21 of Fulton). So the intersection
numbers of `L` and `F` add up to the number of roots of `G`, which is at most `deg F`, and is
`deg G` when `k` is algebraically closed.

The restriction is written `aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) *
Polynomial.X) F`, as in Tau Ceti's `TauCeti/RingTheory/MvPolynomial/LineRestriction.lean`.

## Main results

* `PlaneCurves.Affine.aeval_line_eq_zero_iff`: `G = 0` iff `ℓ ∣ F`.
* `PlaneCurves.Affine.bijOn_line`: `t ↦ a + t v` is a bijection from the roots of `G` onto
  `V(ℓ) ∩ V(F)`.
* `PlaneCurves.Affine.intersectionNumber_line_eq_rootMultiplicity`:
  `I(a + t v, ℓ ∩ F) = rootMultiplicity t G`.
* `PlaneCurves.Affine.finsum_intersectionNumber_line`: `∑_P I(P, ℓ ∩ F)` is the number of roots
  of `G`, counted with multiplicity.
* `PlaneCurves.Affine.intersectionNumber_line_eq_rootMultiplicity_and_finsum_eq`: Problem 3.21.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §3.3, Problem 3.21
-/

public section

open MvPolynomial

namespace PlaneCurves.Affine

variable {k : Type*} [Field k] {a v : Fin 2 → k} {F : MvPolynomial (Fin 2) k}

/-- `H - H(X, 0)` is divisible by `Y`. -/
private theorem X_one_dvd_sub_aeval (H : MvPolynomial (Fin 2) k) :
    X 1 ∣ H - aeval ![X 0, 0] H := by
  induction H using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add, add_sub_add_comm]; exact dvd_add hp hq
  | mul_X p n hp =>
    rw [map_mul, aeval_X, show p * X n - aeval ![X 0, 0] p * ![X 0, 0] n =
      (p - aeval ![X 0, 0] p) * X n + aeval ![X 0, 0] p * (X n - ![X 0, 0] n) by ring]
    refine dvd_add (hp.mul_right _) (Dvd.dvd.mul_left ?_ _)
    fin_cases n <;> simp

/-- A change of coordinates of `𝔸²` that carries the line through `a` with direction `v` to the
axis `Y = 0`, with `(t, 0) ↦ a + t v`. -/
private theorem exists_algEquiv_line (hv : v ≠ 0) :
    ∃ (ψ : MvPolynomial (Fin 2) k ≃ₐ[k] MvPolynomial (Fin 2) k) (u : k), u ≠ 0 ∧
      (∀ (t : k) (g : MvPolynomial (Fin 2) k), eval ![t, 0] (ψ g) = eval (a + t • v) g) ∧
      ψ (C (v 1) * (X 0 - C (a 0)) - C (v 0) * (X 1 - C (a 1))) = C u * X 1 ∧
      ∀ g : MvPolynomial (Fin 2) k, aeval ![(X 0 : MvPolynomial (Fin 2) k), 0] (ψ g) =
        Polynomial.aeval (X 0)
          (aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) g) := by
  obtain ⟨w, hw⟩ : ∃ w : Fin 2 → k, v 0 * w 1 - w 0 * v 1 ≠ 0 := by
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := fun h1 ↦ hv (funext fun i ↦ by fin_cases i <;> simp [h0, h1])
      exact ⟨![1, 0], by simpa [h0] using h1⟩
    · exact ⟨![0, 1], by simpa using h0⟩
  let M := Matrix.GeneralLinearGroup.mkOfDetNeZero !![v 0, w 0; v 1, w 1]
    (by simpa [Matrix.det_fin_two] using hw)
  let ψ := (taylorAlgEquiv a).trans (linearSubstAlgEquiv M)
  have hψ (g) : ψ g = linearSubst M.1 (taylor a g) := by simp [ψ, taylorAlgEquiv_apply]
  have hC (c : k) : ψ (C c) = C c := ψ.commutes c
  have hX (i) : ψ (X i) = C (v i) * X 0 + C (w i) * X 1 + C (a i) := by
    rw [hψ, taylor_X, map_add, linearSubst_X, Fin.sum_univ_two, ← algebraMap_eq,
      AlgHom.commutes, algebraMap_eq]
    fin_cases i <;> simp [M, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  refine ⟨ψ, v 1 * w 0 - v 0 * w 1, fun h ↦ hw (by linear_combination -h), fun t g ↦ ?_, ?_,
    fun g ↦ ?_⟩
  · have hM : (M : Matrix (Fin 2) (Fin 2) k).mulVec ![t, 0] + a = a + t • v := by
      funext i
      fin_cases i <;> simp [M, Matrix.GeneralLinearGroup.mkOfDetNeZero] <;> ring
    rw [hψ, eval_linearSubst, eval_taylor, hM]
  · simp only [map_sub, map_mul, hC, hX]
    ring
  · have h : (aeval ![(X 0 : MvPolynomial (Fin 2) k), 0]).comp ψ.toAlgHom =
        (Polynomial.aeval (X 0)).comp
          (aeval fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) :=
      MvPolynomial.algHom_ext fun i ↦ by fin_cases i <;> simp [hX, add_comm]
    exact congr($h g)

/-- The restriction of `F` to the line through `a` with direction `v ≠ 0` vanishes iff the line
`v₁ (X - a₀) - v₀ (Y - a₁)` divides `F`. -/
theorem aeval_line_eq_zero_iff (hv : v ≠ 0) :
    aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) F = 0 ↔
      C (v 1) * (X 0 - C (a 0)) - C (v 0) * (X 1 - C (a 1)) ∣ F := by
  refine ⟨fun h ↦ ?_, fun ⟨A, hA⟩ ↦ ?_⟩
  · obtain ⟨ψ, u, hu, -, hℓ, hG⟩ := exists_algEquiv_line (a := a) hv
    have h1 := X_one_dvd_sub_aeval (ψ F)
    rw [hG, h, map_zero, sub_zero] at h1
    have h2 : ψ (C (v 1) * (X 0 - C (a 0)) - C (v 0) * (X 1 - C (a 1))) ∣ ψ F := by
      rw [hℓ]
      exact Dvd.dvd.trans
        ⟨C u⁻¹, by rw [mul_right_comm, ← C_mul, mul_inv_cancel₀ hu, C_1, one_mul]⟩ h1
    simpa using map_dvd ψ.symm h2
  · rw [hA, map_mul]
    convert zero_mul _
    simp only [map_sub, map_mul, aeval_X, aeval_C, Polynomial.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply]
    ring

/-- `t ↦ a + t v` maps the roots of the restriction `G` of `F` to the line through `a` with
direction `v ≠ 0` bijectively onto the points of `F` on the line
`v₁ (X - a₀) - v₀ (Y - a₁) = 0`. -/
theorem bijOn_line (hv : v ≠ 0) (F : MvPolynomial (Fin 2) k) :
    Set.BijOn (fun t : k ↦ a + t • v)
      {t | (aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) F).IsRoot t}
      {P | eval P (C (v 1) * (X 0 - C (a 0)) - C (v 0) * (X 1 - C (a 1))) = 0 ∧
        eval P F = 0} := by
  refine ⟨fun t ht ↦ ⟨?_, by simpa using ht⟩, fun s _ t _ h ↦ ?_, fun P ⟨hP, hF⟩ ↦ ?_⟩
  · simp only [map_sub, map_mul, eval_C, eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · exact smul_left_injective k hv (add_left_cancel h)
  · simp only [map_sub, map_mul, eval_C, eval_X] at hP
    have key : ∃ t : k, P = a + t • v := by
      by_cases h0 : v 0 = 0
      · have h1 : v 1 ≠ 0 := fun h1 ↦ hv (funext fun i ↦ by fin_cases i <;> simp [h0, h1])
        refine ⟨(P 1 - a 1) / v 1, funext fun i ↦ ?_⟩
        have : P 0 = a 0 := by
          simpa [h0, h1, sub_eq_zero] using hP
        fin_cases i
        · simpa [h0] using this
        · simp [h1]
      · refine ⟨(P 0 - a 0) / v 0, funext fun i ↦ ?_⟩
        fin_cases i
        · simp; field_simp; ring
        · simp; field_simp; linear_combination -hP
    obtain ⟨t, rfl⟩ := key
    exact ⟨t, by simpa using hF, rfl⟩

/-- **Intersection number with a line as a root multiplicity.** If the restriction
`G(T) = F(a + T v)` of `F` to the line through `a` with direction `v ≠ 0` is nonzero, then for
every `t`, `I(a + t v, ℓ ∩ F) = rootMultiplicity t G`, with `ℓ = v₁ (X - a₀) - v₀ (Y - a₁)`. -/
theorem intersectionNumber_line_eq_rootMultiplicity (hv : v ≠ 0)
    (hF : aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) F ≠ 0) (t : k) :
    intersectionNumber (a + t • v) (C (v 1) * (X 0 - C (a 0)) - C (v 0) * (X 1 - C (a 1))) F =
      (aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) F).rootMultiplicity
        t := by
  obtain ⟨ψ, u, hu, hev, hℓ, hG⟩ := exists_algEquiv_line (a := a) hv
  set G := aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) F
  obtain ⟨A, hA⟩ := X_one_dvd_sub_aeval (ψ F)
  obtain ⟨q, hq, hqt⟩ := G.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hF t
  set e := G.rootMultiplicity t
  have hqt' : eval ![t, 0] (Polynomial.aeval (X 0) q) ≠ 0 := by
    have h : ∀ p : Polynomial k, eval ![t, 0] (Polynomial.aeval (X 0) p) = p.eval t := by
      intro p
      induction p using Polynomial.induction_on' with
      | add p q hp hq => simp [hp, hq]
      | monomial n c => simp
    rw [h]
    simpa [Polynomial.dvd_iff_isRoot] using hqt
  rw [← intersectionNumber_algEquiv ψ (hev t), hℓ, mul_comm,
    intersectionNumber_mul_left_of_eval_ne_zero (by simpa using hu),
    show ψ F = Polynomial.aeval (X 0) G + A * X 1 by rw [← hG]; linear_combination hA,
    intersectionNumber_add_mul, hq, map_mul, map_pow, intersectionNumber_mul_right,
    intersectionNumber_eq_zero_of_eval_ne_zero_right hqt', intersectionNumber_pow_right,
    intersectionNumber_comm]
  have h1 := intersectionNumber_X_sub_C_X_sub_C (k := k) ![t, 0]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, C_0,
    sub_zero] at h1
  simp [h1]

/-- If the restriction `G` of `F` to the line through `a` with direction `v ≠ 0` is nonzero, the
intersection numbers of `ℓ = v₁ (X - a₀) - v₀ (Y - a₁)` and `F` add up to the number of roots of
`G`, counted with multiplicity. -/
theorem finsum_intersectionNumber_line (hv : v ≠ 0)
    (hF : aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) F ≠ 0) :
    ∑ᶠ P, intersectionNumber P (C (v 1) * (X 0 - C (a 0)) - C (v 0) * (X 1 - C (a 1))) F =
      (aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) F).roots.card := by
  classical
  set G := aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) F
  have hsupp : Function.support (fun P ↦ intersectionNumber P
      (C (v 1) * (X 0 - C (a 0)) - C (v 0) * (X 1 - C (a 1))) F) ⊆
      (G.roots.toFinset.image fun t ↦ a + t • v : Finset (Fin 2 → k)) := by
    intro P hP
    have hP' : eval P (C (v 1) * (X 0 - C (a 0)) - C (v 0) * (X 1 - C (a 1))) = 0 ∧
        eval P F = 0 := by simpa [intersectionNumber_eq_zero_iff] using hP
    obtain ⟨t, ht, rfl⟩ := (bijOn_line hv F).surjOn hP'
    simpa [Polynomial.mem_roots hF] using ⟨t, ht, rfl⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp,
    Finset.sum_image fun s _ t _ h ↦ smul_left_injective k hv (add_left_cancel h)]
  simp_rw [intersectionNumber_line_eq_rootMultiplicity hv hF, ← Polynomial.count_roots]
  rw [← Nat.cast_sum, Multiset.toFinset_sum_count_eq]

/-- **Intersection of a plane curve with a line** (Problem 3.21). Let `L` be the line through
`a ∈ k²` with direction `v ≠ 0`, with equation `ℓ = v₁ (X - a₀) - v₀ (Y - a₁)`, and let `F` be a
plane curve of which `L` is not a component (`¬ ℓ ∣ F`). Put `G(T) = F(a + T v)`. Then

1. `G ≠ 0`;
2. `t ↦ a + t v` is a bijection from the roots of `G` onto `L ∩ V(F)`;
3. `I(a + t v, L ∩ F) = rootMultiplicity t G` for every `t`;
4. `∑_P I(P, L ∩ F)` is the number of roots of `G` with multiplicity, and `deg G ≤ deg F`;
5. if `k` is algebraically closed, `∑_P I(P, L ∩ F) = deg G`.

Milestone: *Intersection of a plane curve with a line*. -/
theorem intersectionNumber_line_eq_rootMultiplicity_and_finsum_eq (hv : v ≠ 0)
    (hF : ¬ C (v 1) * (X 0 - C (a 0)) - C (v 0) * (X 1 - C (a 1)) ∣ F) :
    aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) F ≠ 0 ∧
    Set.BijOn (fun t : k ↦ a + t • v)
      {t | (aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) F).IsRoot t}
      {P | eval P (C (v 1) * (X 0 - C (a 0)) - C (v 0) * (X 1 - C (a 1))) = 0 ∧
        eval P F = 0} ∧
    (∀ t : k, intersectionNumber (a + t • v)
      (C (v 1) * (X 0 - C (a 0)) - C (v 0) * (X 1 - C (a 1))) F =
      (aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) F).rootMultiplicity
        t) ∧
    ∑ᶠ P, intersectionNumber P (C (v 1) * (X 0 - C (a 0)) - C (v 0) * (X 1 - C (a 1))) F =
      (aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) F).roots.card ∧
    (aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) F).natDegree ≤
      F.totalDegree ∧
    (IsAlgClosed k →
      ∑ᶠ P, intersectionNumber P (C (v 1) * (X 0 - C (a 0)) - C (v 0) * (X 1 - C (a 1))) F =
        (aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) F).natDegree) := by
  have hG := mt (aeval_line_eq_zero_iff hv).1 hF
  refine ⟨hG, bijOn_line hv F, intersectionNumber_line_eq_rootMultiplicity hv hG,
    finsum_intersectionNumber_line hv hG, ?_, fun _ ↦ ?_⟩
  · simpa [aeval_def, Polynomial.algebraMap_eq] using
      natDegree_eval₂_C_add_C_mul_X_le F (RingHom.id k) a v
  · rw [finsum_intersectionNumber_line hv hG, IsAlgClosed.card_roots_eq_natDegree]

end PlaneCurves.Affine

end
