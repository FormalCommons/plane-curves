/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Moving a point and a line through it to standard position

For a nonzero vector `p ∈ k³` and a nonzero linear form `t` with `t(p) = 0`, there is an
invertible matrix `M` with `M e₂ = p` and `t ∘ M = e₁*`. As a projective change of coordinates,
`M` sends `[0 : 0 : 1]` to `[p]` and the line `Y = 0` to the line `t = 0`, which passes through
`[p]`. This is how a simple point of a plane curve and its tangent are put in the position
`[0 : 0 : 1]`, `Y = 0` ([Fulton2008], §5.3, Problem 5.23).

## Main results

* `Matrix.exists_mulVec_single_eq_and_vecMul_eq_single`: such an `M` exists.

## References

* [W. Fulton, *Algebraic Curves: An Introduction to Algebraic Geometry*][Fulton2008], §5.3
-/

public section

open scoped Matrix.GeneralLinearGroup

namespace Matrix

variable {k : Type*} [Field k]

/-- **A point and a line through it in standard position.** For a nonzero `p ∈ k³` and a nonzero
`t ∈ k³` with `t ⬝ᵥ p = 0`, some invertible `M` has last column `p` and `t ᵥ* M = e₁`: the
projective change of coordinates `M` sends `[0 : 0 : 1]` to `[p]`, and the line
`t₀ X + t₁ Y + t₂ Z = 0` to `Y = 0`. -/
theorem exists_mulVec_single_eq_and_vecMul_eq_single {t p : Fin 3 → k} (ht : t ≠ 0) (hp : p ≠ 0)
    (htp : t ⬝ᵥ p = 0) :
    ∃ M : GL (Fin 3) k, M.1 *ᵥ Pi.single 2 1 = p ∧ t ᵥ* M.1 = Pi.single 1 1 := by
  obtain ⟨i, hi⟩ : ∃ i, t i ≠ 0 := by
    by_contra! h
    exact ht (funext h)
  set φ : (Fin 3 → k) →ₗ[k] k := dotProductBilin k k t
  have hφ (x) : φ x = t ⬝ᵥ x := rfl
  set u₁ : Fin 3 → k := Pi.single i (t i)⁻¹
  have hu₁ : t ⬝ᵥ u₁ = 1 := by simp [u₁, hi]
  have hker : Module.finrank k (LinearMap.ker φ) = 2 := by
    have hr : LinearMap.range φ = ⊤ :=
      LinearMap.range_eq_top.2 fun c ↦ ⟨c • u₁, by simp [hφ, hu₁]⟩
    have := LinearMap.finrank_range_add_finrank_ker φ
    rw [hr, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at this
    omega
  obtain ⟨u₀, hu₀, hu₀p⟩ : ∃ u₀ ∈ LinearMap.ker φ, u₀ ∉ Submodule.span k {p} := by
    by_contra! h
    have := Submodule.finrank_mono (show LinearMap.ker φ ≤ Submodule.span k {p} from h)
    rw [hker, finrank_span_singleton hp] at this
    omega
  rw [LinearMap.mem_ker, hφ] at hu₀
  set M : Matrix (Fin 3) (Fin 3) k := Matrix.of fun r c ↦ ![u₀, u₁, p] c r
  have hM (g : Fin 3 → k) : M *ᵥ g = g 0 • u₀ + g 1 • u₁ + g 2 • p := by
    funext r
    simp [M, mulVec, dotProduct, Fin.sum_univ_three]
    ring
  have hMu : IsUnit M := by
    rw [← mulVec_injective_iff_isUnit]
    intro g g' h
    have h0 : M *ᵥ (g - g') = 0 := by rw [mulVec_sub, h, sub_self]
    rw [hM] at h0
    set d := g - g' with hd
    have h1 : d 1 = 0 := by
      simpa [dotProduct_add, dotProduct_smul, hu₀, hu₁, htp] using congrArg (t ⬝ᵥ ·) h0
    rw [h1, zero_smul, add_zero] at h0
    have h0' : d 0 = 0 := by
      by_contra hd0
      refine hu₀p (Submodule.mem_span_singleton.2 ⟨-(d 0)⁻¹ * d 2, ?_⟩)
      have : u₀ = (d 0)⁻¹ • (d 0 • u₀) := by rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
      rw [this, eq_neg_of_add_eq_zero_left h0, smul_neg, smul_smul, neg_mul, neg_smul]
    rw [h0', zero_smul, zero_add, smul_eq_zero] at h0
    have h2 := h0.resolve_right hp
    rw [← sub_eq_zero, ← hd]
    funext j
    fin_cases j <;> simp [h0', h1, h2]
  have hv (c) : (t ᵥ* M) c = t ⬝ᵥ ![u₀, u₁, p] c := by simp [M, vecMul, dotProduct]
  refine ⟨hMu.unit, ?_, ?_⟩
  · simp [hM]
  · funext c
    rw [IsUnit.unit_spec, hv]
    fin_cases c <;> simp [hu₀, hu₁, htp]

end Matrix

end
