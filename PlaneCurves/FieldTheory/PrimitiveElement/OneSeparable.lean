/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.FieldTheory.PrimitiveElement

/-!
# Primitive elements of `F(α, β)` with only `β` separable

The classical proof of the primitive element theorem shows that `F(α, β) = F(α + cβ)` for
all but finitely many `c ∈ F` when `F` is infinite. It uses the separability of `β` only:
`α` need only be algebraic. This file proves that form of the theorem, for any field `F`.

## Main results

* `Field.exists_adjoin_pair_eq_adjoin_simple`: if `α` is integral and `β` is separable over
  `F`, then `F⟮α, β⟯ = F⟮γ⟯` for some `γ`.

## References

* [W. Fulton, *Algebraic Curves: An Introduction to Algebraic Geometry*][Fulton2008],
  Problem 6.31
-/

public section

open IntermediateField Polynomial
open scoped IntermediateField

namespace Field

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E]

/-- Over an infinite field `F`, if `α` is integral and `β` is separable over `F`, then
`F⟮α, β⟯ = F⟮γ⟯` for some `γ`, namely `γ = α + c • β` for a suitable `c : F`. -/
theorem exists_adjoin_pair_eq_adjoin_simple_of_infinite [Infinite F] {α β : E}
    (hα : IsIntegral F α) (hβ : IsSeparable F β) : ∃ γ : E, F⟮α, β⟯ = F⟮γ⟯ := by
  let f := minpoly F α
  let g := minpoly F β
  let ιFE := algebraMap F E
  let ιEE' := algebraMap E (SplittingField (g.map ιFE))
  obtain ⟨c, hc⟩ := primitive_element_inf_aux_exists_c (ιEE'.comp ιFE) (ιEE' α) (ιEE' β) f g
  let γ := α + c • β
  suffices β_in_Fγ : β ∈ F⟮γ⟯ by
    use γ
    apply le_antisymm
    · rw [adjoin_le_iff]
      have α_in_Fγ : α ∈ F⟮γ⟯ := by
        rw [← add_sub_cancel_right α (c • β)]
        exact F⟮γ⟯.sub_mem (mem_adjoin_simple_self F γ) (F⟮γ⟯.toSubalgebra.smul_mem β_in_Fγ c)
      rintro x (rfl | rfl) <;> assumption
    · rw [adjoin_simple_le_iff]
      have α_in_Fαβ : α ∈ F⟮α, β⟯ := subset_adjoin F {α, β} (Set.mem_insert α {β})
      have β_in_Fαβ : β ∈ F⟮α, β⟯ := subset_adjoin F {α, β} (Set.mem_insert_of_mem α rfl)
      exact F⟮α, β⟯.add_mem α_in_Fαβ (F⟮α, β⟯.smul_mem β_in_Fαβ)
  classical
  let p := EuclideanDomain.gcd ((f.map (algebraMap F F⟮γ⟯)).comp
    (C (AdjoinSimple.gen F γ) - (C ↑c : F⟮γ⟯[X]) * X)) (g.map (algebraMap F F⟮γ⟯))
  let h := EuclideanDomain.gcd ((f.map ιFE).comp (C γ - C (ιFE c) * X)) (g.map ιFE)
  have map_g_ne_zero : g.map ιFE ≠ 0 := map_ne_zero (minpoly.ne_zero hβ.isIntegral)
  have h_ne_zero : h ≠ 0 :=
    mt EuclideanDomain.gcd_eq_zero_iff.mp (not_and.mpr fun _ => map_g_ne_zero)
  suffices p_linear : p.map (algebraMap F⟮γ⟯ E) = C h.leadingCoeff * (X - C β) by
    have finale : β = algebraMap F⟮γ⟯ E (-p.coeff 0 / p.coeff 1) := by
      simp [map_div₀, map_neg, ← coeff_map, ← coeff_map, p_linear,
        mul_sub, coeff_C, mul_div_cancel_left₀ β (mt leadingCoeff_eq_zero.mp h_ne_zero)]
    rw [finale]
    exact Subtype.mem (-p.coeff 0 / p.coeff 1)
  have h_sep : h.Separable := separable_gcd_right _ (.map hβ)
  have h_root : h.eval β = 0 := by
    apply eval_gcd_eq_zero
    · rw [eval_comp, eval_sub, eval_mul, eval_C, eval_C, eval_X, eval_map_algebraMap, ←
        Algebra.smul_def, add_sub_cancel_right, minpoly.aeval]
    · rw [eval_map_algebraMap, minpoly.aeval]
  have h_splits : Splits (h.map ιEE') := by
    rw [← Polynomial.gcd_map]
    exact (SplittingField.splits _).of_dvd (map_ne_zero map_g_ne_zero)
      (EuclideanDomain.gcd_dvd_right _ _)
  have h_roots : ∀ x ∈ (h.map ιEE').roots, x = ιEE' β := by
    intro x hx
    rw [mem_roots_map h_ne_zero] at hx
    specialize hc (ιEE' γ - ιEE' (ιFE c) * x) (by
      have f_root := root_left_of_root_gcd hx
      rw [eval₂_comp, eval₂_sub, eval₂_mul, eval₂_C, eval₂_C, eval₂_X, eval₂_map] at f_root
      exact (mem_roots_map (minpoly.ne_zero hα)).mpr f_root)
    specialize hc x (by
      rw [mem_roots_map (minpoly.ne_zero hβ.isIntegral), ← eval₂_map]
      exact root_right_of_root_gcd hx)
    by_contra a
    apply hc
    apply (div_eq_iff (sub_ne_zero.mpr a)).mpr
    simp only [γ, Algebra.smul_def, map_add, map_mul, RingHom.comp_apply]
    ring
  rw [← eq_X_sub_C_of_separable_of_root_eq h_sep h_root h_splits h_roots]
  trans EuclideanDomain.gcd (?_ : E[X]) (?_ : E[X])
  · dsimp only [γ]
    convert (gcd_map (algebraMap F⟮γ⟯ E)).symm
  · simp only [map_comp, Polynomial.map_map, ← IsScalarTower.algebraMap_eq, Polynomial.map_sub,
      map_C, AdjoinSimple.algebraMap_gen, Polynomial.map_mul, map_X]
    congr

/-- **Primitive element theorem with one separable generator**: if `α` is integral and `β` is
separable over `F`, then `F⟮α, β⟯ = F⟮γ⟯` for some `γ`. Only `β` need be separable. -/
theorem exists_adjoin_pair_eq_adjoin_simple {α β : E} (hα : IsIntegral F α)
    (hβ : IsSeparable F β) : ∃ γ : E, F⟮α, β⟯ = F⟮γ⟯ := by
  cases finite_or_infinite F
  · have : FiniteDimensional F F⟮α, β⟯ :=
      finiteDimensional_adjoin fun x hx ↦ by
        rcases hx with rfl | rfl
        exacts [hα, hβ.isIntegral]
    have : Finite F⟮α, β⟯ := Module.finite_of_finite F
    obtain ⟨γ, hγ⟩ := exists_primitive_element_of_finite_top F F⟮α, β⟯
    refine ⟨γ, ?_⟩
    rw [← lift_adjoin_simple, hγ, lift_top]
  · exact exists_adjoin_pair_eq_adjoin_simple_of_infinite F hα hβ

end Field

end
