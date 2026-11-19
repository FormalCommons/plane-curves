/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Germs of the functions on the charts of `Proj` in its function field

For a graded ring `A = ⨁ 𝒜 n` whose scheme `Proj 𝒜` is irreducible, the fraction `a / fⁿ` of
`A_(f)` is a function on the chart `D₊(f)`, and so has a germ in the function field of `Proj 𝒜`.
These germs are compatible between charts.

## Main results

* `AlgebraicGeometry.Proj.germToFunctionField_awayToSection_awayMap`: for `x = f g`, the germ of
  `a / fⁿ` is the germ of its restriction `a gⁿ / xⁿ` to `D₊(x)`.
* `AlgebraicGeometry.Proj.germToFunctionField_awayToSection_mul`: for `f`, `g` of the same degree,
  `(a / fⁿ) · (fⁿ / gⁿ) = a / gⁿ` in the function field.
-/

public section

open CategoryTheory HomogeneousLocalization

namespace AlgebraicGeometry.Proj

variable {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜] [IrreducibleSpace (Proj 𝒜)]

/-- For `x = f g` with `g` homogeneous, the germ in the function field of a function `a` on
`D₊(f)` is the germ of its restriction `awayMap a` to `D₊(x)`. -/
theorem germToFunctionField_awayToSection_awayMap {f g x : A} {e : ℕ} (hg : g ∈ 𝒜 e)
    (hx : x = f * g) [Nonempty (basicOpen 𝒜 f)] [Nonempty (basicOpen 𝒜 x)] (a : Away 𝒜 f) :
    (Proj 𝒜).germToFunctionField _ (awayToSection 𝒜 x (awayMap 𝒜 hg hx a)) =
      (Proj 𝒜).germToFunctionField _ (awayToSection 𝒜 f a) := by
  have h := ConcreteCategory.congr_hom (awayMap_awayToSection 𝒜 hg hx) a
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, CommRingCat.ofHom_apply] at h
  rw [h, Scheme.germToFunctionField, Scheme.germToFunctionField,
    TopCat.Presheaf.germ_res_apply]

/-- For `f`, `g` homogeneous of the same degree `e`, with `D₊(f)` and `D₊(g)` nonempty, the
functions `a / fⁿ` on `D₊(f)` and `fⁿ / gⁿ`, `a / gⁿ` on `D₊(g)` satisfy
`(a / fⁿ) · (fⁿ / gⁿ) = a / gⁿ` in the function field of `Proj 𝒜`. -/
theorem germToFunctionField_awayToSection_mul {f g : A} {e : ℕ} (hf : f ∈ 𝒜 e) (hg : g ∈ 𝒜 e)
    [Nonempty (basicOpen 𝒜 f)] [Nonempty (basicOpen 𝒜 g)] (n : ℕ) {a : A} (ha : a ∈ 𝒜 (n • e)) :
    (Proj 𝒜).germToFunctionField _ (awayToSection 𝒜 f (Away.mk 𝒜 hf n a ha)) *
        (Proj 𝒜).germToFunctionField _
          (awayToSection 𝒜 g (Away.mk 𝒜 hg n (f ^ n) (SetLike.pow_mem_graded n hf))) =
      (Proj 𝒜).germToFunctionField _ (awayToSection 𝒜 g (Away.mk 𝒜 hg n a ha)) := by
  have : Nonempty (basicOpen 𝒜 (f * g)) := by
    rw [basicOpen_mul]
    obtain ⟨⟨p, hp⟩⟩ := ‹Nonempty (basicOpen 𝒜 f)›
    obtain ⟨⟨q, hq⟩⟩ := ‹Nonempty (basicOpen 𝒜 g)›
    obtain ⟨r, hr⟩ := nonempty_preirreducible_inter (basicOpen 𝒜 f).isOpen
      (basicOpen 𝒜 g).isOpen ⟨p, hp⟩ ⟨q, hq⟩
    exact ⟨⟨r, hr⟩⟩
  have hgf : f * g = g * f := mul_comm f g
  rw [← germToFunctionField_awayToSection_awayMap 𝒜 hg rfl,
    ← germToFunctionField_awayToSection_awayMap 𝒜 hf hgf,
    ← germToFunctionField_awayToSection_awayMap 𝒜 hf hgf, ← map_mul, ← map_mul]
  congr 2
  ext
  simp only [awayMap_mk, val_mul, Away.val_mk, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [Submonoid.coe_mul, OneMemClass.coe_one]; ring⟩

end AlgebraicGeometry.Proj

end
