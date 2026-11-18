/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.AffineSpace.LocalRing
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.FunctionField
public import TauCeti.LinearAlgebra.Projectivization.AffineChart
public import TauCeti.RingTheory.MvPolynomial.Dehomogenization

/-!
# Local rings of projective space in an affine chart

For a field `k`, a point `P ∈ ℙⁿ` in the standard affine open `Uᵢ = {Xᵢ ≠ 0}` and the chart
`φᵢ = affineChart i : Uᵢ → 𝔸ⁿ`, the local ring `𝒪_P(ℙⁿ)` is isomorphic to `𝒪_{φᵢ(P)}(𝔸ⁿ)`: a
fraction `f / g` of forms of the same degree with `g(P) ≠ 0` goes to the fraction of the
dehomogenizations `f_* / g_*`, where `h_*` sets `Xᵢ = 1` in `h`; the inverse sends the
coordinate `Yⱼ` to `X_{i.succAbove j} / Xᵢ`.

## Main definitions

* `PlaneCurves.ProjectiveSpace.localRing.chartEquiv i hP`: the isomorphism
  `𝒪_P(ℙⁿ) ≃ₐ[k] 𝒪_{φᵢ(P)}(𝔸ⁿ)`.

## Main results

* `localRing.chartEquiv_mk`: `f / g ↦ f_* / g_*`; `localRing.chartEquiv_mk_of_den_eq`:
  `f / Xᵢᵐ ↦ f_*`.
* `localRing.chartEquiv_symm_algebraMap`, `localRing.chartEquiv_symm_algebraMap_X`: the inverse
  substitutes `X_{i.succAbove j} / Xᵢ` for `Yⱼ`.
* `localRing.evalAt_chartEquiv`: the isomorphism preserves values at `P` and at `φᵢ(P)`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §4.3
-/

public section

noncomputable section

open MvPolynomial Projectivization TauCeti
open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PlaneCurves.ProjectiveSpace

variable {k : Type*} [Field k] {n : ℕ} {P : ℙ k (Fin (n + 1) → k)} {i : Fin (n + 1)}

/-- At a point `P` of `Uᵢ`, the dehomogenization of a form `g` of degree `d` takes the value
`g(v) / vᵢᵈ` at the chart point, where `v` is the representative of `P`. -/
theorem eval_affineChart_dehomogenize (hP : P ∈ affineOpen i)
    {g : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hg : g.IsHomogeneous d) :
    eval (affineChart i P) (dehomogenize i g) = (P.rep i)⁻¹ ^ d * eval P.rep g := by
  conv_lhs => rw [← mk_rep P, affineChart_mk]
  exact eval_dehomogenize_div i hg _ ((mem_affineOpen_iff i P).1 hP)

/-- At a point `P` of `Uᵢ`, the coordinate `Xᵢ` does not lie in the ideal of `P`. -/
theorem X_mem_primeCompl_pointIdeal (hP : P ∈ affineOpen i) :
    (X i : MvPolynomial (Fin (n + 1)) k) ∈ (pointIdeal P).toIdeal.primeCompl := fun h ↦
  (mem_affineOpen_iff i P).1 hP
    (by simpa using (mem_pointIdeal_iff_of_isHomogeneous (isHomogeneous_X k i)).1 h)

/-- At a point `P` of `Uᵢ`, a form `g` with `g(P) ≠ 0` dehomogenizes to a polynomial that does
not vanish at the chart point. -/
theorem dehomogenize_mem_primeCompl (hP : P ∈ affineOpen i) {g : MvPolynomial (Fin (n + 1)) k}
    {d : ℕ} (hg : g ∈ homogeneousSubmodule (Fin (n + 1)) k d)
    (hgP : g ∈ (pointIdeal P).toIdeal.primeCompl) :
    dehomogenize i g ∈ (MvPolynomial.vanishingIdeal k {affineChart i P}).primeCompl := by
  rw [Ideal.mem_primeCompl_iff, mem_vanishingIdeal_singleton_iff, aeval_eq_eval,
    eval_affineChart_dehomogenize hP ((mem_homogeneousSubmodule _ _).1 hg)]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero ((mem_affineOpen_iff i P).1 hP)))
    (localRing.eval_rep_ne_zero hg hgP)

namespace localRing

variable (i) in
/-- The fraction `Xⱼ / Xᵢ` in `𝒪_P(ℙⁿ)`. -/
private noncomputable def coord (hP : P ∈ affineOpen i) (j : Fin (n + 1)) : localRing P :=
  HomogeneousLocalization.mk ⟨1, ⟨X j, (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X k j)⟩,
    ⟨X i, (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X k i)⟩,
    X_mem_primeCompl_pointIdeal hP⟩

private theorem val_coord (hP : P ∈ affineOpen i) (j : Fin (n + 1)) :
    (coord i hP j).val = Localization.mk (X j) ⟨X i, X_mem_primeCompl_pointIdeal hP⟩ :=
  HomogeneousLocalization.val_mk _

private theorem coord_self (hP : P ∈ affineOpen i) : coord i hP i = 1 := by
  rw [HomogeneousLocalization.ext_iff_val, val_coord, HomogeneousLocalization.val_one]
  exact Localization.mk_self
    (⟨X i, X_mem_primeCompl_pointIdeal hP⟩ : (pointIdeal P).toIdeal.primeCompl)

/-- A form `g` of degree `d` evaluated at the fractions `Xⱼ / Xᵢ` is `g / Xᵢᵈ`. -/
private theorem val_aeval_coord (hP : P ∈ affineOpen i) {g : MvPolynomial (Fin (n + 1)) k}
    {d : ℕ} (hg : g.IsHomogeneous d) :
    (aeval (coord i hP) g).val =
      Localization.mk g ⟨X i ^ d, pow_mem (X_mem_primeCompl_pointIdeal hP) d⟩ := by
  set s : (pointIdeal P).toIdeal.primeCompl := ⟨X i, X_mem_primeCompl_pointIdeal hP⟩
  set u : Localization (pointIdeal P).toIdeal.primeCompl := Localization.mk 1 s
  have hC : (algebraMap (localRing P) (Localization (pointIdeal P).toIdeal.primeCompl)).comp
      (algebraMap k (localRing P)) = (algebraMap (MvPolynomial (Fin (n + 1)) k)
        (Localization (pointIdeal P).toIdeal.primeCompl)).comp C := by
    ext a
    rfl
  have hX : (algebraMap (localRing P) (Localization (pointIdeal P).toIdeal.primeCompl)) ∘
      coord i hP = u • (algebraMap (MvPolynomial (Fin (n + 1)) k)
        (Localization (pointIdeal P).toIdeal.primeCompl) ∘ X) := by
    funext j
    rw [Function.comp_apply, HomogeneousLocalization.algebraMap_apply, val_coord, Pi.smul_apply,
      smul_eq_mul, Function.comp_apply, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul,
      one_mul, mul_one]
  have := hg.map ((algebraMap (MvPolynomial (Fin (n + 1)) k)
    (Localization (pointIdeal P).toIdeal.primeCompl)).comp C)
  change algebraMap (localRing P) (Localization (pointIdeal P).toIdeal.primeCompl) _ = _
  rw [aeval_def, eval₂_comp_left, hC, hX, ← eval_map, this.eval_smul, eval_map,
    ← eval₂_comp_left, eval₂_eta]
  rw [← Localization.mk_one_eq_algebraMap, Localization.mk_pow, Localization.mk_mul, one_pow,
    one_mul, mul_one]
  rfl


variable (i) in
/-- The `k`-algebra map `k[Y₀, …, Yₙ₋₁] → 𝒪_P(ℙⁿ)` sending `Yⱼ` to `X_{i.succAbove j} / Xᵢ`. -/
private noncomputable def ofPoly (hP : P ∈ affineOpen i) :
    MvPolynomial (Fin n) k →ₐ[k] localRing P :=
  aeval (coord i hP ∘ i.succAbove)

private theorem ofPoly_dehomogenize (hP : P ∈ affineOpen i) {g : MvPolynomial (Fin (n + 1)) k}
    {d : ℕ} (hg : g.IsHomogeneous d) :
    ofPoly i hP (dehomogenize i g) =
      HomogeneousLocalization.mk ⟨d, ⟨g, (mem_homogeneousSubmodule _ _).2 hg⟩,
        ⟨X i ^ d, (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X_pow i d)⟩,
        pow_mem (X_mem_primeCompl_pointIdeal hP) d⟩ := by
  have : Fin.insertNth (α := fun _ ↦ localRing P) i 1 (coord i hP ∘ i.succAbove) = coord i hP := by
    funext j
    refine Fin.succAboveCases i ?_ (fun l ↦ ?_) j <;> simp [coord_self]
  rw [ofPoly, aeval_dehomogenize, this, HomogeneousLocalization.ext_iff_val, val_aeval_coord hP hg,
    HomogeneousLocalization.val_mk]

private theorem evalAt_comp_ofPoly (hP : P ∈ affineOpen i) :
    (evalAt P).comp (ofPoly i hP) = aeval (affineChart i P) := by
  refine MvPolynomial.algHom_ext fun j ↦ ?_
  rw [AlgHom.comp_apply, ofPoly, aeval_X, aeval_X, Function.comp_apply, coord, evalAt_mk_rep]
  conv_rhs => rw [← mk_rep P, affineChart_mk]
  simp

private theorem isUnit_ofPoly (hP : P ∈ affineOpen i)
    (s : (MvPolynomial.vanishingIdeal k {affineChart i P}).primeCompl) :
    IsUnit (ofPoly i hP s) := by
  rw [isUnit_iff_evalAt_ne_zero, ← AlgHom.comp_apply, evalAt_comp_ofPoly, aeval_eq_eval]
  exact AffineSpace.localRing.eval_ne_zero s

variable (i) in
/-- The inverse of the chart isomorphism, `𝒪(𝔸ⁿ) → 𝒪_P(ℙⁿ)` at the chart point. -/
private noncomputable def ofChart (hP : P ∈ affineOpen i) :
    AffineSpace.localRing k (affineChart i P) →ₐ[k] localRing P :=
  IsLocalization.liftAlgHom (M := (MvPolynomial.vanishingIdeal k {affineChart i P}).primeCompl)
    (f := ofPoly i hP) (isUnit_ofPoly hP)

private theorem ofChart_algebraMap (hP : P ∈ affineOpen i) (p : MvPolynomial (Fin n) k) :
    ofChart i hP (algebraMap _ _ p) = ofPoly i hP p := by
  rw [ofChart, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

private theorem ofChart_mk' (hP : P ∈ affineOpen i)
    (c : HomogeneousLocalization.NumDenSameDeg (homogeneousSubmodule (Fin (n + 1)) k)
      (pointIdeal P).toIdeal.primeCompl) :
    ofChart i hP (IsLocalization.mk' _ (dehomogenize i (c.num : MvPolynomial (Fin (n + 1)) k))
      ⟨_, dehomogenize_mem_primeCompl hP c.den.2 c.den_mem⟩) = HomogeneousLocalization.mk c := by
  rw [ofChart, IsLocalization.liftAlgHom_apply, IsLocalization.lift_mk'_spec]
  change ofPoly i hP _ = ofPoly i hP _ * _
  rw [ofPoly_dehomogenize hP ((mem_homogeneousSubmodule _ _).1 c.num.2),
    ofPoly_dehomogenize hP ((mem_homogeneousSubmodule _ _).1 c.den.2),
    HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk,
    HomogeneousLocalization.val_mk, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

private theorem ofChart_bijective (hP : P ∈ affineOpen i) : Function.Bijective (ofChart i hP) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective
      (MvPolynomial.vanishingIdeal k {affineChart i P}).primeCompl z
    rw [ofChart, IsLocalization.liftAlgHom_apply, IsLocalization.lift_mk'_spec,
      mul_zero] at hz
    change ofPoly i hP a = 0 at hz
    obtain ⟨g, hg, rfl⟩ := exists_isHomogeneous_dehomogenize_eq i (le_refl a.totalDegree)
    rw [ofPoly_dehomogenize hP hg, HomogeneousLocalization.ext_iff_val,
      HomogeneousLocalization.val_mk, HomogeneousLocalization.val_zero,
      Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at hz
    obtain ⟨⟨m, hm⟩, hmg⟩ := hz
    have hm0 : m ≠ 0 := fun h ↦ hm (h ▸ zero_mem _)
    change IsLocalization.mk' _ (dehomogenize i g) s = 0
    have hg0 : g = 0 := (mul_eq_zero.1 hmg).resolve_left hm0
    rw [hg0, map_zero, IsLocalization.mk'_zero]
  · obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
    exact ⟨_, ofChart_mk' hP c⟩

variable (i) in
/-- The chart isomorphism `𝒪_P(ℙⁿ) ≅ 𝒪_{φᵢ(P)}(𝔸ⁿ)` for a point `P` of the standard affine open
`Uᵢ = {Xᵢ ≠ 0}`, with `φᵢ = affineChart i`: a fraction `f / g` of forms of the same degree goes to
`f(Y₀, …, 1, …, Yₙ₋₁) / g(Y₀, …, 1, …, Yₙ₋₁)` (`chartEquiv_mk`), and its inverse sends `Yⱼ` to
`X_{i.succAbove j} / Xᵢ` (`chartEquiv_symm_algebraMap_X`). -/
noncomputable def chartEquiv (hP : P ∈ affineOpen i) :
    localRing P ≃ₐ[k] AffineSpace.localRing k (affineChart i P) :=
  (AlgEquiv.ofBijective (ofChart i hP) (ofChart_bijective hP)).symm



/-- The chart isomorphism sends a fraction `f / g` of forms of the same degree with `g(P) ≠ 0` to
the fraction `f(Y₀, …, 1, …, Yₙ₋₁) / g(Y₀, …, 1, …, Yₙ₋₁)` of their dehomogenizations. -/
@[simp]
theorem chartEquiv_mk (hP : P ∈ affineOpen i)
    (c : HomogeneousLocalization.NumDenSameDeg (homogeneousSubmodule (Fin (n + 1)) k)
      (pointIdeal P).toIdeal.primeCompl) :
    chartEquiv i hP (HomogeneousLocalization.mk c) =
      IsLocalization.mk' _ (dehomogenize i (c.num : MvPolynomial (Fin (n + 1)) k))
        ⟨_, dehomogenize_mem_primeCompl hP c.den.2 c.den_mem⟩ := by
  rw [chartEquiv, AlgEquiv.symm_apply_eq, AlgEquiv.ofBijective_apply, ofChart_mk']

/-- The chart isomorphism sends a fraction `f / Xᵢᵐ` to the dehomogenization of `f`. -/
theorem chartEquiv_mk_of_den_eq (hP : P ∈ affineOpen i)
    (c : HomogeneousLocalization.NumDenSameDeg (homogeneousSubmodule (Fin (n + 1)) k)
      (pointIdeal P).toIdeal.primeCompl) {m : ℕ}
    (h : (c.den : MvPolynomial (Fin (n + 1)) k) = X i ^ m) :
    chartEquiv i hP (HomogeneousLocalization.mk c) =
      algebraMap _ _ (dehomogenize i (c.num : MvPolynomial (Fin (n + 1)) k)) := by
  rw [chartEquiv_mk, IsLocalization.mk'_eq_iff_eq_mul]
  simp [h]

/-- The inverse of the chart isomorphism on polynomials: it substitutes `X_{i.succAbove j} / Xᵢ`
for `Yⱼ`. -/
theorem chartEquiv_symm_algebraMap (hP : P ∈ affineOpen i) (p : MvPolynomial (Fin n) k) :
    (chartEquiv i hP).symm (algebraMap _ _ p) =
      aeval (fun j ↦ HomogeneousLocalization.mk
        ⟨1, ⟨X (i.succAbove j), (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X k _)⟩,
          ⟨X i, (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X k i)⟩,
          X_mem_primeCompl_pointIdeal hP⟩) p := by
  rw [chartEquiv, AlgEquiv.symm_symm, AlgEquiv.ofBijective_apply, ofChart_algebraMap]
  rfl

/-- The inverse of the chart isomorphism sends `Yⱼ` to `X_{i.succAbove j} / Xᵢ`. -/
@[simp]
theorem chartEquiv_symm_algebraMap_X (hP : P ∈ affineOpen i) (j : Fin n) :
    (chartEquiv i hP).symm (algebraMap _ _ (X j : MvPolynomial (Fin n) k)) =
      HomogeneousLocalization.mk
        ⟨1, ⟨X (i.succAbove j), (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X k _)⟩,
          ⟨X i, (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X k i)⟩,
          X_mem_primeCompl_pointIdeal hP⟩ := by
  rw [chartEquiv_symm_algebraMap, aeval_X]

/-- The chart isomorphism is compatible with the values at `P` and at its chart point. -/
@[simp]
theorem evalAt_chartEquiv (hP : P ∈ affineOpen i) (z : localRing P) :
    AffineSpace.localRing.evalAt k (affineChart i P) (chartEquiv i hP z) = evalAt P z := by
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  rw [chartEquiv_mk, AffineSpace.localRing.evalAt_mk', evalAt_mk_rep,
    eval_affineChart_dehomogenize hP ((mem_homogeneousSubmodule _ _).1 c.num.2),
    eval_affineChart_dehomogenize hP ((mem_homogeneousSubmodule _ _).1 c.den.2),
    mul_div_mul_left _ _ (pow_ne_zero _ (inv_ne_zero ((mem_affineOpen_iff i P).1 hP)))]

end localRing

end PlaneCurves.ProjectiveSpace

end

end
