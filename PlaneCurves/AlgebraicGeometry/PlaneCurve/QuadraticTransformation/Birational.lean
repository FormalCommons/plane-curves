/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.CurveLocalRing
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.Basic
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.GoodPosition
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.Hypersurface
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.Irreducible

/-!
# The standard quadratic transformation as a birational map of curves

The standard quadratic transformation of `ℙ²` sends `[x : y : z]` to `[yz : xz : xy]`. It is
defined off the three fundamental points, and is an involution of the complement `U` of the
fundamental triangle `xyz = 0`. For every form `F` it maps `V(F) ∖ U` bijectively onto
`V(F') ∖ U`, where `F'` is the proper transform, and it maps every point of `V(F')` that is not
fundamental into `V(F)`. If `F` is irreducible, with no exceptional component, over an
algebraically closed field, then `V(F')` is the closure of the image of `V(F) ∖ U`. For an
irreducible `F` with no exceptional component, `G / H ↦ G^Q / H^Q` is an isomorphism
`k(F) ≅ k(F')` of function fields: the quadratic transformation is a birational map of the two
curves.

## Main definitions

* `PlaneCurves.Projective.quadraticMap`: the point map `[x : y : z] ↦ [yz : xz : xy]`, with the
  junk value `P` at a fundamental point `P`.
* `PlaneCurves.Projective.quadraticFunctionFieldHom`: for irreducible forms `F`, `G` with
  `G ∣ H^Q ↔ F ∣ H` for every `H`, the map of function fields `k(F) → k(G)`,
  `G₁ / H₁ ↦ G₁^Q / H₁^Q`.
* `PlaneCurves.Projective.quadraticFunctionFieldEquiv`: for an irreducible form `F` with no
  exceptional component, the isomorphism `k(F) ≅ k(F')` of function fields.

## Main results

* `PlaneCurves.Projective.quadraticMap_quadraticMap`,
  `PlaneCurves.Projective.bijOn_quadraticMap_compl_fundamentalTriangle`: the point map is an
  involution of the complement of the fundamental triangle.
* `PlaneCurves.Projective.quadraticMap_eq_fundamentalPoint_iff`: the point map contracts the
  exceptional line `V(Xᵢ)`, without its fundamental points, to `[eᵢ]`.
* `PlaneCurves.Projective.bijOn_quadraticMap`: the point map is a bijection from
  `V(F) ∖ V(XYZ)` onto `V(F') ∖ V(XYZ)`.
* `PlaneCurves.Projective.quadraticMap_mem_zeroLocus_of_mem_zeroLocus_properTransform`: it maps
  the points of `V(F')` that are not fundamental into `V(F)`.
* `PlaneCurves.Projective.zeroLocus_vanishingIdeal_image_quadraticMap`: `V(F')` is the closure,
  `V(I(·))`, of the image of `V(F) ∖ V(XYZ)`.
* `PlaneCurves.Projective.quadraticFunctionFieldEquiv_mk`: the isomorphism of function fields
  sends `G / H` to `G^Q / H^Q`.
* `PlaneCurves.Projective.properTransform_spec`: Fulton's properties (1)–(4) of the proper
  transform of an irreducible form with no exceptional component, together.

## Implementation notes

The library has no Zariski topology on `ℙ²`: the closure of a set `S` of points is
`zeroLocus (vanishingIdeal S)`, the smallest algebraic set that contains it.

The map of function fields is built with `HomogeneousLocalization.liftAlgHom`. The map
`H ↦ (H^Q)_*`, `Q` followed by the dehomogenization at a coordinate `Xᵢ` with `G ∤ Xᵢ`, sends the
homogeneous coordinate ring of `F` to the function field of the affine chart of `G`, which is
`k(G)` by `Projective.functionField.chartEquiv`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.4
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial hiding zeroLocus zeroLocus_anti_mono vanishingIdeal mem_vanishingIdeal_iff
open Projectivization PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type*} [Field k]

section QuadraticMap

private theorem quadVec_smul (c : k) (v : Fin 3 → k) :
    ![(c • v) 1 * (c • v) 2, (c • v) 0 * (c • v) 2, (c • v) 0 * (c • v) 1] =
      (c ^ 2) • ![v 1 * v 2, v 0 * v 2, v 0 * v 1] := by
  funext i
  fin_cases i <;> simp <;> ring

private theorem quadVec_quadVec (v : Fin 3 → k) :
    ![![v 1 * v 2, v 0 * v 2, v 0 * v 1] 1 * ![v 1 * v 2, v 0 * v 2, v 0 * v 1] 2,
      ![v 1 * v 2, v 0 * v 2, v 0 * v 1] 0 * ![v 1 * v 2, v 0 * v 2, v 0 * v 1] 2,
      ![v 1 * v 2, v 0 * v 2, v 0 * v 1] 0 * ![v 1 * v 2, v 0 * v 2, v 0 * v 1] 1] =
      (v 0 * v 1 * v 2) • v := by
  funext i
  fin_cases i <;> simp <;> ring

/-- `(yz, xz, xy)` vanishes exactly when `[x : y : z]` is a fundamental point. -/
private theorem quadVec_eq_zero_iff (v : Fin 3 → k) (hv : v ≠ 0) :
    ![v 1 * v 2, v 0 * v 2, v 0 * v 1] = 0 ↔ ∃ i, mk k v hv = fundamentalPoint i := by
  have hv' : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 := by
    by_contra h
    exact hv (funext fun i ↦ by fin_cases i <;> simp_all)
  simp only [mk_eq_fundamentalPoint_iff, funext_iff]
  simp [Fin.forall_fin_succ, Fin.exists_fin_succ]
  tauto

private theorem quadVec_ne_zero_of_forall_ne_zero {v : Fin 3 → k} (h : ∀ i, v i ≠ 0) :
    ![v 1 * v 2, v 0 * v 2, v 0 * v 1] ≠ 0 := fun h0 ↦ by
  simpa [h] using congrFun h0 0

private theorem quadVec_ne_zero_of_forall_ne_fundamentalPoint {v : Fin 3 → k} {hv : v ≠ 0}
    (hP : ∀ i, mk k v hv ≠ fundamentalPoint i) : ![v 1 * v 2, v 0 * v 2, v 0 * v 1] ≠ 0 :=
  fun h ↦ have ⟨i, hi⟩ := (quadVec_eq_zero_iff v hv).1 h; hP i hi

private theorem forall_rep_ne_zero_of_notMem {v : Fin 3 → k} {hv : v ≠ 0}
    (h : mk k v hv ∉ fundamentalTriangle) : ∀ i, v i ≠ 0 := by
  simpa [mk_mem_fundamentalTriangle_iff] using h

private theorem ne_fundamentalPoint_of_notMem {P : ℙ k (Fin 3 → k)}
    (h : P ∉ fundamentalTriangle) (i : Fin 3) : P ≠ fundamentalPoint i := by
  rintro rfl
  exact h (fundamentalPoint_mem_fundamentalTriangle i)

open scoped Classical in
/-- The standard quadratic transformation of the points of `ℙ²`, `[x : y : z] ↦ [yz : xz : xy]`.
It is defined off the three fundamental points, and is the identity on them (a junk value). -/
noncomputable def quadraticMap (P : ℙ k (Fin 3 → k)) : ℙ k (Fin 3 → k) :=
  if h : ![P.rep 1 * P.rep 2, P.rep 0 * P.rep 2, P.rep 0 * P.rep 1] = 0 then P else mk k _ h

open scoped Classical in
theorem quadraticMap_def (P : ℙ k (Fin 3 → k)) :
    quadraticMap P =
      if h : ![P.rep 1 * P.rep 2, P.rep 0 * P.rep 2, P.rep 0 * P.rep 1] = 0 then P
      else mk k _ h :=
  (rfl)

/-- The point map sends `[x : y : z]` to `[yz : xz : xy]`, for every representative with
`(yz, xz, xy) ≠ 0`. -/
theorem quadraticMap_mk (v : Fin 3 → k) (hv : v ≠ 0)
    (hw : ![v 1 * v 2, v 0 * v 2, v 0 * v 1] ≠ 0) :
    quadraticMap (mk k v hv) = mk k ![v 1 * v 2, v 0 * v 2, v 0 * v 1] hw := by
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep k v hv
  have h : ![(mk k v hv).rep 1 * (mk k v hv).rep 2, (mk k v hv).rep 0 * (mk k v hv).rep 2,
      (mk k v hv).rep 0 * (mk k v hv).rep 1] =
        ((a : k) ^ 2) • ![v 1 * v 2, v 0 * v 2, v 0 * v 1] := by
    rw [← ha, Units.smul_def, quadVec_smul]
  rw [quadraticMap_def, dite_eq_right (h ▸ smul_ne_zero (pow_ne_zero _ a.ne_zero) hw),
    mk_eq_mk_iff']
  exact ⟨_, h.symm⟩

/-- The point map is the identity on the fundamental points (a junk value). -/
@[simp]
theorem quadraticMap_fundamentalPoint (i : Fin 3) :
    quadraticMap (fundamentalPoint (k := k) i) = fundamentalPoint i := by
  rw [quadraticMap_def, dite_eq_left]
  exact (quadVec_eq_zero_iff _ (rep_ne_zero _)).2 ⟨i, mk_rep _⟩

/-- The point map is an involution off the fundamental triangle. -/
theorem quadraticMap_quadraticMap {P : ℙ k (Fin 3 → k)} (hP : P ∉ fundamentalTriangle) :
    quadraticMap (quadraticMap P) = P := by
  induction P using Projectivization.ind with | h v hv =>
  have h := forall_rep_ne_zero_of_notMem hP
  have hw := quadVec_ne_zero_of_forall_ne_zero h
  have hww := quadVec_quadVec v ▸ smul_ne_zero (by simp [h]) hv
  rw [quadraticMap_mk v hv hw, quadraticMap_mk _ hw hww, mk_eq_mk_iff']
  exact ⟨_, (quadVec_quadVec v).symm⟩

/-- A point that is not fundamental is mapped into the fundamental triangle exactly when it lies
on it. -/
theorem quadraticMap_mem_fundamentalTriangle_iff {P : ℙ k (Fin 3 → k)}
    (hP : ∀ i, P ≠ fundamentalPoint i) :
    quadraticMap P ∈ fundamentalTriangle ↔ P ∈ fundamentalTriangle := by
  induction P using Projectivization.ind with | h v hv =>
  have hw := quadVec_ne_zero_of_forall_ne_fundamentalPoint hP
  rw [quadraticMap_mk v hv hw, mk_mem_fundamentalTriangle_iff, mk_mem_fundamentalTriangle_iff]
  simp [Fin.exists_fin_succ]
  tauto

/-- The point map is a bijection of the complement of the fundamental triangle onto itself. -/
theorem bijOn_quadraticMap_compl_fundamentalTriangle :
    Set.BijOn quadraticMap (fundamentalTriangleᶜ : Set (ℙ k (Fin 3 → k))) fundamentalTriangleᶜ := by
  have hmaps : Set.MapsTo quadraticMap (fundamentalTriangleᶜ : Set (ℙ k (Fin 3 → k)))
      fundamentalTriangleᶜ := fun P hP ↦
    (quadraticMap_mem_fundamentalTriangle_iff (ne_fundamentalPoint_of_notMem hP)).not.2 hP
  exact Set.InvOn.bijOn ⟨fun _ hP ↦ quadraticMap_quadraticMap hP,
    fun _ hP ↦ quadraticMap_quadraticMap hP⟩ hmaps hmaps

/-- The point map contracts the exceptional line `V(Xᵢ)`, without its fundamental points, to the
fundamental point `[eᵢ]`. For `i = 2` this is Fulton's `Q⁻¹(P) = L ∖ {P', P''}`. -/
theorem quadraticMap_eq_fundamentalPoint_iff {P : ℙ k (Fin 3 → k)}
    (hP : ∀ i, P ≠ fundamentalPoint i) (i : Fin 3) :
    quadraticMap P = fundamentalPoint i ↔ P ∈ zeroLocus {X i} := by
  induction P using Projectivization.ind with | h v hv =>
  have hw := quadVec_ne_zero_of_forall_ne_fundamentalPoint hP
  simp only [mk_eq_fundamentalPoint_iff, ne_eq] at hP
  rw [quadraticMap_mk v hv hw, mk_eq_fundamentalPoint_iff,
    mk_mem_zeroLocus_iff (by simpa using ⟨1, isHomogeneous_X k i⟩)]
  simp only [Fin.forall_fin_succ, Fin.isValue] at hP
  fin_cases i <;> simp [Fin.forall_fin_succ] at hP ⊢ <;> tauto

end QuadraticMap

section ZeroLocus

variable {F : MvPolynomial (Fin 3) k} {n : ℕ}

/-- Off the fundamental triangle, `F^Q` and the proper transform `F'` have the same zeros. -/
theorem mem_zeroLocus_quadraticTransform_iff (hF : F.IsHomogeneous n) {P : ℙ k (Fin 3 → k)}
    (hP : P ∉ fundamentalTriangle) :
    P ∈ zeroLocus {quadraticTransform F} ↔ P ∈ zeroLocus {properTransform F} := by
  have h : ∀ i, P.rep i ≠ 0 := by simpa [mem_fundamentalTriangle_iff] using hP
  rw [mem_zeroLocus_iff_eval_rep (by simpa using ⟨_, hF.quadraticTransform⟩),
    mem_zeroLocus_iff_eval_rep (by simpa using ⟨_, hF.properTransform⟩)]
  simp [quadraticTransform_eq hF, h]

/-- Off the fundamental triangle, the point map sends the zeros of `F` to the zeros of `F^Q`,
and only them. -/
theorem quadraticMap_mem_zeroLocus_iff (hF : F.IsHomogeneous n) {P : ℙ k (Fin 3 → k)}
    (hP : P ∉ fundamentalTriangle) :
    quadraticMap P ∈ zeroLocus {quadraticTransform F} ↔ P ∈ zeroLocus {F} := by
  induction P using Projectivization.ind with | h v hv =>
  have h := forall_rep_ne_zero_of_notMem hP
  rw [quadraticMap_mk v hv (quadVec_ne_zero_of_forall_ne_zero h),
    mk_mem_zeroLocus_iff (by simpa using ⟨_, hF.quadraticTransform⟩),
    mk_mem_zeroLocus_iff (by simpa using ⟨_, hF⟩)]
  simp only [Set.mem_singleton_iff, forall_eq]
  rw [eval_quadraticTransform]
  rw [quadVec_quadVec, hF.eval_smul]
  simp [h]

/-- Off the fundamental triangle, the point map sends the zeros of `F` to the zeros of the
proper transform `F'`, and only them. -/
theorem quadraticMap_mem_zeroLocus_properTransform_iff (hF : F.IsHomogeneous n)
    {P : ℙ k (Fin 3 → k)} (hP : P ∉ fundamentalTriangle) :
    quadraticMap P ∈ zeroLocus {properTransform F} ↔ P ∈ zeroLocus {F} := by
  rw [← mem_zeroLocus_quadraticTransform_iff hF
    (bijOn_quadraticMap_compl_fundamentalTriangle.mapsTo hP), quadraticMap_mem_zeroLocus_iff hF hP]

/-- The point map sends every point of `V(F')` that is not fundamental into `V(F)`: the
quadratic transformation maps `C' ∖ {P, P', P''}` into `C`. -/
theorem quadraticMap_mem_zeroLocus_of_mem_zeroLocus_properTransform (hF : F.IsHomogeneous n)
    {P : ℙ k (Fin 3 → k)} (hP : ∀ i, P ≠ fundamentalPoint i)
    (h : P ∈ zeroLocus {properTransform F}) : quadraticMap P ∈ zeroLocus {F} := by
  induction P using Projectivization.ind with | h v hv =>
  have hw := quadVec_ne_zero_of_forall_ne_fundamentalPoint hP
  rw [mk_mem_zeroLocus_iff (by simpa using ⟨_, hF.properTransform⟩)] at h
  rw [quadraticMap_mk v hv hw, mk_mem_zeroLocus_iff (by simpa using ⟨_, hF⟩)]
  simp only [Set.mem_singleton_iff, forall_eq] at h ⊢
  rw [← eval_quadraticTransform, quadraticTransform_eq hF]
  simp [h]

/-- **The quadratic transformation is a bijection of curves off the fundamental triangle**: for
every form `F`, the point map sends `V(F) ∖ V(XYZ)` bijectively onto `V(F') ∖ V(XYZ)`. -/
theorem bijOn_quadraticMap (hF : F.IsHomogeneous n) :
    Set.BijOn quadraticMap (zeroLocus {F} \ fundamentalTriangle)
      (zeroLocus {properTransform F} \ fundamentalTriangle) := by
  have hT := bijOn_quadraticMap_compl_fundamentalTriangle (k := k)
  refine Set.InvOn.bijOn ⟨fun _ hP ↦ quadraticMap_quadraticMap hP.2,
    fun _ hP ↦ quadraticMap_quadraticMap hP.2⟩ (fun P hP ↦ ⟨?_, hT.mapsTo hP.2⟩)
    (fun P hP ↦ ⟨?_, hT.mapsTo hP.2⟩)
  · exact (quadraticMap_mem_zeroLocus_properTransform_iff hF hP.2).2 hP.1
  · exact quadraticMap_mem_zeroLocus_of_mem_zeroLocus_properTransform hF
      (ne_fundamentalPoint_of_notMem hP.2) hP.1

/-- Let `G` be an irreducible form with no exceptional component, over an algebraically closed
field. Every form that vanishes on `V(G) ∖ V(XYZ)` vanishes on `V(G)`, so `V(G)` is the closure
`V(I(·))` of `V(G) ∖ V(XYZ)`. -/
theorem zeroLocus_vanishingIdeal_zeroLocus_diff_fundamentalTriangle [IsAlgClosed k]
    {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous n) (hirr : Irreducible G)
    (hX : ∀ i, ¬ X i ∣ G) :
    zeroLocus (vanishingIdeal (zeroLocus {G} \ fundamentalTriangle) : Set _) = zeroLocus {G} := by
  have hGS : ∀ f ∈ ({G} : Set (MvPolynomial (Fin 3) k)), ∃ d, f.IsHomogeneous d := by
    simpa using ⟨n, hG⟩
  refine (zeroLocus_anti_mono ?_).antisymm ?_
  · rw [Set.singleton_subset_iff, SetLike.mem_coe, mem_vanishingIdeal_iff_of_isHomogeneous hG]
    exact fun P hP ↦ ((mem_zeroLocus_iff_eval_rep hGS).1 hP.1) G rfl
  · conv_lhs => rw [← zeroLocus_vanishingIdeal_zeroLocus_of_isHomogeneous hGS]
    refine zeroLocus_anti_mono fun f hf ↦ ?_
    rw [SetLike.mem_coe, mem_vanishingIdeal_iff] at hf ⊢
    intro d P hP
    set g := homogeneousComponent d f
    have hg := homogeneousComponent_isHomogeneous d f
    have hXg : X 0 * X 1 * X 2 * g ∈ (vanishingIdeal (zeroLocus {G})).toIdeal := by
      rw [HomogeneousIdeal.mem_iff, mem_vanishingIdeal_iff_of_isHomogeneous
        ((((isHomogeneous_X k 0).mul (isHomogeneous_X k 1)).mul (isHomogeneous_X k 2)).mul hg)]
      intro Q hQ
      by_cases hQT : Q ∈ fundamentalTriangle
      · obtain ⟨i, hi⟩ := mem_fundamentalTriangle_iff.1 hQT
        fin_cases i <;> simp_all
      · simp [hf d Q ⟨hQ, hQT⟩]
    rw [vanishingIdeal_zeroLocus_singleton_of_squarefree (n := 2) two_ne_zero hG
      hirr.squarefree, Ideal.mem_span_singleton] at hXg
    have hp := hirr.prime
    have hXG (i : Fin 3) : ¬ G ∣ X i := fun h ↦ hX i (hirr.dvd_symm prime_X.irreducible h)
    obtain ⟨K, hK⟩ := (hp.dvd_or_dvd hXg).resolve_left (by simp [hp.dvd_mul, hXG])
    rw [hK, eval_mul, ((mem_zeroLocus_iff_eval_rep hGS).1 hP) G rfl, zero_mul]

/-- **The proper transform is the closure of the image**: for an irreducible form `F` with no
exceptional component, over an algebraically closed field, `V(F')` is the closure `V(I(·))` of
the image of `V(F) ∖ V(XYZ)` under the point map. -/
theorem zeroLocus_vanishingIdeal_image_quadraticMap [IsAlgClosed k] (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) (hX : ∀ i, ¬ X i ∣ F) :
    zeroLocus (vanishingIdeal (quadraticMap '' (zeroLocus {F} \ fundamentalTriangle)) : Set _) =
      zeroLocus {properTransform F} := by
  rw [(bijOn_quadraticMap hF).image_eq]
  exact zeroLocus_vanishingIdeal_zeroLocus_diff_fundamentalTriangle hF.properTransform
    (irreducible_properTransform hF hirr hX) (not_X_dvd_properTransform hF hirr.ne_zero)

end ZeroLocus

section FunctionField

open TauCeti TauCeti.AlgebraicGeometry

variable {F G : MvPolynomial (Fin 3) k} {n m : ℕ}

/-- The map `H ↦ (H^Q)_*` from the homogeneous coordinate ring of `F` to the function field of
the affine chart `Xᵢ = 1` of `G`, for forms `F`, `G` with `F ∣ H → G ∣ H^Q`. -/
private noncomputable def quadraticChartHom (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous m)
    [Fact (Irreducible G)] {i : Fin 3} (hi : ¬ G ∣ X i)
    (h : ∀ H, F ∣ H → G ∣ quadraticTransform H) :
    haveI := isPrime_span_dehomogenize hG hi
    MvPolynomial (Fin 3) k ⧸ (projectivePlaneCurve.ideal hF).toIdeal →ₐ[k]
      AffineSpace.functionField (Ideal.span {dehomogenize i G}) :=
  haveI := isPrime_span_dehomogenize hG hi
  (IsScalarTower.toAlgHom k (MvPolynomial (Fin 2) k ⧸ Ideal.span {dehomogenize i G}) _).comp
    (Ideal.quotientMapₐ _ ((dehomogenize i).comp quadraticTransform) fun H hH ↦ by
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      exact map_dvd _ (h H ((projectivePlaneCurve.mem_ideal_iff hF).1 hH)))

private theorem quadraticChartHom_mk (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous m)
    [Fact (Irreducible G)] {i : Fin 3} (hi : ¬ G ∣ X i)
    (h : ∀ H, F ∣ H → G ∣ quadraticTransform H) (H : MvPolynomial (Fin 3) k) :
    haveI := isPrime_span_dehomogenize hG hi
    quadraticChartHom hF hG hi h (Ideal.Quotient.mk _ H) =
      algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {dehomogenize i G})
        (dehomogenize i (quadraticTransform H))) :=
  (rfl)

private theorem quadraticChartHom_ne_zero (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous m)
    [Fact (Irreducible F)] [Fact (Irreducible G)] {i : Fin 3} (hi : ¬ G ∣ X i)
    (h : ∀ H, G ∣ quadraticTransform H ↔ F ∣ H) ⦃d : ℕ⦄
    ⦃g : MvPolynomial (Fin 3) k ⧸ (projectivePlaneCurve.ideal hF).toIdeal⦄
    (hg : g ∈ (projectivePlaneCurve.ideal hF).quotientGrading d)
    (hgI : g ∈ (⊥ : Ideal (MvPolynomial (Fin 3) k ⧸
      (projectivePlaneCurve.ideal hF).toIdeal)).primeCompl) :
    quadraticChartHom hF hG hi (fun H ↦ (h H).2) g ≠ 0 := by
  have := isPrime_span_dehomogenize hG hi
  obtain ⟨g, hg', rfl⟩ := (projectivePlaneCurve.ideal hF).exists_isHomogeneous_mk_eq hg
  rw [quadraticChartHom_mk, Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem,
    ← projectivePlaneCurve.map_dehomogenize_ideal hG i]
  refine dehomogenize_notMem_map ((projectivePlaneCurve.mem_ideal_iff hG).not.2 hi)
    hg'.quadraticTransform ((projectivePlaneCurve.mem_ideal_iff hG).not.2 fun hQ ↦ hgI ?_)
  exact Ideal.Quotient.eq_zero_iff_mem.2 ((projectivePlaneCurve.mem_ideal_iff hF).2 ((h g).1 hQ))

/-- **The quadratic transformation of function fields.** For irreducible forms `F`, `G` such
that `G ∣ H^Q ↔ F ∣ H` for every polynomial `H`, the `k`-algebra hom `k(F) → k(G)` of the
function fields of the curves `F = 0` and `G = 0` that sends `G₁ / H₁` to `G₁^Q / H₁^Q`
(`quadraticFunctionFieldHom_mk`). -/
noncomputable def quadraticFunctionFieldHom (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous m)
    [Fact (Irreducible F)] [Fact (Irreducible G)] (h : ∀ H, G ∣ quadraticTransform H ↔ F ∣ H) :
    Projective.functionField hF →ₐ[k] Projective.functionField hG :=
  haveI := isPrime_span_dehomogenize hG
    (projectivePlaneCurve.exists_not_dvd_X (Fact.out : Irreducible G)).choose_spec
  (Projective.functionField.chartEquiv hG _
      (projectivePlaneCurve.exists_not_dvd_X (Fact.out : Irreducible G)).choose_spec).symm.toAlgHom
    |>.comp (HomogeneousLocalization.liftAlgHom _ (Ideal.primeCompl_le_nonZeroDivisors _)
      (quadraticChartHom hF hG _ (fun H ↦ (h H).2))
      (quadraticChartHom_ne_zero hF hG
        (projectivePlaneCurve.exists_not_dvd_X (Fact.out : Irreducible G)).choose_spec h))

/-- The quadratic transformation of function fields sends `G₁ / H₁` to `G₁^Q / H₁^Q`. -/
@[simp]
theorem quadraticFunctionFieldHom_mk (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous m)
    [Fact (Irreducible F)] [Fact (Irreducible G)] (h : ∀ H, G ∣ quadraticTransform H ↔ F ∣ H)
    {d : ℕ} {G₁ H₁ : MvPolynomial (Fin 3) k} (hG₁ : G₁.IsHomogeneous d)
    (hH₁ : H₁.IsHomogeneous d) (hH₁F : H₁ ∉ projectivePlaneCurve.ideal hF) :
    quadraticFunctionFieldHom hF hG h (ProjectiveSpace.functionField.mk hG₁ hH₁ hH₁F) =
      ProjectiveSpace.functionField.mk hG₁.quadraticTransform hH₁.quadraticTransform
        fun hQ ↦ hH₁F ((projectivePlaneCurve.mem_ideal_iff hF).2
          ((h H₁).1 ((projectivePlaneCurve.mem_ideal_iff hG).1 hQ))) := by
  have hi := (projectivePlaneCurve.exists_not_dvd_X (Fact.out : Irreducible G)).choose_spec
  have := isPrime_span_dehomogenize hG hi
  rw [quadraticFunctionFieldHom, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    AlgEquiv.symm_apply_eq, Projective.functionField.chartEquiv_mk,
    ProjectiveSpace.functionField.mk_def, HomogeneousLocalization.liftAlgHom_mk]
  rfl

/-- The quadratic transformations of function fields `k(F) → k(G)` and `k(G) → k(F)` are
inverse to each other: `G₁^{QQ} / H₁^{QQ} = (XYZ)^d G₁ / ((XYZ)^d H₁) = G₁ / H₁`. -/
theorem quadraticFunctionFieldHom_comp_quadraticFunctionFieldHom (hF : F.IsHomogeneous n)
    (hG : G.IsHomogeneous m) [Fact (Irreducible F)] [Fact (Irreducible G)]
    (h : ∀ H, G ∣ quadraticTransform H ↔ F ∣ H) (h' : ∀ H, F ∣ quadraticTransform H ↔ G ∣ H) :
    (quadraticFunctionFieldHom hG hF h').comp (quadraticFunctionFieldHom hF hG h) =
      AlgHom.id k _ := by
  refine AlgHom.ext fun z ↦ ?_
  obtain ⟨d, f, g, hf, hg, hgI, rfl⟩ := ProjectiveSpace.functionField.exists_eq_mk z
  rw [AlgHom.comp_apply, quadraticFunctionFieldHom_mk, quadraticFunctionFieldHom_mk,
    AlgHom.id_apply, ProjectiveSpace.functionField.mk_eq_mk_iff,
    quadraticTransform_quadraticTransform hf, quadraticTransform_quadraticTransform hg]
  convert zero_mem (projectivePlaneCurve.ideal hF)
  ring

variable [Fact (Irreducible F)] [Fact (Irreducible (properTransform F))]

/-- **The quadratic transformation is birational.** For an irreducible form `F` with no
exceptional component, the isomorphism `k(F) ≅ k(F')` of the function fields of the curve
`F = 0` and of its proper transform, that sends `G / H` to `G^Q / H^Q`
(`quadraticFunctionFieldEquiv_mk`). Its inverse is the same map for `F'`, since `(F')' = F`
(`quadraticFunctionFieldEquiv_symm_mk`). -/
noncomputable def quadraticFunctionFieldEquiv (hF : F.IsHomogeneous n) (hX : ∀ i, ¬ X i ∣ F) :
    Projective.functionField hF ≃ₐ[k] Projective.functionField hF.properTransform :=
  AlgEquiv.ofAlgHom
    (quadraticFunctionFieldHom hF hF.properTransform fun _ ↦
      dvd_quadraticTransform_iff hF Fact.out hX)
    (quadraticFunctionFieldHom hF.properTransform hF fun _ ↦
      dvd_quadraticTransform_iff_properTransform_dvd hF Fact.out hX)
    (quadraticFunctionFieldHom_comp_quadraticFunctionFieldHom _ _ _ _)
    (quadraticFunctionFieldHom_comp_quadraticFunctionFieldHom _ _ _ _)

theorem quadraticFunctionFieldEquiv_def (hF : F.IsHomogeneous n) (hX : ∀ i, ¬ X i ∣ F) :
    quadraticFunctionFieldEquiv hF hX =
      AlgEquiv.ofAlgHom
        (quadraticFunctionFieldHom hF hF.properTransform fun _ ↦
          dvd_quadraticTransform_iff hF Fact.out hX)
        (quadraticFunctionFieldHom hF.properTransform hF fun _ ↦
          dvd_quadraticTransform_iff_properTransform_dvd hF Fact.out hX)
        (quadraticFunctionFieldHom_comp_quadraticFunctionFieldHom _ _ _ _)
        (quadraticFunctionFieldHom_comp_quadraticFunctionFieldHom _ _ _ _) :=
  (rfl)

/-- The isomorphism `k(F) ≅ k(F')` sends `G / H` to `G^Q / H^Q`. -/
@[simp]
theorem quadraticFunctionFieldEquiv_mk (hF : F.IsHomogeneous n) (hX : ∀ i, ¬ X i ∣ F) {d : ℕ}
    {G H : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous d) (hH : H.IsHomogeneous d)
    (hHF : H ∉ projectivePlaneCurve.ideal hF) :
    quadraticFunctionFieldEquiv hF hX (ProjectiveSpace.functionField.mk hG hH hHF) =
      ProjectiveSpace.functionField.mk hG.quadraticTransform hH.quadraticTransform
        fun hQ ↦ hHF ((projectivePlaneCurve.mem_ideal_iff hF).2
          ((dvd_quadraticTransform_iff hF Fact.out hX).1
            ((projectivePlaneCurve.mem_ideal_iff hF.properTransform).1 hQ))) :=
  quadraticFunctionFieldHom_mk _ _ (fun _ ↦ dvd_quadraticTransform_iff hF Fact.out hX) hG hH hHF

/-- The inverse of the isomorphism `k(F) ≅ k(F')` sends `G / H` to `G^Q / H^Q`. -/
@[simp]
theorem quadraticFunctionFieldEquiv_symm_mk (hF : F.IsHomogeneous n) (hX : ∀ i, ¬ X i ∣ F)
    {d : ℕ} {G H : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous d) (hH : H.IsHomogeneous d)
    (hHF : H ∉ projectivePlaneCurve.ideal hF.properTransform) :
    (quadraticFunctionFieldEquiv hF hX).symm (ProjectiveSpace.functionField.mk hG hH hHF) =
      ProjectiveSpace.functionField.mk hG.quadraticTransform hH.quadraticTransform
        fun hQ ↦ hHF ((projectivePlaneCurve.mem_ideal_iff hF.properTransform).2
          ((dvd_quadraticTransform_iff_properTransform_dvd hF Fact.out hX).1
            ((projectivePlaneCurve.mem_ideal_iff hF).1 hQ))) :=
  quadraticFunctionFieldHom_mk _ _
    (fun _ ↦ dvd_quadraticTransform_iff_properTransform_dvd hF Fact.out hX) hG hH hHF

end FunctionField

section Milestone

variable {F : MvPolynomial (Fin 3) k} {n : ℕ}

/-- **Proper transform of a plane curve under the standard quadratic transformation.** Let `F`
be an irreducible form of degree `n` over an algebraically closed field, not an exceptional line
(no `Xᵢ` divides `F`), with multiplicities `rᵢ` at the fundamental points `[eᵢ]`, and let
`F'` be its proper transform. Then:

1. `F^Q = X^{r₀} Y^{r₁} Z^{r₂} F'`, no `Xᵢ` divides `F'`, and `Xᵢ` divides `F^Q` exactly `rᵢ`
   times;
2. `F'` is an irreducible form of degree `2n - r₀ - r₁ - r₂` with `(F')' = F`; `V(F')` is the
   closure of the image of `V(F) ∖ V(XYZ)` under the point map `Q`, which is a bijection from
   `V(F) ∖ V(XYZ)` onto `V(F') ∖ V(XYZ)` and maps the points of `V(F')` that are not fundamental
   into `V(F)`; and `Q` is birational: the function fields `k(F)` and `k(F')` are isomorphic;
3. the multiplicities of `F'` at the fundamental points are `n - r₁ - r₂`, `n - r₀ - r₂` and
   `n - r₀ - r₁`;
4. if `F` is in good position, so is `F'`.

Milestone: *Proper transform of a plane curve under the standard quadratic transformation*. -/
theorem properTransform_spec [IsAlgClosed k] (hF : F.IsHomogeneous n) (hirr : Irreducible F)
    (hX : ∀ i, ¬ X i ∣ F) :
    (quadraticTransform F =
        X 0 ^ (mult F (fundamentalPoint 0)).toNat * X 1 ^ (mult F (fundamentalPoint 1)).toNat *
          X 2 ^ (mult F (fundamentalPoint 2)).toNat * properTransform F ∧
      (∀ i, ¬ X i ∣ properTransform F) ∧
      ∀ i, multiplicity (X i) (quadraticTransform F) = (mult F (fundamentalPoint i)).toNat) ∧
    ((properTransform F).IsHomogeneous (2 * n - ∑ i, (mult F (fundamentalPoint i)).toNat) ∧
      Irreducible (properTransform F) ∧ properTransform (properTransform F) = F ∧
      zeroLocus (vanishingIdeal (quadraticMap '' (zeroLocus {F} \ fundamentalTriangle)) :
        Set _) = zeroLocus {properTransform F} ∧
      Set.BijOn quadraticMap (zeroLocus {F} \ fundamentalTriangle)
        (zeroLocus {properTransform F} \ fundamentalTriangle) ∧
      Set.MapsTo quadraticMap (zeroLocus {properTransform F} \ Set.range fundamentalPoint)
        (zeroLocus {F}) ∧
      haveI := Fact.mk hirr
      haveI := Fact.mk (irreducible_properTransform hF hirr hX)
      Nonempty (Projective.functionField hF ≃ₐ[k] Projective.functionField hF.properTransform)) ∧
    (mult (properTransform F) (fundamentalPoint 0) =
        (n - (mult F (fundamentalPoint 1)).toNat - (mult F (fundamentalPoint 2)).toNat : ℕ) ∧
      mult (properTransform F) (fundamentalPoint 1) =
        (n - (mult F (fundamentalPoint 0)).toNat - (mult F (fundamentalPoint 2)).toNat : ℕ) ∧
      mult (properTransform F) (fundamentalPoint 2) =
        (n - (mult F (fundamentalPoint 0)).toNat - (mult F (fundamentalPoint 1)).toNat : ℕ)) ∧
    (IsGoodPosition F → IsGoodPosition (properTransform F)) := by
  have := Fact.mk hirr
  have := Fact.mk (irreducible_properTransform hF hirr hX)
  refine ⟨⟨quadraticTransform_eq hF, not_X_dvd_properTransform hF hirr.ne_zero,
      multiplicity_X_quadraticTransform hF hirr.ne_zero⟩,
    ⟨hF.properTransform, irreducible_properTransform hF hirr hX,
      properTransform_properTransform hF hX,
      zeroLocus_vanishingIdeal_image_quadraticMap hF hirr hX, bijOn_quadraticMap hF,
      fun P hP ↦ quadraticMap_mem_zeroLocus_of_mem_zeroLocus_properTransform hF
        (fun i hi ↦ hP.2 ⟨i, hi.symm⟩) hP.1,
      ⟨quadraticFunctionFieldEquiv hF hX⟩⟩,
    ⟨mult_properTransform_fundamentalPoint_zero hF (hX 0),
      mult_properTransform_fundamentalPoint_one hF (hX 1),
      mult_properTransform_fundamentalPoint_two hF (hX 2)⟩,
    fun h ↦ h.properTransform hF⟩

end Milestone

end PlaneCurves.Projective

end
