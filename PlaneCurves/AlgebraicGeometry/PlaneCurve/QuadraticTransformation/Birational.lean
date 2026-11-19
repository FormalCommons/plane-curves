/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.Basic
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.Hypersurface
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.Irreducible

/-!
# The standard quadratic transformation as a map of points

The standard quadratic transformation of `ℙ²` sends `[x : y : z]` to `[yz : xz : xy]`. It is
defined off the three fundamental points, and is an involution of the complement `U` of the
fundamental triangle `xyz = 0`. For every form `F` it maps `V(F) ∖ U` bijectively onto
`V(F') ∖ U`, where `F'` is the proper transform, and it maps every point of `V(F')` that is not
fundamental into `V(F)`. If `F` is irreducible, with no exceptional component, over an
algebraically closed field, then `V(F')` is the closure of the image of `V(F) ∖ U`.

## Main definitions

* `PlaneCurves.Projective.quadraticMap`: the point map `[x : y : z] ↦ [yz : xz : xy]`, with the
  junk value `P` at a fundamental point `P`.

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

## Implementation notes

The library has no Zariski topology on `ℙ²`: the closure of a set `S` of points is
`zeroLocus (vanishingIdeal S)`, the smallest algebraic set that contains it.

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
  have hw : ![v 1 * v 2, v 0 * v 2, v 0 * v 1] ≠ 0 := fun h ↦
    have ⟨i, hi⟩ := (quadVec_eq_zero_iff v hv).1 h
    hP i hi
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
  have hw : ![v 1 * v 2, v 0 * v 2, v 0 * v 1] ≠ 0 := fun h ↦
    have ⟨i, hi⟩ := (quadVec_eq_zero_iff v hv).1 h
    hP i hi
  have hv' : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 := by
    by_contra h
    exact hv (funext fun i ↦ by fin_cases i <;> simp_all)
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
  have hw : ![v 1 * v 2, v 0 * v 2, v 0 * v 1] ≠ 0 := fun h ↦
    have ⟨i, hi⟩ := (quadVec_eq_zero_iff v hv).1 h
    hP i hi
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

/-- An irreducible form `G` with no exceptional component vanishes on every form that vanishes on
`V(G) ∖ V(XYZ)`, over an algebraically closed field: `V(G)` is the closure of
`V(G) ∖ V(XYZ)`. -/
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

end PlaneCurves.Projective

end
