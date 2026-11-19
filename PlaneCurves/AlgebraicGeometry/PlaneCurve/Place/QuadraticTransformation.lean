/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Place.ChangeOfCoordinates
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Place.OrdinaryMultiplePoint
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.Birational
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.Singularities.Chart

/-!
# Places under a quadratic transformation

Let `C : F = 0` be an irreducible projective plane curve with no exceptional component, `F'` its
proper transform under the standard quadratic transformation `Q`, and
`e : k(F) ≅ k(F')`, `G / H ↦ G^Q / H^Q`, the isomorphism of function fields
(`quadraticFunctionFieldEquiv`). Places of `k(F)` move to places of `k(F')` along `e`. This file
computes where their centres go.

Off the fundamental triangle the centre moves by the point map: the centre of the moved place is
the image of the centre. The orders of forms are not invariant, since `ordForm` is normalised by
a form not vanishing at the centre, but their differences are: for forms `G₁`, `G₂` of the same
degree, `ord(G₁) - ord(G₂)` at the moved place is `ord(G₁^Q) - ord(G₂^Q)` at the place. At an
ordinary multiple point `[0 : 0 : 1]` of a curve in good position, the lines `X = 0` and `Y = 0`
are not tangent, so they have order one at every place over the point; it follows that the
moved place is centred at a point `[α : 1 : 0]` with `α ≠ 0`, a point over the centre, which is
simple on `F'` if `F` is in excellent position.

The same holds for a quadratic transformation `G` of `F` centred at a point `P`
(`IsQuadraticTransformAt`), which composes a change of coordinates with the standard one.

## Main results

* `center_map_quadraticFunctionFieldEquiv`: off the fundamental triangle, the centre of the
  moved place is the image of the centre under the point map.
* `ordForm_map_quadraticFunctionFieldEquiv_add`: `ord(G₁) + ord(G₂^Q) = ord(G₂) + ord(G₁^Q)`,
  the first orders at the moved place, the others at the place.
* `center_map_quadraticFunctionFieldEquiv_mem_pointsOverCentre`,
  `isSimplePoint_center_map_quadraticFunctionFieldEquiv`: a place centred at the ordinary
  multiple point `[0 : 0 : 1]` moves to a place centred at a point over the centre, a simple
  point of `F'`.
* `IsQuadraticTransformAt.exists_algEquiv_center`: the same facts for a quadratic transformation
  centred at a point.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.4, §7.5
-/

public section

open MvPolynomial Projectivization TauCeti TauCeti.AlgebraicGeometry PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PlaneCurves.Projective

variable {k : Type*} [Field k] [IsAlgClosed k] {F : MvPolynomial (Fin 3) k} {n : ℕ}
  {hF : F.IsHomogeneous n} [Fact (Irreducible F)] [Fact (Irreducible (properTransform F))]

/-! ### Centres off the fundamental triangle -/

/-- **Centres off the fundamental triangle.** If a place `p` of `k(F)` is centred off the
fundamental triangle, the place `p` moved to `k(F')` along the quadratic transformation of
function fields is centred at the image of the centre of `p` under the point map. -/
theorem center_map_quadraticFunctionFieldEquiv (hX : ∀ i, ¬ X i ∣ F)
    (p : Place k (functionField hF)) (hp : (center hF p).1 ∉ fundamentalTriangle) :
    (center hF.properTransform (p.map (quadraticFunctionFieldEquiv hF hX))).1 =
      quadraticMap (center hF p).1 := by
  have hR : quadraticMap (center hF p).1 ∈ zeroLocus
      (projectivePlaneCurve.ideal hF.properTransform : Set (MvPolynomial (Fin 3) k)) := by
    have h := (quadraticMap_mem_zeroLocus_properTransform_iff hF hp).2 (by
      rw [mem_zeroLocus_iff_eval_rep (by simpa using ⟨n, hF⟩)]
      simpa using (mem_zeroLocus_ideal_iff hF).1 (center hF p).2)
    rw [mem_zeroLocus_iff_eval_rep (by simpa using ⟨_, hF.properTransform⟩)] at h
    exact (mem_zeroLocus_ideal_iff _).2 (by simpa using h)
  exact congrArg Subtype.val ((center_map_eq_iff_of_map_localSubring _
    (map_localSubring_quadraticFunctionFieldEquiv hF hX (R' := ⟨_, hR⟩) hp rfl)).2 rfl)

/-! ### Orders of forms -/

/-- **Orders of forms under the quadratic transformation.** For forms `G₁`, `G₂` of the same
degree and a place `p` of `k(F)`, moved to `k(F')` along the quadratic transformation of function
fields, `ord_{p'}(G₁) - ord_{p'}(G₂) = ord_p(G₁^Q) - ord_p(G₂^Q)`, in the additive form
`ord_{p'}(G₁) + ord_p(G₂^Q) = ord_{p'}(G₂) + ord_p(G₁^Q)`. Only the differences are invariant,
since the order of a form is normalised by a form not vanishing at the centre. -/
theorem ordForm_map_quadraticFunctionFieldEquiv_add (hX : ∀ i, ¬ X i ∣ F)
    (p : Place k (functionField hF)) {m : ℕ} {G₁ G₂ : MvPolynomial (Fin 3) k}
    (hG₁ : G₁.IsHomogeneous m) (hG₂ : G₂.IsHomogeneous m) :
    ordForm hF.properTransform (p.map (quadraticFunctionFieldEquiv hF hX)) hG₁ +
        ordForm hF p hG₂.quadraticTransform =
      ordForm hF.properTransform (p.map (quadraticFunctionFieldEquiv hF hX)) hG₂ +
        ordForm hF p hG₁.quadraticTransform := by
  by_cases hG₂F : properTransform F ∣ G₂
  · have hG₂F' : F ∣ quadraticTransform G₂ :=
      (dvd_quadraticTransform_iff_properTransform_dvd hF Fact.out hX).2 hG₂F
    rw [(ordForm_eq_top_iff _).2 hG₂F, (ordForm_eq_top_iff _).2 hG₂F', add_top, top_add]
  have hG₂F' : ¬ F ∣ quadraticTransform G₂ :=
    (dvd_quadraticTransform_iff_properTransform_dvd hF Fact.out hX).not.2 hG₂F
  rw [ordForm_eq_addValuation_mk_add _ hG₁ hG₂ hG₂F,
    ordForm_eq_addValuation_mk_add p hG₁.quadraticTransform hG₂.quadraticTransform hG₂F',
    Place.addValuation_map, quadraticFunctionFieldEquiv_symm_mk]
  ac_rfl

/-! ### Places over an ordinary multiple point at `[0 : 0 : 1]` -/

omit [IsAlgClosed k] in
/-- A coordinate `Xⱼ` vanishes at the fundamental point `[eᵢ]` iff `j ≠ i`. -/
private theorem eval_rep_fundamentalPoint_X_eq_zero_iff {i j : Fin 3} :
    eval (fundamentalPoint (k := k) i).rep (X j) = 0 ↔ i ≠ j := by
  rw [← fundamentalPoint_mem_zeroLocus_X_iff (k := k),
    mem_zeroLocus_iff_eval_rep (by simpa using ⟨1, isHomogeneous_X k j⟩)]
  simp

omit [Fact (Irreducible (properTransform F))] in
/-- The order of `Xᵢ^Q` at a place centred at an ordinary multiple point `[0 : 0 : 1]` of a curve
in good position: `X^Q = YZ` and `Y^Q = XZ` have order one, `Z^Q = XY` has order two. -/
private theorem ordForm_quadraticTransform_X (h : IsGoodPosition F)
    {p : Place k (functionField hF)} (hp : (center hF p).1 = fundamentalPoint 2)
    (hP : IsOrdinaryMultiplePoint F (fundamentalPoint 2)) :
    ordForm hF p (isHomogeneous_X k 0).quadraticTransform = 1 ∧
      ordForm hF p (isHomogeneous_X k 1).quadraticTransform = 1 ∧
      ordForm hF p (isHomogeneous_X k 2).quadraticTransform = 2 := by
  have h1 : ∀ j : Fin 3, j ≠ 2 → ordForm hF p (isHomogeneous_X k j) = 1 := fun j hj ↦
    ordForm_eq_one_of_not_isTangentAt (hp ▸ hP) (isHomogeneous_X k j) (X_ne_zero j)
      (by rw [hp]; exact eval_rep_fundamentalPoint_X_eq_zero_iff.2 hj.symm)
      (by rw [hp]; exact isGoodPosition_def.1 h 2 j hj.symm) (mem_placesOver_center p)
  have h0 : ordForm hF p (isHomogeneous_X k 2) = 0 :=
    ordForm_eq_zero_of_eval_ne_zero _ (by
      rw [hp, Ne, eval_rep_fundamentalPoint_X_eq_zero_iff]
      simp)
  refine ⟨?_, ?_, ?_⟩
  · rw [ordForm_congr _ ((isHomogeneous_X k 1).mul (isHomogeneous_X k 2)) quadraticTransform_X_zero
      rfl, ordForm_mul (isHomogeneous_X k 1) (isHomogeneous_X k 2), h1 1 (by decide), h0,
      add_zero]
  · rw [ordForm_congr _ ((isHomogeneous_X k 0).mul (isHomogeneous_X k 2)) quadraticTransform_X_one
      rfl, ordForm_mul (isHomogeneous_X k 0) (isHomogeneous_X k 2), h1 0 (by decide), h0,
      add_zero]
  · rw [ordForm_congr _ ((isHomogeneous_X k 0).mul (isHomogeneous_X k 1)) quadraticTransform_X_two
      rfl, ordForm_mul (isHomogeneous_X k 0) (isHomogeneous_X k 1), h1 0 (by decide),
      h1 1 (by decide)]
    rfl

/-- **Places over an ordinary multiple point.** Let `F` be in good position and
`[0 : 0 : 1]` an ordinary multiple point of `F`. A place of `k(F)` centred at `[0 : 0 : 1]`,
moved to `k(F')` along the quadratic transformation of function fields, is centred at a point
over the centre: a point `[α : 1 : 0]` of `F'` with `α ≠ 0`. -/
theorem center_map_quadraticFunctionFieldEquiv_mem_pointsOverCentre (h : IsGoodPosition F)
    (p : Place k (functionField hF)) (hp : (center hF p).1 = fundamentalPoint 2)
    (hP : IsOrdinaryMultiplePoint F (fundamentalPoint 2)) :
    (center hF.properTransform (p.map (quadraticFunctionFieldEquiv hF h.not_X_dvd))).1 ∈
      pointsOverCentre F := by
  obtain ⟨q0, q1, q2⟩ := ordForm_quadraticTransform_X h hp hP
  have e01 := ordForm_map_quadraticFunctionFieldEquiv_add h.not_X_dvd p (isHomogeneous_X k 0)
    (isHomogeneous_X k 1)
  have e21 := ordForm_map_quadraticFunctionFieldEquiv_add h.not_X_dvd p (isHomogeneous_X k 2)
    (isHomogeneous_X k 1)
  rw [q0, q1] at e01
  rw [q1, q2] at e21
  set p' := p.map (quadraticFunctionFieldEquiv hF h.not_X_dvd)
  set c := (center hF.properTransform p').1
  have htop : ∀ i, ordForm hF.properTransform p' (isHomogeneous_X k i) ≠ ⊤ := fun i hi ↦
    not_X_dvd_properTransform hF h.ne_zero i ((irreducible_properTransform hF Fact.out
      h.not_X_dvd).dvd_symm (prime_X (R := k) (i := i)).irreducible ((ordForm_eq_top_iff _).1 hi))
  obtain ⟨a0, ha0⟩ := WithTop.ne_top_iff_exists.1 (htop 0)
  obtain ⟨a1, ha1⟩ := WithTop.ne_top_iff_exists.1 (htop 1)
  obtain ⟨a2, ha2⟩ := WithTop.ne_top_iff_exists.1 (htop 2)
  have hn1 := ordForm_nonneg (Q := p') (isHomogeneous_X k 1)
  have hp0 := ordForm_pos_iff (Q := p') (isHomogeneous_X k 0)
  have hp1 := ordForm_pos_iff (Q := p') (isHomogeneous_X k 1)
  have hp2 := ordForm_pos_iff (Q := p') (isHomogeneous_X k 2)
  have hz0 := ordForm_eq_zero_iff (Q := p') (isHomogeneous_X k 0)
  have hz1 := ordForm_eq_zero_iff (Q := p') (isHomogeneous_X k 1)
  rw [← ha0] at hp0 hz0 e01
  rw [← ha1] at hn1 hp1 hz1 e01 e21
  rw [← ha2] at hp2 e21
  rw [show (2 : WithTop ℤ) = ((2 : ℤ) : WithTop ℤ) from rfl] at e21
  norm_cast at e01 e21 hn1 hp0 hp1 hp2 hz0 hz1
  have hc2 : eval c.rep (X 2) = 0 := hp2.1 (by omega)
  have hc1 : eval c.rep (X 1) ≠ 0 := hz1.1 (by
    by_contra hne
    have h0 := hp0.1 (by omega)
    have h1 := hp1.1 (by omega)
    refine c.rep_ne_zero (funext fun i ↦ ?_)
    fin_cases i
    · simpa using h0
    · simpa using h1
    · simpa using hc2)
  have hc0 : eval c.rep (X 0) ≠ 0 := hz0.1 (by
    by_contra hne
    exact hc1 (hp1.1 (by omega)))
  simp only [pointsOverCentre_def, Set.mem_ofPred_eq]
  refine ⟨?_, fun i hi ↦ ?_⟩
  · rw [mem_zeroLocus_iff_eval_rep (by
      simpa using ⟨⟨_, hF.properTransform⟩, 1, isHomogeneous_X k 2⟩)]
    simpa [hc2] using (mem_zeroLocus_ideal_iff _).1 (center hF.properTransform p').2
  · rw [hi] at hc0 hc1
    fin_cases i
    · exact hc1 (eval_rep_fundamentalPoint_X_eq_zero_iff.2 (by decide))
    · exact hc0 (eval_rep_fundamentalPoint_X_eq_zero_iff.2 (by decide))
    · exact hc0 (eval_rep_fundamentalPoint_X_eq_zero_iff.2 (by decide))

/-- **The points over an ordinary centre are simple**, for places: let `F` be in excellent
position and `[0 : 0 : 1]` an ordinary multiple point of `F`. A place of `k(F)` centred at
`[0 : 0 : 1]`, moved to `k(F')` along the quadratic transformation of function fields, is centred
at a simple point of `F'`. -/
theorem isSimplePoint_center_map_quadraticFunctionFieldEquiv (h : IsExcellentPosition F)
    (p : Place k (functionField hF)) (hp : (center hF p).1 = fundamentalPoint 2)
    (hP : IsOrdinaryMultiplePoint F (fundamentalPoint 2)) :
    IsSimplePoint (properTransform F)
      (center hF.properTransform (p.map (quadraticFunctionFieldEquiv hF h.not_X_dvd))).1 :=
  h.isSimplePoint_of_mem_pointsOverCentre hF (Or.inr hP)
    (center_map_quadraticFunctionFieldEquiv_mem_pointsOverCentre h.isGoodPosition p hp hP)

/-! ### Quadratic transformations centred at a point -/

omit [Fact (Irreducible (properTransform F))] in
/-- **Places along a quadratic transformation centred at a point.** Let `G` be a quadratic
transformation of an irreducible form `F` centred at `P`. There are a change of coordinates `T`,
given by a matrix `M` as in `IsQuadraticTransformAt`, and an isomorphism `e : k(F) ≅ k(G)` such
that, for every place `p` of `k(F)`:

1. if the centre of `p` is `T R` with `R` off the fundamental triangle, the place `p` moved to
   `k(G)` is centred at `Q(R)`;
2. if `P` is an ordinary multiple point of `F` and the centre of `p` is `P`, the moved place is
   centred at a point over the centre of `F^T`, a simple point of `G`. -/
theorem IsQuadraticTransformAt.exists_algEquiv_center {P : ℙ k (Fin 3 → k)}
    {G : MvPolynomial (Fin 3) k} {m : ℕ} (h : IsQuadraticTransformAt F P G)
    (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous m) [Fact (Irreducible G)] :
    ∃ (M : Matrix (Fin 3) (Fin 3) k) (hM : Function.Injective M.mulVecLin),
      map M.mulVecLin hM (fundamentalPoint 2) = P ∧ IsExcellentPosition (linearSubst M F) ∧
        G = properTransform (linearSubst M F) ∧
        ∃ e : functionField hF ≃ₐ[k] functionField hG,
          (∀ (p : Place k (functionField hF)) (R : ℙ k (Fin 3 → k)), R ∉ fundamentalTriangle →
            map M.mulVecLin hM R = (center hF p).1 →
              (center hG (p.map e)).1 = quadraticMap R) ∧
          (IsOrdinaryMultiplePoint F P → ∀ p : Place k (functionField hF), (center hF p).1 = P →
            (center hG (p.map e)).1 ∈ pointsOverCentre (linearSubst M F) ∧
              IsSimplePoint G (center hG (p.map e)).1) := by
  obtain ⟨M, hM, hMP, hE, rfl⟩ := isQuadraticTransformAt_def.1 h
  refine ⟨M, hM, hMP, hE, rfl, ?_⟩
  obtain ⟨M', rfl⟩ : ∃ M' : GL (Fin 3) k, M'.1 = M :=
    ⟨Matrix.nonsingInvUnit M (Matrix.isUnit_det_of_mulVecLin_injective hM), rfl⟩
  have hF' := hF.linearSubst M'.1
  have hI : projectivePlaneCurve.ideal hF'.properTransform = projectivePlaneCurve.ideal hG :=
    HomogeneousIdeal.toIdeal_injective (by
      rw [projectivePlaneCurve.toIdeal_ideal, projectivePlaneCurve.toIdeal_ideal])
  set e₁ := functionField.linearSubstEquiv hF M'
  set e₂ := quadraticFunctionFieldEquiv hF' hE.not_X_dvd
  set e₃ := ProjectiveSpace.functionField.equivOfEq hI
  have hc : ∀ p : Place k (functionField hF),
      (center hG (p.map ((e₁.trans e₂).trans e₃))).1 =
        (center hF'.properTransform ((p.map e₁).map e₂)).1 := fun p ↦ by
    rw [← Place.map_map, ← Place.map_map]
    exact coe_center_map_equivOfEq hI _
  have hR : ∀ (p : Place k (functionField hF)) (R : ℙ k (Fin 3 → k)),
      map M'.1.mulVecLin hM R = (center hF p).1 → (center hF' (p.map e₁)).1 = R :=
    fun p R hR ↦ map_injective _ hM (by rw [hR]; exact map_center_map_linearSubstEquiv p)
  refine ⟨(e₁.trans e₂).trans e₃, fun p R hRT hRp ↦ ?_, fun hP p hp ↦ ?_⟩
  · rw [hc, center_map_quadraticFunctionFieldEquiv hE.not_X_dvd _ (by rwa [hR p R hRp]),
      hR p R hRp]
  · have hp' := hR p _ (hMP.trans hp.symm)
    have hP' : IsOrdinaryMultiplePoint (linearSubst M'.1 F) (fundamentalPoint 2) := by
      rwa [isOrdinaryMultiplePoint_linearSubst_iff hF hM, hMP]
    rw [hc]
    exact ⟨center_map_quadraticFunctionFieldEquiv_mem_pointsOverCentre hE.isGoodPosition _ hp' hP',
      isSimplePoint_center_map_quadraticFunctionFieldEquiv hE _ hp' hP'⟩

end PlaneCurves.Projective

end
