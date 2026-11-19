/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Cubic.Chord
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Cubic.Residual

/-!
# The group law on a plane cubic

Let `F` be an irreducible cubic over an algebraically closed field and `O` a simple point of `F`.
Fulton's chord–tangent construction (§5.6) makes the simple points of `F` an abelian group with
zero `O`: for simple points `P`, `Q`, with `φ(P, Q) = thirdPoint F P Q` the third point of the
chord through `P` and `Q`,

  `P ⊕ Q = φ(O, φ(P, Q))`,  `-P = φ(P, φ(O, O))`.

The carrier is the structure `CubicGroup F O` of simple points of `F`, which carries `O` as a
parameter, so that the groups for different base points live on different types. The
hypotheses on `F` and `O` are carried by `Fact` instances.

Associativity is Fulton's argument: for simple `P`, `Q`, `R`, the products `L₁L₂L₃` and `M₁M₂M₃`
of six chord lines are cubics that meet `F` in eight common points and in
`φ(φ(O, φ(P, Q)), R)`, respectively `φ(P, φ(O, φ(Q, R)))`. Eight simple points of an irreducible
cubic determine the ninth (`eq_of_intersectionCycle_eq_add_single`), so these agree.

## Main definitions

* `PlaneCurves.Projective.CubicGroup F O`: the simple points of `F`, with base point `O`.
* `PlaneCurves.Projective.CubicGroup.chord`: the third point `φ(P, Q)` on simple points.
* `PlaneCurves.Projective.CubicGroup.instAddCommGroup`: the chord–tangent group law.
* `PlaneCurves.Projective.CubicGroup.changeBase`: change of base point.

## Main results

* `PlaneCurves.Projective.intersectionCycle_chordLine_mul_chordLine_mul_chordLine`: the
  intersection cycle of a product of three chord lines with `F`.
* `PlaneCurves.Projective.thirdPoint_thirdPoint_thirdPoint_assoc`:
  `φ(φ(O, φ(P, Q)), R) = φ(P, φ(O, φ(Q, R)))`.
* `PlaneCurves.Projective.CubicGroup.add_assoc'`: associativity in terms of `thirdPoint`.
* `PlaneCurves.Projective.CubicGroup.point_zero`, `PlaneCurves.Projective.CubicGroup.point_add`,
  `PlaneCurves.Projective.CubicGroup.point_neg`: the group law on points.
* `PlaneCurves.Projective.CubicGroup.chord_eq_sub`: `φ(P, Q) = φ(O, O) - P - Q`.
* `PlaneCurves.Projective.CubicGroup.exists_line_iff_add_add_eq`: `P`, `Q`, `R` are the
  intersection of `F` with a line iff `P + Q + R = φ(O, O)`.
* `PlaneCurves.Projective.CubicGroup.equivZeroLocus`: for a nonsingular `F`, the carrier is the
  curve `V(F)`.
* `PlaneCurves.Projective.CubicGroup.chordTangent_group`: the group law on a plane cubic.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.6
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace
open Finsupp (single)
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 3) k} {O P Q R : ℙ k (Fin 3 → k)}

/-! ### Products of chord lines -/

/-- A product of three chord lines through pairs of simple points of an irreducible cubic `F`
meets `F` in the sum of their intersection cycles, `P₁ + Q₁ + φ(P₁, Q₁) + ⋯`. -/
theorem intersectionCycle_chordLine_mul_chordLine_mul_chordLine [IsAlgClosed k]
    (hF : F.IsHomogeneous 3) (hirr : Irreducible F) {P₁ Q₁ P₂ Q₂ P₃ Q₃ : ℙ k (Fin 3 → k)}
    (hP₁ : IsSimplePoint F P₁) (hQ₁ : IsSimplePoint F Q₁) (hP₂ : IsSimplePoint F P₂)
    (hQ₂ : IsSimplePoint F Q₂) (hP₃ : IsSimplePoint F P₃) (hQ₃ : IsSimplePoint F Q₃) :
    intersectionCycle (chordLine F P₁ Q₁ * chordLine F P₂ Q₂ * chordLine F P₃ Q₃) F =
      (single P₁ 1 + single Q₁ 1 + single (thirdPoint F P₁ Q₁) 1) +
      (single P₂ 1 + single Q₂ 1 + single (thirdPoint F P₂ Q₂) 1) +
      (single P₃ 1 + single Q₃ 1 + single (thirdPoint F P₃ Q₃) 1) := by
  have h₁ := isRelPrime_chordLine (Q := Q₁) hF hirr (by norm_num) (Or.inr hP₁)
  have h₂ := isRelPrime_chordLine (Q := Q₂) hF hirr (by norm_num) (Or.inr hP₂)
  have h₃ := isRelPrime_chordLine (Q := Q₃) hF hirr (by norm_num) (Or.inr hP₃)
  rw [intersectionCycle_mul_left ((isHomogeneous_chordLine F P₁ Q₁).mul
      (isHomogeneous_chordLine F P₂ Q₂)) (isHomogeneous_chordLine F P₃ Q₃) hF (h₁.mul_left h₂) h₃,
    intersectionCycle_mul_left (isHomogeneous_chordLine F P₁ Q₁)
      (isHomogeneous_chordLine F P₂ Q₂) hF h₁ h₂,
    intersectionCycle_chordLine hF hirr hP₁ hQ₁, intersectionCycle_chordLine hF hirr hP₂ hQ₂,
    intersectionCycle_chordLine hF hirr hP₃ hQ₃]

/-- A product of three chord lines through pairs of simple points of an irreducible form `F` of
degree at least two is not a multiple of `F`. -/
theorem not_dvd_chordLine_mul_chordLine_mul_chordLine {d : ℕ} (hF : F.IsHomogeneous d)
    (hirr : Irreducible F) (hd : 2 ≤ d) {P₁ Q₁ P₂ Q₂ P₃ Q₃ : ℙ k (Fin 3 → k)}
    (hP₁ : IsSimplePoint F P₁) (hP₂ : IsSimplePoint F P₂) (hP₃ : IsSimplePoint F P₃) :
    ¬F ∣ chordLine F P₁ Q₁ * chordLine F P₂ Q₂ * chordLine F P₃ Q₃ := fun h ↦
  hirr.not_isUnit <| (((isRelPrime_chordLine (Q := Q₁) hF hirr hd (Or.inr hP₁)).mul_left
    (isRelPrime_chordLine (Q := Q₂) hF hirr hd (Or.inr hP₂))).mul_left
    (isRelPrime_chordLine (Q := Q₃) hF hirr hd (Or.inr hP₃))) h dvd_rfl

/-! ### Associativity -/

/-- **Associativity of the chord–tangent construction** ([Fulton2008], §5.6). For simple points
`O`, `P`, `Q`, `R` of an irreducible cubic, `φ(φ(O, φ(P, Q)), R) = φ(P, φ(O, φ(Q, R)))`. The
cubics `L₁L₂L₃` and `M₁M₂M₃`, products of the chord lines through `P, Q`, through `O, φ(Q, R)`
and through `φ(O, φ(P, Q)), R`, respectively through `Q, R`, through `O, φ(P, Q)` and through
`P, φ(O, φ(Q, R))`, meet `F` in eight common simple points and in the two sides of the
equation, which agree since eight simple points determine the ninth. -/
theorem thirdPoint_thirdPoint_thirdPoint_assoc [IsAlgClosed k] (hF : F.IsHomogeneous 3)
    (hirr : Irreducible F) (hO : IsSimplePoint F O) (hP : IsSimplePoint F P)
    (hQ : IsSimplePoint F Q) (hR : IsSimplePoint F R) :
    thirdPoint F (thirdPoint F O (thirdPoint F P Q)) R =
      thirdPoint F P (thirdPoint F O (thirdPoint F Q R)) := by
  have hs : ∀ {A B}, IsSimplePoint F A → IsSimplePoint F B →
      IsSimplePoint F (thirdPoint F A B) :=
    isSimplePoint_thirdPoint hF hirr
  set S' := thirdPoint F P Q
  set U := thirdPoint F O S'
  set T := thirdPoint F U R
  set S := thirdPoint F Q R
  set U' := thirdPoint F O S
  set T' := thirdPoint F P U'
  have hS' : IsSimplePoint F S' := hs hP hQ
  have hU : IsSimplePoint F U := hs hO hS'
  have hS : IsSimplePoint F S := hs hQ hR
  have hU' : IsSimplePoint F U' := hs hO hS
  set D := single P 1 + single Q 1 + single S' 1 + single O 1 + single S 1 + single U' 1 +
    single U 1 + single R 1
  have hD : ∀ X ∈ D.support, IsSimplePoint F X := fun X hX ↦ by
    by_contra hns
    have hne : ∀ Y, IsSimplePoint F Y → Y ≠ X := fun Y hY h ↦ hns (h ▸ hY)
    simp [D, hne P hP, hne Q hQ, hne S' hS', hne O hO, hne S hS,
      hne U' hU', hne U hU, hne R hR] at hX
  have hhom := isHomogeneous_chordLine (F := F)
  refine (eq_of_intersectionCycle_eq_add_single (D := D) hF hirr
    (G := chordLine F P Q * chordLine F O S * chordLine F U R)
    (H := chordLine F Q R * chordLine F O S' * chordLine F P U')
    (((hhom _ _).mul (hhom _ _)).mul (hhom _ _)) (((hhom _ _).mul (hhom _ _)).mul (hhom _ _))
    (not_dvd_chordLine_mul_chordLine_mul_chordLine hF hirr (by norm_num) hP hO hU)
    (not_dvd_chordLine_mul_chordLine_mul_chordLine hF hirr (by norm_num) hQ hO hP) hD
    (hs hU hR) ?_ ?_).symm
  · rw [intersectionCycle_chordLine_mul_chordLine_mul_chordLine hF hirr hP hQ hO hS hU hR]
    simp only [D, S', U, S, U']
    abel
  · rw [intersectionCycle_chordLine_mul_chordLine_mul_chordLine hF hirr hQ hR hO hS' hP hU']
    simp only [D, S', U, S, U', T']
    abel

/-! ### The group of simple points -/

/-- The simple points of a plane curve `F`, with base point `O`: the carrier of the chord–tangent
group of an irreducible cubic `F` with zero `O`. The point `O` is only a parameter, so that the
groups for different base points live on different types. -/
@[ext]
structure CubicGroup (F : MvPolynomial (Fin 3) k) (O : ℙ k (Fin 3 → k)) where
  /-- The point of the projective plane. -/
  point : ℙ k (Fin 3 → k)
  /-- It is a simple point of `F`. -/
  isSimplePoint : IsSimplePoint F point

namespace CubicGroup

theorem point_injective : Function.Injective (point : CubicGroup F O → ℙ k (Fin 3 → k)) :=
  fun _ _ ↦ CubicGroup.ext

@[simp]
theorem point_inj {A B : CubicGroup F O} : A.point = B.point ↔ A = B :=
  point_injective.eq_iff

@[simp]
theorem mk_point (A : CubicGroup F O) : (⟨A.point, A.isSimplePoint⟩ : CubicGroup F O) = A :=
  (rfl)

/-- The points of `CubicGroup F O` are the simple points of `F`. -/
def equivSubtype : CubicGroup F O ≃ {P // IsSimplePoint F P} where
  toFun A := ⟨A.point, A.isSimplePoint⟩
  invFun P := ⟨P.1, P.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_equivSubtype_apply (A : CubicGroup F O) : (equivSubtype A : ℙ k (Fin 3 → k)) =
    A.point :=
  (rfl)

@[simp]
theorem point_equivSubtype_symm_apply (P : {P // IsSimplePoint F P}) :
    (equivSubtype.symm P : CubicGroup F O).point = P :=
  (rfl)

/-- A simple point of `F` as a point of the group with another base point `O'`. -/
def ofPoint (O' : ℙ k (Fin 3 → k)) (A : CubicGroup F O) : CubicGroup F O' :=
  ⟨A.point, A.isSimplePoint⟩

@[simp]
theorem point_ofPoint (O' : ℙ k (Fin 3 → k)) (A : CubicGroup F O) :
    (ofPoint O' A).point = A.point :=
  (rfl)

@[simp]
theorem ofPoint_ofPoint (O' O'' : ℙ k (Fin 3 → k)) (A : CubicGroup F O) :
    ofPoint O'' (ofPoint O' A) = ofPoint O'' A :=
  (rfl)

@[simp]
theorem ofPoint_self (A : CubicGroup F O) : ofPoint O A = A :=
  (rfl)

section Zero

variable [hO : Fact (IsSimplePoint F O)]

/-- The zero of the chord–tangent group is the base point `O`. -/
instance : Zero (CubicGroup F O) :=
  ⟨⟨O, hO.out⟩⟩

@[simp]
theorem point_zero : (0 : CubicGroup F O).point = O :=
  (rfl)

end Zero

variable [IsAlgClosed k] [hF : Fact (F.IsHomogeneous 3)] [hirr : Fact (Irreducible F)]

/-- The third point `φ(A, B)` of the chord through simple points `A`, `B` of an irreducible cubic,
as a point of the group. -/
noncomputable def chord (A B : CubicGroup F O) : CubicGroup F O :=
  ⟨thirdPoint F A.point B.point, isSimplePoint_thirdPoint hF.out hirr.out A.isSimplePoint
    B.isSimplePoint⟩

@[simp]
theorem point_chord (A B : CubicGroup F O) :
    (chord A B).point = thirdPoint F A.point B.point :=
  (rfl)

theorem chord_comm (A B : CubicGroup F O) : chord A B = chord B A :=
  CubicGroup.ext (thirdPoint_comm hF.out hirr.out A.isSimplePoint B.isSimplePoint)

@[simp]
theorem chord_chord (A B : CubicGroup F O) : chord A (chord A B) = B :=
  CubicGroup.ext (thirdPoint_thirdPoint hF.out hirr.out A.isSimplePoint B.isSimplePoint)

@[simp]
theorem chord_chord' (A B : CubicGroup F O) : chord (chord A B) B = A :=
  CubicGroup.ext (thirdPoint_thirdPoint' hF.out hirr.out A.isSimplePoint B.isSimplePoint)

omit [IsAlgClosed k] hF hirr in
/-- **Associativity of the group law** in terms of `thirdPoint`: for simple points `O`, `P`, `Q`,
`R` of an irreducible cubic, `(P ⊕ Q) ⊕ R = P ⊕ (Q ⊕ R)`, that is,
`φ(O, φ(φ(O, φ(P, Q)), R)) = φ(O, φ(P, φ(O, φ(Q, R))))`. -/
theorem add_assoc' [IsAlgClosed k] (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (hO : IsSimplePoint F O) (hP : IsSimplePoint F P) (hQ : IsSimplePoint F Q)
    (hR : IsSimplePoint F R) :
    thirdPoint F O (thirdPoint F (thirdPoint F O (thirdPoint F P Q)) R) =
      thirdPoint F O (thirdPoint F P (thirdPoint F O (thirdPoint F Q R))) := by
  rw [thirdPoint_thirdPoint_thirdPoint_assoc hF hirr hO hP hQ hR]


variable [hO : Fact (IsSimplePoint F O)]

/-- The sum in the chord–tangent group: `P + Q = φ(O, φ(P, Q))`. -/
noncomputable instance : Add (CubicGroup F O) :=
  ⟨fun A B ↦ chord 0 (chord A B)⟩

/-- The negative in the chord–tangent group: `-P = φ(P, φ(O, O))`. -/
noncomputable instance : Neg (CubicGroup F O) :=
  ⟨fun A ↦ chord A (chord 0 0)⟩

@[simp]
theorem point_add (A B : CubicGroup F O) :
    (A + B).point = thirdPoint F O (thirdPoint F A.point B.point) :=
  (rfl)

@[simp]
theorem point_neg (A : CubicGroup F O) :
    (-A).point = thirdPoint F A.point (thirdPoint F O O) :=
  (rfl)

theorem add_def (A B : CubicGroup F O) : A + B = chord 0 (chord A B) :=
  (rfl)

theorem neg_def (A : CubicGroup F O) : -A = chord A (chord 0 0) :=
  (rfl)

/-- The chord–tangent group law on the simple points of an irreducible cubic `F` with zero `O`
([Fulton2008], §5.6): `P + Q = φ(O, φ(P, Q))` and `-P = φ(P, φ(O, O))`. -/
noncomputable instance instAddCommGroup : AddCommGroup (CubicGroup F O) where
  add_assoc A B C := CubicGroup.ext <| by
    simpa using add_assoc' hF.out hirr.out hO.out A.isSimplePoint B.isSimplePoint
      C.isSimplePoint
  zero_add A := by rw [add_def, chord_chord]
  add_zero A := by rw [add_def, chord_comm A, chord_chord]
  add_comm A B := by rw [add_def, add_def, chord_comm A]
  neg_add_cancel A := by rw [add_def, neg_def, chord_comm (chord A _), chord_chord, chord_chord]
  nsmul := nsmulRec
  zsmul := zsmulRec

/-! ### The collinearity criterion -/

/-- `φ(O, A) = φ(O, O) - A` in the chord–tangent group with zero `O`. -/
theorem chord_zero_eq_sub (A : CubicGroup F O) : chord 0 A = chord 0 0 - A := by
  rw [sub_eq_add_neg, add_def, neg_def, chord_comm A, chord_chord]

/-- The third point of a chord in the chord–tangent group: `φ(A, B) = φ(O, O) - A - B`. -/
theorem chord_eq_sub (A B : CubicGroup F O) : chord A B = chord 0 0 - A - B := by
  have h := chord_zero_eq_sub (chord A B)
  rw [← add_def] at h
  rw [sub_sub, h, sub_sub_cancel]

/-- `φ(C, φ(A, B)) = A + B - C` in the chord–tangent group. -/
theorem chord_chord_eq_add_sub (A B C : CubicGroup F O) : chord C (chord A B) = A + B - C := by
  rw [chord_eq_sub C, chord_eq_sub A B]
  abel

/-- `φ(φ(O, A), B) = A - B` in the chord–tangent group with zero `O`. -/
theorem chord_chord_zero_eq_sub (A B : CubicGroup F O) : chord (chord 0 A) B = A - B := by
  rw [chord_eq_sub (chord 0 A), chord_zero_eq_sub A]
  abel

/-- The difference in the chord–tangent group with zero `O`: `A - B = φ(φ(O, A), B)`. -/
@[simp]
theorem point_sub (A B : CubicGroup F O) :
    (A - B).point = thirdPoint F (thirdPoint F O A.point) B.point := by
  rw [← chord_chord_zero_eq_sub]
  simp

/-- **The collinearity criterion** ([Fulton2008], §5.6). Simple points `A`, `B`, `C` of an
irreducible cubic `F` are the intersection `L • F = A + B + C` of `F` with a line `L` iff
`A + B + C = φ(O, O)` in the chord–tangent group with zero `O`. -/
theorem exists_line_iff_add_add_eq (A B C : CubicGroup F O) :
    (∃ L : MvPolynomial (Fin 3) k, L.IsHomogeneous 1 ∧ L ≠ 0 ∧
      intersectionCycle L F = single A.point 1 + single B.point 1 + single C.point 1) ↔
      A + B + C = chord 0 0 := by
  rw [← thirdPoint_eq_iff hF.out hirr.out A.isSimplePoint B.isSimplePoint, ← point_chord A B,
    point_inj, chord_eq_sub, sub_sub, sub_eq_iff_eq_add, eq_comm, add_comm C]

/-! ### Change of base point -/

section ChangeBase

variable {O' : ℙ k (Fin 3 → k)} [hO' : Fact (IsSimplePoint F O')]

/-- The sum of the group with zero `O'`, computed in the group with zero `O`:
`A +' B = A + B - O'`. -/
theorem ofPoint_add_ofPoint (A B : CubicGroup F O) :
    ofPoint O' A + ofPoint O' B = ofPoint O' (A + B - ofPoint O (0 : CubicGroup F O')) := by
  ext
  rw [← chord_chord_eq_add_sub]
  simp

variable (O O') in
/-- **Change of base point** ([Fulton2008], §5.6, Problem 5.35). For simple points `O`, `O'` of an
irreducible cubic, `P ↦ φ(φ(O, O'), P)` is an isomorphism from the chord–tangent group with zero
`O` to the one with zero `O'`. In the group with zero `O`, it is `P ↦ O' - P`. -/
noncomputable def changeBase : CubicGroup F O ≃+ CubicGroup F O' where
  toFun A := ofPoint O' (ofPoint O (0 : CubicGroup F O') - A)
  invFun B := ⟨thirdPoint F (thirdPoint F O' O) B.point, isSimplePoint_thirdPoint hF.out hirr.out
    (isSimplePoint_thirdPoint hF.out hirr.out hO'.out hO.out) B.isSimplePoint⟩
  left_inv A := by
    ext
    simp [thirdPoint_comm hF.out hirr.out hO'.out hO.out,
      thirdPoint_thirdPoint hF.out hirr.out (isSimplePoint_thirdPoint hF.out hirr.out hO.out
        hO'.out) A.isSimplePoint]
  right_inv B := by
    ext
    simp [thirdPoint_comm hF.out hirr.out hO.out hO'.out,
      thirdPoint_thirdPoint hF.out hirr.out (isSimplePoint_thirdPoint hF.out hirr.out hO'.out
        hO.out) B.isSimplePoint]
  map_add' A B := by
    simp only [ofPoint_add_ofPoint]
    congr 1
    abel

/-- The change of base point in the group with zero `O`: `P ↦ O' - P`. -/
theorem changeBase_apply_eq_sub (A : CubicGroup F O) :
    changeBase O O' A = ofPoint O' (ofPoint O (0 : CubicGroup F O') - A) :=
  (rfl)

/-- The change of base point on points: `P ↦ φ(φ(O, O'), P)`. -/
@[simp]
theorem point_changeBase (A : CubicGroup F O) :
    (changeBase O O' A).point = thirdPoint F (thirdPoint F O O') A.point := by
  simp [changeBase_apply_eq_sub]

@[simp]
theorem changeBase_symm : (changeBase (F := F) O O').symm = changeBase O' O :=
  AddEquiv.ext fun B ↦ CubicGroup.ext (by rw [point_changeBase]; rfl)

/-- The change of base point from `O` to itself is the negation `P ↦ -P`, not the identity. -/
theorem changeBase_self_apply (A : CubicGroup F O) : changeBase O O A = -A :=
  CubicGroup.ext <| by
    rw [point_changeBase, point_neg, thirdPoint_comm hF.out hirr.out
      (isSimplePoint_thirdPoint hF.out hirr.out hO.out hO.out) A.isSimplePoint]

end ChangeBase

end CubicGroup

/-! ### Nonsingular cubics -/

namespace CubicGroup

variable {d : ℕ}

/-- A point of a nonsingular curve `F` as a point of the group of simple points of `F`. -/
def ofMem (hF : F.IsHomogeneous d) (hns : IsNonsingular F)
    (hP : P ∈ ProjectiveSpace.zeroLocus {F}) :
    CubicGroup F O :=
  ⟨P, (isNonsingular_iff_forall_isSimplePoint hF).1 hns P hP⟩

@[simp]
theorem point_ofMem (hF : F.IsHomogeneous d) (hns : IsNonsingular F)
    (hP : P ∈ ProjectiveSpace.zeroLocus {F}) :
    (ofMem (O := O) hF hns hP).point = P :=
  (rfl)

/-- For a nonsingular curve `F`, the points of `CubicGroup F O` are the points of the curve
`V(F)`. A nonsingular cubic over an algebraically closed field is irreducible
(`IsNonsingular.irreducible`), so its chord–tangent group lives on all of `V(F)`. -/
def equivZeroLocus (hF : F.IsHomogeneous d) (hns : IsNonsingular F) :
    CubicGroup F O ≃ ProjectiveSpace.zeroLocus {F} where
  toFun A := ⟨A.point, A.isSimplePoint.mem_zeroLocus hF⟩
  invFun P := ofMem hF hns P.2
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_equivZeroLocus_apply (hF : F.IsHomogeneous d) (hns : IsNonsingular F)
    (A : CubicGroup F O) : (equivZeroLocus hF hns A : ℙ k (Fin 3 → k)) = A.point :=
  (rfl)

@[simp]
theorem point_equivZeroLocus_symm_apply (hF : F.IsHomogeneous d) (hns : IsNonsingular F)
    (P : ProjectiveSpace.zeroLocus {F}) : ((equivZeroLocus (O := O) hF hns).symm P).point = P :=
  (rfl)

/-! ### The group law -/

/-- **The group law on a plane cubic** ([Fulton2008], §5.6, Proposition 4, Problems 5.35, 5.36).
Let `F` be an irreducible cubic over an algebraically closed field and `O` a simple point of `F`.

* (a) For simple points `P`, `Q`, the chord line through `P` and `Q` (the tangent if `P = Q`)
  meets `F` in `P + Q + φ(P, Q)`; every line `L` with `L • F = P + Q + R` is a nonzero multiple
  of it, and `R = φ(P, Q)`; the point `φ(P, Q)` is simple, `φ(P, Q) = φ(Q, P)` and
  `φ(P, φ(P, Q)) = Q`.
* (b) The simple points of `F` form an abelian group `CubicGroup F O` with zero `O`, sum
  `P ⊕ Q = φ(O, φ(P, Q))` and negative `-P = φ(P, φ(O, O))`, in which `A`, `B`, `C` are the
  intersection of `F` with a line iff `A ⊕ B ⊕ C = φ(O, O)`.
* (c) For another simple point `O'`, `P ↦ φ(φ(O, O'), P)` is an isomorphism of the groups with
  zeros `O` and `O'`.

A nonsingular cubic is irreducible (`IsNonsingular.irreducible`), all its points are simple
(`isNonsingular_iff_forall_isSimplePoint`), and `equivZeroLocus` identifies the carrier of the
group with the curve.

Milestone: *Group law on a nonsingular plane cubic*. -/
theorem chordTangent_group [IsAlgClosed k] (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (hO : IsSimplePoint F O) :
    (∀ P Q, IsSimplePoint F P → IsSimplePoint F Q →
      intersectionCycle (chordLine F P Q) F =
          single P 1 + single Q 1 + single (thirdPoint F P Q) 1 ∧
        (∀ (L : MvPolynomial (Fin 3) k) R, L.IsHomogeneous 1 → L ≠ 0 →
          intersectionCycle L F = single P 1 + single Q 1 + single R 1 →
          (∃ c : k, c ≠ 0 ∧ L = c • chordLine F P Q) ∧ R = thirdPoint F P Q) ∧
        IsSimplePoint F (thirdPoint F P Q) ∧ thirdPoint F P Q = thirdPoint F Q P ∧
        thirdPoint F P (thirdPoint F P Q) = Q) ∧
    (letI : Fact (F.IsHomogeneous 3) := ⟨hF⟩
     letI : Fact (Irreducible F) := ⟨hirr⟩
     letI : Fact (IsSimplePoint F O) := ⟨hO⟩
     (∀ A B : CubicGroup F O, (A + B).point = thirdPoint F O (thirdPoint F A.point B.point)) ∧
      (0 : CubicGroup F O).point = O ∧
      (∀ A : CubicGroup F O, (-A).point = thirdPoint F A.point (thirdPoint F O O)) ∧
      ∀ A B C : CubicGroup F O, (∃ L : MvPolynomial (Fin 3) k, L.IsHomogeneous 1 ∧ L ≠ 0 ∧
        intersectionCycle L F = single A.point 1 + single B.point 1 + single C.point 1) ↔
          A + B + C = chord 0 0) ∧
    ∀ O' (hO' : IsSimplePoint F O'),
      letI : Fact (F.IsHomogeneous 3) := ⟨hF⟩
      letI : Fact (Irreducible F) := ⟨hirr⟩
      letI : Fact (IsSimplePoint F O) := ⟨hO⟩
      letI : Fact (IsSimplePoint F O') := ⟨hO'⟩
      ∃ e : CubicGroup F O ≃+ CubicGroup F O',
        ∀ A, (e A).point = thirdPoint F (thirdPoint F O O') A.point := by
  let : Fact (F.IsHomogeneous 3) := ⟨hF⟩
  let : Fact (Irreducible F) := ⟨hirr⟩
  let : Fact (IsSimplePoint F O) := ⟨hO⟩
  refine ⟨fun P Q hP hQ ↦ ⟨intersectionCycle_chordLine hF hirr hP hQ,
    fun L R hL hL0 h ↦ ⟨eq_smul_chordLine_of_intersectionCycle_eq hF hirr hP hL hL0 h,
      eq_thirdPoint_of_intersectionCycle_eq hF hirr hP hQ hL hL0 h⟩,
    isSimplePoint_thirdPoint hF hirr hP hQ, thirdPoint_comm hF hirr hP hQ,
    thirdPoint_thirdPoint hF hirr hP hQ⟩,
    ⟨point_add, point_zero, point_neg, exists_line_iff_add_add_eq⟩, fun O' hO' ↦ ?_⟩
  let : Fact (IsSimplePoint F O') := ⟨hO'⟩
  exact ⟨changeBase O O', point_changeBase⟩

end CubicGroup

end PlaneCurves.Projective

end
