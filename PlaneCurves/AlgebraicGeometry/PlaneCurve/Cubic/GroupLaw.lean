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

## Main results

* `PlaneCurves.Projective.intersectionCycle_chordLine_mul_chordLine_mul_chordLine`: the
  intersection cycle of a product of three chord lines with `F`.
* `PlaneCurves.Projective.thirdPoint_thirdPoint_thirdPoint_assoc`:
  `φ(φ(O, φ(P, Q)), R) = φ(P, φ(O, φ(Q, R)))`.
* `PlaneCurves.Projective.CubicGroup.add_assoc'`: associativity in terms of `thirdPoint`.
* `PlaneCurves.Projective.CubicGroup.point_zero`, `PlaneCurves.Projective.CubicGroup.point_add`,
  `PlaneCurves.Projective.CubicGroup.point_neg`: the group law on points.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.6
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization
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

end CubicGroup

end PlaneCurves.Projective

end
