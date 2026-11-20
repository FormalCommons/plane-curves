/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Data.List.Range
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Cubic.NormalForm
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.Resolution.Basic

/-!
# Sequences of quadratic transformations with explicit coordinates

A quadratic transformation centred at a point `P` (`IsQuadraticTransformAt`) is a projective
change of coordinates `T`, given by an invertible matrix `M` with `T([0 : 0 : 1]) = P`, that puts
the curve in excellent position, followed by the proper transform (Fulton, §7.4). To apply the
same transformations to two curves `F` and `G`, as in Noether's formula (Fulton, Problems 7.15
and 7.16), the matrices must be part of the data. This file makes them so.

## Main definitions

* `PlaneCurves.Projective.quadraticTransformSeq M F i`: the curve `Fᵢ` obtained from `F₀ = F`
  by the successive changes of coordinates `M 0, M 1, …` and proper transforms,
  `Fᵢ₊₁ = (Fᵢ(M i X))'`.
* `PlaneCurves.Projective.IsQuadraticTransformSeq M F s`: the first `s` steps are quadratic
  transformations, that is, each `M i` with `i < s` is invertible and `Fᵢ(M i X)` is in
  excellent position. The `i`-th centre is `T_{M i}([0 : 0 : 1])`.

## Main results

* `PlaneCurves.Projective.quadraticTransformSeq_mul`: for forms `F` and `G`, the sequence of
  `F G` is the product of the sequences of `F` and of `G`.
* `PlaneCurves.Projective.isQuadraticTransformSeq_succ_iff`: a sequence of `s + 1` steps is a
  first step followed by a sequence of `s` steps.
* `PlaneCurves.Projective.IsQuadraticTransformSeq.of_mul_left`, `.of_mul_right`: a sequence of
  quadratic transformations of `F G` is one of `F` and one of `G`.
* `PlaneCurves.Projective.IsQuadraticTransformSeq.isChain`: a sequence of quadratic
  transformations is a chain `List.IsChain IsQuadraticTransform`.
* `PlaneCurves.Projective.IsQuadraticTransformSeq.irreducible`,
  `PlaneCurves.Projective.IsQuadraticTransformSeq.isRelPrime`: along a sequence, irreducible
  curves stay irreducible, and relatively prime curves stay relatively prime.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008]
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] {M : ℕ → Matrix (Fin 3) (Fin 3) k}
  {F G : MvPolynomial (Fin 3) k} {n m : ℕ}

/-! ### The curves along a sequence -/

/-- The curves `F = F₀, F₁, …` obtained from `F` by the successive projective changes of
coordinates `M i` and proper transforms: `Fᵢ₊₁` is the proper transform of `Fᵢ(M i X)`. -/
noncomputable def quadraticTransformSeq (M : ℕ → Matrix (Fin 3) (Fin 3) k)
    (F : MvPolynomial (Fin 3) k) : ℕ → MvPolynomial (Fin 3) k
  | 0 => F
  | i + 1 => properTransform (linearSubst (M i) (quadraticTransformSeq M F i))

@[simp]
theorem quadraticTransformSeq_zero (M : ℕ → Matrix (Fin 3) (Fin 3) k)
    (F : MvPolynomial (Fin 3) k) : quadraticTransformSeq M F 0 = F :=
  (rfl)

@[simp]
theorem quadraticTransformSeq_succ (M : ℕ → Matrix (Fin 3) (Fin 3) k)
    (F : MvPolynomial (Fin 3) k) (i : ℕ) :
    quadraticTransformSeq M F (i + 1) =
      properTransform (linearSubst (M i) (quadraticTransformSeq M F i)) :=
  (rfl)

/-- The curves along a sequence, with the first step peeled off: `Fᵢ₊₁` is the `i`-th curve of
the sequence of `F₁` along `M 1, M 2, …`. -/
theorem quadraticTransformSeq_succ' (M : ℕ → Matrix (Fin 3) (Fin 3) k)
    (F : MvPolynomial (Fin 3) k) (i : ℕ) :
    quadraticTransformSeq M F (i + 1) =
      quadraticTransformSeq (fun j ↦ M (j + 1)) (properTransform (linearSubst (M 0) F)) i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [quadraticTransformSeq_succ, ih, quadraticTransformSeq_succ]

/-- The curves along a sequence starting from a form are forms. -/
theorem isHomogeneous_quadraticTransformSeq (hF : F.IsHomogeneous n) (i : ℕ) :
    ∃ d, (quadraticTransformSeq M F i).IsHomogeneous d := by
  induction i with
  | zero => exact ⟨n, hF⟩
  | succ i ih =>
    obtain ⟨d, hd⟩ := ih
    exact ⟨_, (hd.linearSubst (M i)).properTransform⟩

/-- **Multiplicativity**: along a sequence, the curves of a product `F G` of forms are the
products of the curves of `F` and of `G`. -/
theorem quadraticTransformSeq_mul (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous m) (i : ℕ) :
    quadraticTransformSeq M (F * G) i =
      quadraticTransformSeq M F i * quadraticTransformSeq M G i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    obtain ⟨d, hd⟩ := isHomogeneous_quadraticTransformSeq (M := M) hF i
    obtain ⟨e, he⟩ := isHomogeneous_quadraticTransformSeq (M := M) hG i
    rw [quadraticTransformSeq_succ, ih, map_mul,
      properTransform_mul (hd.linearSubst (M i)) (he.linearSubst (M i))]
    rfl

/-! ### Sequences of quadratic transformations -/

/-- The first `s` steps of the sequence of `F` along `M` are quadratic transformations: for
`i < s`, the matrix `M i` is invertible and `Fᵢ(M i X)` is in excellent position. The `i`-th step
is then centred at `T_{M i}([0 : 0 : 1])`. -/
def IsQuadraticTransformSeq (M : ℕ → Matrix (Fin 3) (Fin 3) k) (F : MvPolynomial (Fin 3) k)
    (s : ℕ) : Prop :=
  ∀ i < s, Function.Injective (M i).mulVecLin ∧
    IsExcellentPosition (linearSubst (M i) (quadraticTransformSeq M F i))

theorem isQuadraticTransformSeq_def {s : ℕ} :
    IsQuadraticTransformSeq M F s ↔ ∀ i < s, Function.Injective (M i).mulVecLin ∧
      IsExcellentPosition (linearSubst (M i) (quadraticTransformSeq M F i)) :=
  Iff.rfl

/-- The empty sequence is a sequence of quadratic transformations. -/
@[simp]
theorem isQuadraticTransformSeq_zero (M : ℕ → Matrix (Fin 3) (Fin 3) k)
    (F : MvPolynomial (Fin 3) k) : IsQuadraticTransformSeq M F 0 :=
  fun _ hi ↦ absurd hi (Nat.not_lt_zero _)

/-- A sequence of `s + 1` quadratic transformations is a first quadratic transformation, along
`M 0`, followed by a sequence of `s` of them, along `M 1, M 2, …`. -/
theorem isQuadraticTransformSeq_succ_iff {s : ℕ} :
    IsQuadraticTransformSeq M F (s + 1) ↔
      (Function.Injective (M 0).mulVecLin ∧ IsExcellentPosition (linearSubst (M 0) F)) ∧
        IsQuadraticTransformSeq (fun j ↦ M (j + 1)) (properTransform (linearSubst (M 0) F)) s := by
  simp only [isQuadraticTransformSeq_def, ← quadraticTransformSeq_succ']
  refine ⟨fun h ↦ ⟨h 0 s.succ_pos, fun i hi ↦ h (i + 1) (by omega)⟩, fun ⟨h0, h⟩ i hi ↦ ?_⟩
  rcases i with _ | i
  exacts [h0, h i (by omega)]

namespace IsQuadraticTransformSeq

variable {s : ℕ}

/-- The matrix of a step of a sequence of quadratic transformations is invertible. -/
theorem injective (h : IsQuadraticTransformSeq M F s) {i : ℕ} (hi : i < s) :
    Function.Injective (M i).mulVecLin :=
  (h i hi).1

/-- Before each step of a sequence of quadratic transformations, the curve is in excellent
position in the coordinates of that step. -/
theorem isExcellentPosition (h : IsQuadraticTransformSeq M F s) {i : ℕ} (hi : i < s) :
    IsExcellentPosition (linearSubst (M i) (quadraticTransformSeq M F i)) :=
  (h i hi).2

/-- The first steps of a sequence of quadratic transformations are one. -/
theorem mono (h : IsQuadraticTransformSeq M F s) {s' : ℕ} (hs : s' ≤ s) :
    IsQuadraticTransformSeq M F s' :=
  fun i hi ↦ h i (hi.trans_le hs)

/-- A sequence of quadratic transformations of a product `F G` of forms is one of `F`. -/
theorem of_mul_left (h : IsQuadraticTransformSeq M (F * G) s) (hF : F.IsHomogeneous n)
    (hG : G.IsHomogeneous m) : IsQuadraticTransformSeq M F s := by
  intro i hi
  obtain ⟨hM, hE⟩ := h i hi
  obtain ⟨d, hd⟩ := isHomogeneous_quadraticTransformSeq (M := M) hF i
  obtain ⟨e, he⟩ := isHomogeneous_quadraticTransformSeq (M := M) hG i
  rw [quadraticTransformSeq_mul hF hG, map_mul] at hE
  exact ⟨hM, hE.of_mul_left (hd.linearSubst (M i)) (he.linearSubst (M i))⟩

/-- A sequence of quadratic transformations of a product `F G` of forms is one of `G`. -/
theorem of_mul_right (h : IsQuadraticTransformSeq M (F * G) s) (hF : F.IsHomogeneous n)
    (hG : G.IsHomogeneous m) : IsQuadraticTransformSeq M G s :=
  (mul_comm F G ▸ h).of_mul_left hG hF

/-- The `i`-th step of a sequence of quadratic transformations is a quadratic transformation
centred at `T_{M i}([0 : 0 : 1])`. -/
theorem isQuadraticTransformAt (h : IsQuadraticTransformSeq M F s) {i : ℕ} (hi : i < s) :
    IsQuadraticTransformAt (quadraticTransformSeq M F i)
      (map (M i).mulVecLin (h.injective hi) (fundamentalPoint 2))
      (quadraticTransformSeq M F (i + 1)) :=
  isQuadraticTransformAt_def.2
    ⟨M i, h.injective hi, rfl, h.isExcellentPosition hi, rfl⟩

/-- The curves `F₀, …, F_s` of a sequence of `s` quadratic transformations form a chain of
quadratic transformations. -/
theorem isChain (h : IsQuadraticTransformSeq M F s) :
    List.IsChain IsQuadraticTransform ((List.range (s + 1)).map (quadraticTransformSeq M F)) := by
  rw [List.isChain_map, List.isChain_range_succ]
  exact fun i hi ↦ (h.isQuadraticTransformAt hi).isQuadraticTransform

/-- Along a sequence of quadratic transformations, the curves of an irreducible form are
irreducible. -/
theorem irreducible (h : IsQuadraticTransformSeq M F s) (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) {i : ℕ} (hi : i ≤ s) : Irreducible (quadraticTransformSeq M F i) := by
  induction i with
  | zero => exact hirr
  | succ i ih =>
    obtain ⟨d, hd⟩ := isHomogeneous_quadraticTransformSeq (M := M) hF i
    exact (h.isQuadraticTransformAt hi).irreducible hd (ih (by omega))

/-- Along a sequence of quadratic transformations of a product `F G` of relatively prime forms,
the curves of `F` and of `G` stay relatively prime. -/
theorem isRelPrime (h : IsQuadraticTransformSeq M (F * G) s) (hF : F.IsHomogeneous n)
    (hG : G.IsHomogeneous m) (hFG : IsRelPrime F G) {i : ℕ} (hi : i ≤ s) :
    IsRelPrime (quadraticTransformSeq M F i) (quadraticTransformSeq M G i) := by
  induction i with
  | zero => exact hFG
  | succ i ih =>
    obtain ⟨d, hd⟩ := isHomogeneous_quadraticTransformSeq (M := M) hF i
    obtain ⟨e, he⟩ := isHomogeneous_quadraticTransformSeq (M := M) hG i
    have hM := Matrix.isUnit_det_of_mulVecLin_injective ((h.of_mul_left hF hG) i hi).1
    rw [quadraticTransformSeq_succ, quadraticTransformSeq_succ]
    exact ((isRelPrime_linearSubst_iff hM).2 (ih (by omega))).properTransform
      (hd.linearSubst (M i)) (he.linearSubst (M i)) ((h.of_mul_left hF hG) i hi).2.not_X_dvd
      ((h.of_mul_right hF hG) i hi).2.not_X_dvd

end IsQuadraticTransformSeq

/-! ### Examples -/

/-- In characteristic zero, the nodal cubic `Y²Z = X²(X + Z)` has a sequence of one quadratic
transformation centred at its node `[0 : 0 : 1]`, and the curve it gives is irreducible. -/
example [IsAlgClosed k] [CharZero k] :
    ∃ (M : ℕ → Matrix (Fin 3) (Fin 3) k)
      (h : IsQuadraticTransformSeq M (X 1 ^ 2 * X 2 - X 0 ^ 2 * (X 0 + X 2)) 1),
      map (M 0).mulVecLin (h.injective one_pos) (fundamentalPoint 2) = mk k ![0, 0, 1] (by simp) ∧
        Irreducible (quadraticTransformSeq M (X 1 ^ 2 * X 2 - X 0 ^ 2 * (X 0 + X 2)) 1) := by
  have hX (j : Fin 3) : (X j : MvPolynomial (Fin 3) k).IsHomogeneous 1 := isHomogeneous_X k j
  have hN : (X 1 ^ 2 * X 2 - X 0 ^ 2 * (X 0 + X 2) : MvPolynomial (Fin 3) k).IsHomogeneous 3 :=
    (((hX 1).pow 2).mul (hX 2)).sub (((hX 0).pow 2).mul ((hX 0).add (hX 2)))
  obtain ⟨M, hM, hTP, hE⟩ := exists_isExcellentPosition_of_charZero hN
    irreducible_X_sq_mul_X_sub_X_sq_mul_X_add_X (mk k ![0, 0, 1] (by simp))
  have h : IsQuadraticTransformSeq (fun _ ↦ M) (X 1 ^ 2 * X 2 - X 0 ^ 2 * (X 0 + X 2)) 1 :=
    isQuadraticTransformSeq_succ_iff.2 ⟨⟨hM, hE⟩, isQuadraticTransformSeq_zero _ _⟩
  exact ⟨_, h, hTP, h.irreducible hN irreducible_X_sq_mul_X_sub_X_sq_mul_X_add_X le_rfl⟩

end PlaneCurves.Projective

end
