/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Data.Finsupp.Weight
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Bezout.Basic
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.IntersectionNumber.Properties

/-!
# Intersection cycles of projective plane curves

For forms `F` and `G` in `k[X, Y, Z]` with no common component, the **intersection cycle**
`F • G = ∑_P I(P, F ∩ G) P` is the zero-cycle on `ℙ²` that counts each intersection point with
its intersection number (Fulton, §5.5). Zero-cycles are finitely supported functions
`ℙ² →₀ ℕ`, so `F • G` is `PlaneCurves.Projective.intersectionCycle F G`.

## Main definitions

* `PlaneCurves.Projective.intersectionCycle F G : ℙ k (Fin 3 → k) →₀ ℕ`: the intersection cycle
  `F • G`. It is defined for all polynomials, and is `0` when `I(P, F ∩ G)` is nonzero at
  infinitely many points or infinite at some point.

## Main results

* `intersectionCycle_apply`: for relatively prime forms, `(F • G)(P) = I(P, F ∩ G)`;
  `mem_support_intersectionCycle_iff`: its support is the set of common zeros.
* `intersectionCycle_comm`: `F • G = G • F`.
* `intersectionCycle_mul_left`, `intersectionCycle_mul_right`: `F G • H = F • H + G • H`.
* `intersectionCycle_add_mul`: `F • (G + A F) = F • G`.
* `intersectionCycle_smul_left`, `intersectionCycle_C_left`: scaling `F` does not change `F • G`,
  and a nonzero constant meets nothing.
* `degree_intersectionCycle`: **Bézout's theorem** in the form `deg (F • G) = deg F * deg G`,
  over an algebraically closed field.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.5
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] {F G H F' G' : MvPolynomial (Fin 3) k} {m n e : ℕ}
  {P : ℙ k (Fin 3 → k)}

/-- The points where `I(P, F ∩ G)` is a nonzero natural number lie where it is nonzero. -/
theorem support_toNat_intersectionNumber_subset (F G : MvPolynomial (Fin 3) k) :
    (Function.support fun P ↦ (intersectionNumber P F G).toNat) ⊆
      Function.support fun P ↦ intersectionNumber P F G :=
  fun P hP h0 ↦ hP (by simp [h0])

open Classical in
/-- The **intersection cycle** `F • G = ∑_P I(P, F ∩ G) P` of two plane curves, a zero-cycle on
`ℙ²`. It is `0` unless `I(P, F ∩ G)` is finite at every point and nonzero at only finitely many,
as it is for relatively prime forms (`intersectionCycle_apply`). -/
noncomputable def intersectionCycle (F G : MvPolynomial (Fin 3) k) : ℙ k (Fin 3 → k) →₀ ℕ :=
  if h : (Function.support fun P ↦ intersectionNumber P F G).Finite ∧
      ∀ P, intersectionNumber P F G ≠ ⊤ then
    Finsupp.ofSupportFinite (fun P ↦ (intersectionNumber P F G).toNat)
      (h.1.subset (support_toNat_intersectionNumber_subset F G))
  else 0

open Classical in
theorem intersectionCycle_def (F G : MvPolynomial (Fin 3) k) :
    intersectionCycle F G =
      if h : (Function.support fun P ↦ intersectionNumber P F G).Finite ∧
          ∀ P, intersectionNumber P F G ≠ ⊤ then
        Finsupp.ofSupportFinite (fun P ↦ (intersectionNumber P F G).toNat)
          (h.1.subset (support_toNat_intersectionNumber_subset F G))
      else 0 :=
  (rfl)

/-- The intersection cycle depends only on the intersection numbers. -/
theorem intersectionCycle_congr
    (h : ∀ P, intersectionNumber P F G = intersectionNumber P F' G') :
    intersectionCycle F G = intersectionCycle F' G' := by
  rw [intersectionCycle_def, intersectionCycle_def]
  split_ifs with h1 h2 h2
  · ext P
    simp [h]
  · simp only [h] at h1
    exact absurd h1 h2
  · simp only [← h] at h2
    exact absurd h2 h1
  · rfl

/-- Where the intersection numbers are finite, and nonzero at finitely many points, the
intersection cycle takes the value `I(P, F ∩ G)` at `P`. -/
theorem coe_intersectionCycle_apply_of_finite
    (hfin : (Function.support fun P ↦ intersectionNumber P F G).Finite)
    (htop : ∀ P, intersectionNumber P F G ≠ ⊤) (P : ℙ k (Fin 3 → k)) :
    (intersectionCycle F G P : ℕ∞) = intersectionNumber P F G := by
  rw [intersectionCycle_def, dite_eq_left ⟨hfin, htop⟩, Finsupp.ofSupportFinite_coe,
    ENat.natCast_toNat (htop P)]

/-- For relatively prime forms `F` and `G`, the intersection cycle `F • G` takes the value
`I(P, F ∩ G)` at `P`. -/
theorem intersectionCycle_apply (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n)
    (hFG : IsRelPrime F G) (P : ℙ k (Fin 3 → k)) :
    (intersectionCycle F G P : ℕ∞) = intersectionNumber P F G :=
  coe_intersectionCycle_apply_of_finite (finite_support_intersectionNumber hF hG hFG)
    (fun _ ↦ intersectionNumber_ne_top_of_isRelPrime hF hG hFG) P

/-- For relatively prime forms `F` and `G`, the support of `F • G` is the set of common zeros
of `F` and `G`. -/
theorem mem_support_intersectionCycle_iff (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n)
    (hFG : IsRelPrime F G) :
    P ∈ (intersectionCycle F G).support ↔ eval P.rep F = 0 ∧ eval P.rep G = 0 := by
  rw [Finsupp.mem_support_iff, ← Nat.cast_ne_zero (R := ℕ∞), intersectionCycle_apply hF hG hFG,
    Ne, intersectionNumber_eq_zero_iff hF hG]
  tauto

/-- `F • G = G • F`. -/
theorem intersectionCycle_comm (F G : MvPolynomial (Fin 3) k) :
    intersectionCycle F G = intersectionCycle G F :=
  intersectionCycle_congr fun P ↦ intersectionNumber_comm P F G

/-- `F • (G + A F) = F • G`, for every polynomial `A`; for forms this is Fulton's statement
when `A` is a form of degree `deg G - deg F`. -/
@[simp]
theorem intersectionCycle_add_mul (F G A : MvPolynomial (Fin 3) k) :
    intersectionCycle F (G + A * F) = intersectionCycle F G :=
  intersectionCycle_congr fun P ↦ intersectionNumber_add_mul P F G A

/-- Scaling the first curve does not change the intersection cycle. -/
@[simp]
theorem intersectionCycle_smul_left {c : k} (hc : c ≠ 0) (F G : MvPolynomial (Fin 3) k) :
    intersectionCycle (c • F) G = intersectionCycle F G :=
  intersectionCycle_congr fun P ↦ intersectionNumber_smul_left hc P F G

/-- Scaling the second curve does not change the intersection cycle. -/
@[simp]
theorem intersectionCycle_smul_right {c : k} (hc : c ≠ 0) (F G : MvPolynomial (Fin 3) k) :
    intersectionCycle F (c • G) = intersectionCycle F G :=
  intersectionCycle_congr fun P ↦ intersectionNumber_smul_right hc P F G

/-- A nonzero constant meets no curve: `c • G = 0` for `c ≠ 0`. -/
@[simp]
theorem intersectionCycle_C_left {c : k} (hc : c ≠ 0) (G : MvPolynomial (Fin 3) k) :
    intersectionCycle (C c) G = 0 := by
  ext P
  have h := coe_intersectionCycle_apply_of_finite (F := C c) (G := G) (by simp [hc])
    (by simp [hc]) P
  simpa [hc] using h

/-- No curve meets a nonzero constant: `F • c = 0` for `c ≠ 0`. -/
@[simp]
theorem intersectionCycle_C_right {c : k} (hc : c ≠ 0) (F : MvPolynomial (Fin 3) k) :
    intersectionCycle F (C c) = 0 := by
  rw [intersectionCycle_comm, intersectionCycle_C_left hc]

/-- **Additivity**: for forms `F`, `G` and `H` with `F` and `G` both prime to `H`,
`F G • H = F • H + G • H`. -/
theorem intersectionCycle_mul_left (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n)
    (hH : H.IsHomogeneous e) (hFH : IsRelPrime F H) (hGH : IsRelPrime G H) :
    intersectionCycle (F * G) H = intersectionCycle F H + intersectionCycle G H := by
  ext P
  apply Nat.cast_injective (R := ℕ∞)
  rw [Finsupp.add_apply, Nat.cast_add, intersectionCycle_apply (hF.mul hG) hH (hFH.mul_left hGH),
    intersectionCycle_apply hF hH hFH, intersectionCycle_apply hG hH hGH,
    intersectionNumber_mul_left hF hG hH]

/-- **Additivity**: for forms `F`, `G` and `H` with `F` prime to both `G` and `H`,
`F • G H = F • G + F • H`. -/
theorem intersectionCycle_mul_right (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n)
    (hH : H.IsHomogeneous e) (hFG : IsRelPrime F G) (hFH : IsRelPrime F H) :
    intersectionCycle F (G * H) = intersectionCycle F G + intersectionCycle F H := by
  rw [intersectionCycle_comm, intersectionCycle_mul_left hG hH hF hFG.symm hFH.symm,
    intersectionCycle_comm G, intersectionCycle_comm H]

/-- **Bézout's theorem** for intersection cycles: over an algebraically closed field, for
relatively prime forms `F` and `G` of degrees `m` and `n`, the zero-cycle `F • G` has degree
`mn`. -/
theorem degree_intersectionCycle [IsAlgClosed k] (hF : F.IsHomogeneous m)
    (hG : G.IsHomogeneous n) (hFG : IsRelPrime F G) :
    (intersectionCycle F G).degree = m * n := by
  apply Nat.cast_injective (R := ℕ∞)
  rw [Finsupp.degree_apply, Nat.cast_sum]
  simp_rw [intersectionCycle_apply hF hG hFG]
  exact sum_intersectionNumber_eq_mul hF hG hFG fun P hPF hPG ↦
    (mem_support_intersectionCycle_iff hF hG hFG).2 ⟨hPF, hPG⟩

end PlaneCurves.Projective

end
