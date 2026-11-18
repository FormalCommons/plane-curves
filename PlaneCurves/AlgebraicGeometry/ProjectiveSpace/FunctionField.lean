/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.ZeroLocus
public import PlaneCurves.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# The local ring of projective space at a point

For a field `k` and a point `P ∈ ℙⁿ`, this file defines the homogeneous prime `I(P)` of the
point and the local ring `𝒪_P(ℙⁿ)`: the ring of fractions `f / g` of forms of the same degree
with `g(P) ≠ 0`, that is, the homogeneous localization of `k[X₀, …, Xₙ]` at `I(P)`. A fraction
`f / g` has the value `f(v) / g(v)` at `P`, for any set of homogeneous coordinates `v` of `P`.

## Main definitions

* `PlaneCurves.ProjectiveSpace.pointIdeal P`: the homogeneous prime `I(P)` of the point `P`,
  spanned by the forms that vanish at `P`.
* `PlaneCurves.ProjectiveSpace.localRing P`: the local ring `𝒪_P(ℙⁿ)`, a local `k`-algebra.
* `PlaneCurves.ProjectiveSpace.localRing.evalAt P`: the value at `P`, a `k`-algebra hom
  `𝒪_P(ℙⁿ) →ₐ[k] k`.
* `PlaneCurves.ProjectiveSpace.localRing.residueFieldAlgEquiv P`: the residue field of
  `𝒪_P(ℙⁿ)` is `k`.

## Main results

* `mem_pointIdeal_iff_of_isHomogeneous`, `mem_pointIdeal_mk_iff_of_isHomogeneous`: a form lies
  in `I(P)` iff it vanishes at one, equivalently every, set of homogeneous coordinates of `P`.
* `localRing.evalAt_mk`: the value of `f / g` at `P` is `f(v) / g(v)` for every set of
  homogeneous coordinates `v` of `P`.
* `localRing.ker_evalAt`: the maximal ideal of `𝒪_P(ℙⁿ)` consists of the elements that vanish
  at `P`, and `localRing.isUnit_iff_evalAt_ne_zero`: the units are those that do not.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008]
-/

public section

noncomputable section

open MvPolynomial Projectivization
open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PlaneCurves.ProjectiveSpace

variable {k : Type*} [Field k] {n : ℕ}

/-! ### The ideal of a point -/

/-- The homogeneous prime `I(P)` of a point `P ∈ ℙⁿ`: the homogeneous ideal spanned by the forms
that vanish at `P`. -/
noncomputable def pointIdeal (P : ℙ k (Fin (n + 1) → k)) :
    HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k) :=
  vanishingIdeal {P}

theorem pointIdeal_def (P : ℙ k (Fin (n + 1) → k)) : pointIdeal P = vanishingIdeal {P} :=
  (rfl)

/-- The ideal of a point is prime. -/
instance isPrime_pointIdeal (P : ℙ k (Fin (n + 1) → k)) : (pointIdeal P).toIdeal.IsPrime :=
  isPrime_vanishingIdeal_singleton P

variable {P : ℙ k (Fin (n + 1) → k)} {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ}

/-- A form lies in the ideal of `P` iff it vanishes at the representative of `P`. -/
theorem mem_pointIdeal_iff_of_isHomogeneous (hf : f.IsHomogeneous d) :
    f ∈ pointIdeal P ↔ eval P.rep f = 0 := by
  simp [pointIdeal_def, mem_vanishingIdeal_iff_of_isHomogeneous hf]

/-- A form lies in the ideal of `[v]` iff it vanishes at `v`. -/
theorem mem_pointIdeal_mk_iff_of_isHomogeneous (hf : f.IsHomogeneous d)
    {v : Fin (n + 1) → k} (hv : v ≠ 0) : f ∈ pointIdeal (mk k v hv) ↔ eval v f = 0 := by
  rw [mem_pointIdeal_iff_of_isHomogeneous hf, hf.eval_rep_mk_eq_zero_iff hv]

/-! ### The local ring at a point -/

/-- The local ring `𝒪_P(ℙⁿ)` of projective space at a point `P`: the ring of fractions `f / g`
of forms of the same degree with `g(P) ≠ 0`, the homogeneous localization of
`k[X₀, …, Xₙ]` at the ideal of `P`. -/
abbrev localRing (P : ℙ k (Fin (n + 1) → k)) :=
  HomogeneousLocalization.AtPrime (homogeneousSubmodule (Fin (n + 1)) k) (pointIdeal P).toIdeal

example (P : ℙ k (Fin (n + 1) → k)) : IsLocalRing (localRing P) := inferInstance

example (P : ℙ k (Fin (n + 1) → k)) : Algebra k (localRing P) := inferInstance

namespace localRing

/-- A form not in the ideal of `P` does not vanish at the representative of `P`. -/
theorem eval_rep_ne_zero ⦃i : ℕ⦄ ⦃g : MvPolynomial (Fin (n + 1)) k⦄
    (hg : g ∈ homogeneousSubmodule (Fin (n + 1)) k i)
    (hgP : g ∈ (pointIdeal P).toIdeal.primeCompl) :
    aeval P.rep g ≠ 0 := by
  rw [aeval_eq_eval, Ne,
    ← mem_pointIdeal_iff_of_isHomogeneous ((mem_homogeneousSubmodule i g).1 hg)]
  exact hgP

variable (P) in
/-- The value at `P` of an element of `𝒪_P(ℙⁿ)`: the `k`-algebra hom `𝒪_P(ℙⁿ) →ₐ[k] k` sending
`f / g` to `f(v) / g(v)`, for any set of homogeneous coordinates `v` of `P` (`evalAt_mk`). -/
noncomputable def evalAt : localRing P →ₐ[k] k :=
  HomogeneousLocalization.liftAlgHom _ (pointIdeal P).toIdeal.primeCompl_le_nonZeroDivisors
    (aeval P.rep) eval_rep_ne_zero

variable (P) in
theorem evalAt_def : evalAt P =
    HomogeneousLocalization.liftAlgHom _ (pointIdeal P).toIdeal.primeCompl_le_nonZeroDivisors
      (aeval P.rep) eval_rep_ne_zero :=
  (rfl)

/-- The value at `P` of a fraction `f / g` of forms of the same degree is `f(v) / g(v)`, for every
set of homogeneous coordinates `v` of `P`. -/
theorem evalAt_mk {v : Fin (n + 1) → k} (hv : v ≠ 0) (hP : mk k v hv = P)
    (c : HomogeneousLocalization.NumDenSameDeg (homogeneousSubmodule (Fin (n + 1)) k)
      (pointIdeal P).toIdeal.primeCompl) :
    evalAt P (HomogeneousLocalization.mk c) = eval v c.num / eval v c.den := by
  subst hP
  obtain ⟨u, hu⟩ := exists_smul_eq_mk_rep k v hv
  have hnum := (mem_homogeneousSubmodule _ _).1 c.num.2
  have hden := (mem_homogeneousSubmodule _ _).1 c.den.2
  rw [evalAt_def, HomogeneousLocalization.liftAlgHom_mk, aeval_eq_eval, ← hu, Units.smul_def,
    hnum.eval_smul, hden.eval_smul, mul_div_mul_left _ _ (pow_ne_zero _ u.ne_zero)]

/-- The value at `P` of a fraction `f / g` of forms of the same degree is `f(P) / g(P)`, computed
at the representative of `P`. -/
theorem evalAt_mk_rep
    (c : HomogeneousLocalization.NumDenSameDeg (homogeneousSubmodule (Fin (n + 1)) k)
      (pointIdeal P).toIdeal.primeCompl) :
    evalAt P (HomogeneousLocalization.mk c) = eval P.rep c.num / eval P.rep c.den :=
  evalAt_mk P.rep_ne_zero (mk_rep P) c

/-- The value at `P` of a constant is that constant. -/
@[simp]
theorem evalAt_algebraMap (a : k) : evalAt P (algebraMap k (localRing P) a) = a :=
  (evalAt P).commutes a

variable (P) in
/-- Every element of `k` is the value at `P` of a constant. -/
theorem evalAt_surjective : Function.Surjective (evalAt P) :=
  fun a ↦ ⟨algebraMap k _ a, evalAt_algebraMap a⟩

variable (P) in
/-- The maximal ideal of `𝒪_P(ℙⁿ)` consists of the elements that vanish at `P`. -/
theorem ker_evalAt : RingHom.ker (evalAt P) = IsLocalRing.maximalIdeal (localRing P) :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ (evalAt_surjective P))

/-- An element of `𝒪_P(ℙⁿ)` is a unit iff it does not vanish at `P`. -/
theorem isUnit_iff_evalAt_ne_zero {z : localRing P} : IsUnit z ↔ evalAt P z ≠ 0 := by
  rw [Ne, ← RingHom.mem_ker, ker_evalAt, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]

variable (P) in
/-- The residue field of `𝒪_P(ℙⁿ)` is `k`, through the value at `P`. -/
noncomputable def residueFieldAlgEquiv : IsLocalRing.ResidueField (localRing P) ≃ₐ[k] k :=
  (Ideal.quotientEquivAlgOfEq k (ker_evalAt P)).symm.trans
    (Ideal.quotientKerAlgEquivOfSurjective (evalAt_surjective P))

variable (P) in
theorem residueFieldAlgEquiv_def : residueFieldAlgEquiv P =
    (Ideal.quotientEquivAlgOfEq k (ker_evalAt P)).symm.trans
      (Ideal.quotientKerAlgEquivOfSurjective (evalAt_surjective P)) :=
  (rfl)

/-- The residue-field equivalence sends the residue of `z` to its value at `P`. -/
@[simp]
theorem residueFieldAlgEquiv_residue (z : localRing P) :
    residueFieldAlgEquiv P (IsLocalRing.residue (localRing P) z) = evalAt P z :=
  (rfl)

end localRing

end PlaneCurves.ProjectiveSpace

end

end
