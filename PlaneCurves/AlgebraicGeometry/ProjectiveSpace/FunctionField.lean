/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.LocalRing.LocalSubring
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.ZeroLocus
public import PlaneCurves.RingTheory.GradedAlgebra.HomogeneousLocalization
public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Dehomogenization

/-!
# Function field and local rings of projective space and of a homogeneous prime

For a field `k` and a point `P ∈ ℙⁿ`, this file defines the homogeneous prime `I(P)` of the
point and the local ring `𝒪_P(ℙⁿ)`: the ring of fractions `f / g` of forms of the same degree
with `g(P) ≠ 0`, that is, the homogeneous localization of `R = k[X₀, …, Xₙ]` at `I(P)`. A
fraction `f / g` has the value `f(v) / g(v)` at `P`, for any set of homogeneous coordinates `v`
of `P`.

For a homogeneous prime `I` of `R`, with zero locus `V = V(I)` and homogeneous coordinate ring
`Γ_h(V) = R ⧸ I` graded by `I.quotientGrading`, it defines the function field `k(V)` and, for
`P ∈ V`, the local ring `𝒪_P(V)`, both as a homogeneous localization of `R ⧸ I` and as a local
subring of `k(V)`. A projective variety `V` uses `I = vanishingIdeal V`.

## Main definitions

* `PlaneCurves.ProjectiveSpace.pointIdeal P`: the homogeneous prime `I(P)` of the point `P`,
  spanned by the forms that vanish at `P`.
* `PlaneCurves.ProjectiveSpace.localRing P`: the local ring `𝒪_P(ℙⁿ)`, a local `k`-algebra.
* `PlaneCurves.ProjectiveSpace.localRing.evalAt P`: the value at `P`, a `k`-algebra hom
  `𝒪_P(ℙⁿ) →ₐ[k] k`.
* `PlaneCurves.ProjectiveSpace.localRing.residueFieldAlgEquiv P`: the residue field of
  `𝒪_P(ℙⁿ)` is `k`.
* `PlaneCurves.ProjectiveSpace.quotientPointIdeal I P`: for `P ∈ V(I)`, the image of `I(P)` in
  `R ⧸ I`, a homogeneous prime.
* `PlaneCurves.ProjectiveSpace.functionField I`: the function field `k(V)`, the homogeneous
  localization of `R ⧸ I` at `⊥`; `functionField.mk` is the fraction `f / g`.
* `PlaneCurves.ProjectiveSpace.functionField.equivOfEq h`: the isomorphism `k(V(I)) ≅ k(V(J))`
  for `h : I = J`.
* `PlaneCurves.ProjectiveSpace.varietyLocalRing I P`: the local ring `𝒪_P(V)`, the homogeneous
  localization of `R ⧸ I` at `quotientPointIdeal I P`, with its value map
  `varietyLocalRing.evalAt I P : 𝒪_P(V) →ₐ[k] k` and its inclusion
  `varietyLocalRing.toFunctionField I P` into `k(V)`.
* `PlaneCurves.ProjectiveSpace.localSubring I P`: `𝒪_P(V)` as a local subring of `k(V)`, and
  `localSubringEquiv I P : varietyLocalRing I P ≃ₐ[k] localSubring I P`.
* `PlaneCurves.ProjectiveSpace.functionField.toFractionRing I`: the embedding of `k(V)` into
  the fraction field of `R ⧸ I`.
* `PlaneCurves.ProjectiveSpace.denominators z`, `denominatorIdeal z`: for `z ∈ k(V)`, the forms
  `g ∉ I` with `z = f / g`, and the homogeneous ideal `J(z)` they span.
* `PlaneCurves.ProjectiveSpace.poleSet z`: the pole set of `z ∈ k(V)`, the points `P ∈ V` with
  `z ∉ 𝒪_P(V)`.

## Main results

* `mem_pointIdeal_iff_of_isHomogeneous`, `mem_pointIdeal_mk_iff_of_isHomogeneous`: a form lies
  in `I(P)` iff it vanishes at one, equivalently every, set of homogeneous coordinates of `P`.
* `localRing.evalAt_mk`: the value of `f / g` at `P` is `f(v) / g(v)` for every set of
  homogeneous coordinates `v` of `P`.
* `localRing.ker_evalAt`: the maximal ideal of `𝒪_P(ℙⁿ)` consists of the elements that vanish
  at `P`, and `localRing.isUnit_iff_evalAt_ne_zero`: the units are those that do not.
* `varietyLocalRing.evalAt_mk`, `varietyLocalRing.ker_evalAt`: the same for `𝒪_P(V)`.
* `mem_localSubring_iff`: an element of `k(V)` lies in `𝒪_P(V)` iff it is `f / g` with `f`, `g`
  forms of the same degree and `g(P) ≠ 0`; `mem_maximalIdeal_localSubring_iff`: it lies in the
  maximal ideal iff moreover `f(P) = 0` for some such `f / g`.
* `isFractionRing_localSubring`: `k(V)` is the field of fractions of `𝒪_P(V)`.
* `exists_algebraMap_notMem_range_toFractionRing`: `Γ_h(V) ⊄ k(V)` inside the fraction field of
  `Γ_h(V)`, when `V` is nonempty.
* `functionField.mk_eq_mk_iff`: `f / g = f' / g'` in `k(V)` iff `f g' - f' g ∈ I`.
* `functionField.mk_eq_zero_iff`, `functionField.mk_self`, `functionField.mk_mul_mk_swap`:
  `f / g = 0` iff `f ∈ I`, `f / f = 1` and `(f / g) (g / f) = 1`; `functionField.algebraMap_eq_mk`:
  a constant `a` is `a / 1`.
* `functionField.aeval_mk_X`: a form `f` of degree `m` evaluated at the fractions `Xⱼ / Xᵢ` is
  `f / Xᵢᵐ`, so that `f / g = f(X / Xᵢ) / g(X / Xᵢ)` (`functionField.mk_eq_aeval_div_aeval`).
* `poleSet_eq_inter`: the pole set of `z` is `V(I) ∩ V(J(z))`, and
  `poleSet_eq_zeroLocus_denominatorIdeal`: it is `V(J(z))`. So the pole set is algebraic
  (`exists_poleSet_eq_zeroLocus`).

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

/-! ### The point ideal in the homogeneous coordinate ring -/

section Variety

variable (I : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k))

/-- A point is a zero of a homogeneous ideal `I` iff `I` lies in the ideal of the point. -/
theorem mem_zeroLocus_iff_le_pointIdeal :
    P ∈ zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)) ↔ I ≤ pointIdeal P := by
  rw [← Set.singleton_subset_iff, subset_zeroLocus_iff_le_vanishingIdeal, pointIdeal_def]

variable {I} in
/-- At a zero `P` of `I`, a form with `g(P) ≠ 0` does not lie in `I`. -/
theorem notMem_of_eval_rep_ne_zero (hP : P ∈ zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)))
    {g : MvPolynomial (Fin (n + 1)) k} (hg : g.IsHomogeneous d) (hgP : eval P.rep g ≠ 0) :
    g ∉ I := fun h ↦
  hgP ((mem_pointIdeal_iff_of_isHomogeneous hg).1 ((mem_zeroLocus_iff_le_pointIdeal I).1 hP h))

/-- For a zero `P` of a homogeneous ideal `I`, the ideal of `P` in the homogeneous coordinate ring
`k[X₀, …, Xₙ] ⧸ I`: the image of `I(P)`, a homogeneous ideal for the grading of `R ⧸ I`. -/
noncomputable def quotientPointIdeal (P : zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k))) :
    HomogeneousIdeal I.quotientGrading where
  __ := (pointIdeal P.1).toIdeal.map (Ideal.Quotient.mk I.toIdeal)
  is_homogeneous' := by
    change Ideal.IsHomogeneous _ (Ideal.map _ _)
    obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists _ _).1 (pointIdeal P.1).isHomogeneous
    rw [hS, Ideal.map_span]
    refine Ideal.homogeneous_span _ _ ?_
    rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
    obtain ⟨i, hi⟩ := x.2
    exact ⟨i, TauCeti.GradedAlgebra.mk_mem_quotientPiece _ _ hi⟩

variable (P : zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)))

theorem quotientPointIdeal_toIdeal :
    (quotientPointIdeal I P).toIdeal = (pointIdeal P.1).toIdeal.map (Ideal.Quotient.mk I.toIdeal) :=
  (rfl)

variable {I P} in
/-- The class of a polynomial lies in the ideal of `P` in `R ⧸ I` iff the polynomial lies in
`I(P)`. -/
theorem mk_mem_quotientPointIdeal_iff {f : MvPolynomial (Fin (n + 1)) k} :
    Ideal.Quotient.mk I.toIdeal f ∈ quotientPointIdeal I P ↔ f ∈ pointIdeal P.1 := by
  rw [← HomogeneousIdeal.mem_iff, quotientPointIdeal_toIdeal,
    Ideal.mem_quotient_iff_mem ((mem_zeroLocus_iff_le_pointIdeal I).1 P.2)]
  rfl

variable {I P} in
/-- The class of a form lies in the ideal of `P` in `R ⧸ I` iff the form vanishes at `P`. -/
theorem mk_mem_quotientPointIdeal_iff_of_isHomogeneous {f : MvPolynomial (Fin (n + 1)) k}
    (hf : f.IsHomogeneous d) :
    Ideal.Quotient.mk I.toIdeal f ∈ quotientPointIdeal I P ↔ eval P.1.rep f = 0 := by
  rw [mk_mem_quotientPointIdeal_iff, mem_pointIdeal_iff_of_isHomogeneous hf]

/-- The ideal of a point in the homogeneous coordinate ring is prime. -/
instance isPrime_quotientPointIdeal : (quotientPointIdeal I P).toIdeal.IsPrime := by
  rw [quotientPointIdeal_toIdeal]
  refine Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective ?_
  rw [Ideal.mk_ker]
  exact (mem_zeroLocus_iff_le_pointIdeal I).1 P.2

/-! ### The local ring at a point -/

/-- The local ring `𝒪_P(V)` of `V = V(I)` at a zero `P` of the homogeneous ideal `I`: the ring of
fractions `f / g` of forms of the same degree with `g(P) ≠ 0`, the homogeneous localization of
`R ⧸ I` at the ideal of `P`. -/
abbrev varietyLocalRing :=
  HomogeneousLocalization.AtPrime I.quotientGrading (quotientPointIdeal I P).toIdeal

example : IsLocalRing (varietyLocalRing I P) := inferInstance

example : Algebra k (varietyLocalRing I P) := inferInstance

namespace varietyLocalRing

variable {I P}

/-- The element `f / g` of `𝒪_P(V)`, for forms `f`, `g` of the same degree with `g(P) ≠ 0`. -/
noncomputable def mk {f g : MvPolynomial (Fin (n + 1)) k} (hf : f.IsHomogeneous d)
    (hg : g.IsHomogeneous d) (hgP : eval P.1.rep g ≠ 0) : varietyLocalRing I P :=
  HomogeneousLocalization.mk ⟨d, ⟨_, I.mk_mem_quotientGrading hf⟩,
    ⟨_, I.mk_mem_quotientGrading hg⟩,
    fun h ↦ hgP ((mk_mem_quotientPointIdeal_iff_of_isHomogeneous hg).1 h)⟩

theorem mk_def {f g : MvPolynomial (Fin (n + 1)) k} (hf : f.IsHomogeneous d)
    (hg : g.IsHomogeneous d) (hgP : eval P.1.rep g ≠ 0) :
    mk (I := I) hf hg hgP =
      HomogeneousLocalization.mk ⟨d, ⟨_, I.mk_mem_quotientGrading hf⟩,
        ⟨_, I.mk_mem_quotientGrading hg⟩,
        fun h ↦ hgP ((mk_mem_quotientPointIdeal_iff_of_isHomogeneous hg).1 h)⟩ :=
  (rfl)

/-- Every element of `𝒪_P(V)` is a fraction `f / g` of forms of the same degree with
`g(P) ≠ 0`. -/
theorem exists_eq_mk (z : varietyLocalRing I P) :
    ∃ (d : ℕ) (f g : MvPolynomial (Fin (n + 1)) k) (hf : f.IsHomogeneous d)
      (hg : g.IsHomogeneous d) (hgP : eval P.1.rep g ≠ 0), z = mk hf hg hgP := by
  obtain ⟨⟨d, ⟨_, hx⟩, ⟨_, hy⟩, hden⟩, rfl⟩ := HomogeneousLocalization.mk_surjective z
  obtain ⟨f, hf, rfl⟩ := I.exists_isHomogeneous_mk_eq hx
  obtain ⟨g, hg, rfl⟩ := I.exists_isHomogeneous_mk_eq hy
  exact ⟨d, f, g, hf, hg, fun h ↦ hden ((mk_mem_quotientPointIdeal_iff_of_isHomogeneous hg).2 h),
    rfl⟩

/-- A homogeneous element of `R ⧸ I` outside the ideal of `P` does not vanish at `P`. -/
theorem liftₐ_ne_zero ⦃i : ℕ⦄ ⦃x : MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal⦄
    (hx : x ∈ I.quotientGrading i) (hxP : x ∈ (quotientPointIdeal I P).toIdeal.primeCompl) :
    Ideal.Quotient.liftₐ I.toIdeal (aeval P.1.rep) (fun _ h ↦
      (mem_zeroLocus_iff_le_ker I.isHomogeneous).1 P.2 h) x ≠ 0 := by
  obtain ⟨g, hg, rfl⟩ := I.exists_isHomogeneous_mk_eq hx
  change aeval P.1.rep g ≠ 0
  rw [aeval_eq_eval]
  exact fun h ↦ hxP ((mk_mem_quotientPointIdeal_iff_of_isHomogeneous hg).2 h)

end varietyLocalRing

/-! ### The function field -/

variable [I.toIdeal.IsPrime]

/-- The function field `k(V)` of a homogeneous prime `I`: the field of fractions `f / g` of forms
of the same degree with `g ∉ I`, the homogeneous localization of `R ⧸ I` at `⊥`. -/
abbrev functionField :=
  HomogeneousLocalization.AtPrime I.quotientGrading
    (⊥ : Ideal (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal))

example : Field (functionField I) := inferInstance

example : Algebra k (functionField I) := inferInstance

variable {I} in
/-- The rational function `f / g` in `k(V)`, for forms `f`, `g` of the same degree with
`g ∉ I`. -/
noncomputable def functionField.mk {f g : MvPolynomial (Fin (n + 1)) k} (hf : f.IsHomogeneous d)
    (hg : g.IsHomogeneous d) (hgI : g ∉ I) : functionField I :=
  HomogeneousLocalization.mk ⟨d, ⟨_, I.mk_mem_quotientGrading hf⟩,
    ⟨_, I.mk_mem_quotientGrading hg⟩,
    fun h ↦ hgI (Ideal.Quotient.eq_zero_iff_mem.1 h)⟩

variable {I} in
theorem functionField.mk_def {f g : MvPolynomial (Fin (n + 1)) k} (hf : f.IsHomogeneous d)
    (hg : g.IsHomogeneous d) (hgI : g ∉ I) :
    functionField.mk hf hg hgI =
      HomogeneousLocalization.mk ⟨d, ⟨_, I.mk_mem_quotientGrading hf⟩,
        ⟨_, I.mk_mem_quotientGrading hg⟩, fun h ↦ hgI (Ideal.Quotient.eq_zero_iff_mem.1 h)⟩ :=
  (rfl)

variable {I} in
/-- Every element of `k(V)` is a fraction `f / g` of forms of the same degree with `g ∉ I`. -/
theorem functionField.exists_eq_mk (z : functionField I) :
    ∃ (d : ℕ) (f g : MvPolynomial (Fin (n + 1)) k) (hf : f.IsHomogeneous d)
      (hg : g.IsHomogeneous d) (hgI : g ∉ I), z = functionField.mk hf hg hgI := by
  obtain ⟨⟨d, ⟨_, hx⟩, ⟨_, hy⟩, hden⟩, rfl⟩ := HomogeneousLocalization.mk_surjective z
  obtain ⟨f, hf, rfl⟩ := I.exists_isHomogeneous_mk_eq hx
  obtain ⟨g, hg, rfl⟩ := I.exists_isHomogeneous_mk_eq hy
  exact ⟨d, f, g, hf, hg, fun h ↦ hden (Ideal.Quotient.eq_zero_iff_mem.2 h), rfl⟩

variable {I} in
/-- A fraction `f / g` with `f ∉ I` is nonzero in `k(V)`. -/
theorem functionField.mk_ne_zero {f g : MvPolynomial (Fin (n + 1)) k} (hf : f.IsHomogeneous d)
    (hg : g.IsHomogeneous d) (hgI : g ∉ I) (hfI : f ∉ I) : functionField.mk hf hg hgI ≠ 0 := by
  intro h0
  have h1 := HomogeneousLocalization.mk_mul_mk_swap (𝒜 := I.quotientGrading)
    ⟨_, I.mk_mem_quotientGrading hf⟩ ⟨_, I.mk_mem_quotientGrading hg⟩
    (fun h ↦ hfI (Ideal.Quotient.eq_zero_iff_mem.1 (Ideal.mem_bot.1 h)))
    (fun h ↦ hgI (Ideal.Quotient.eq_zero_iff_mem.1 (Ideal.mem_bot.1 h)))
  rw [functionField.mk_def] at h0
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

variable {I} in
/-- In `k(V)`, `(f / h) / (g / h) = f / g` for forms `f`, `g`, `h` of the same degree. -/
theorem functionField.mk_div_mk {f g h : MvPolynomial (Fin (n + 1)) k} (hf : f.IsHomogeneous d)
    (hg : g.IsHomogeneous d) (hh : h.IsHomogeneous d) (hgI : g ∉ I) (hhI : h ∉ I) :
    functionField.mk hf hh hhI / functionField.mk hg hh hhI = functionField.mk hf hg hgI := by
  rw [div_eq_iff (functionField.mk_ne_zero hg hh hhI hgI), functionField.mk_def,
    functionField.mk_def, functionField.mk_def, ← HomogeneousLocalization.mk_mul,
    HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk,
    HomogeneousLocalization.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by
    simp only [HomogeneousLocalization.NumDenSameDeg.num_mul,
      HomogeneousLocalization.NumDenSameDeg.den_mul]
    ring⟩

variable {I} in
/-- The isomorphism `k(V(I)) ≅ k(V(J))` of the function fields of equal homogeneous primes
`I = J`, sending `f / g` to `f / g` (`functionField.equivOfEq_mk`). -/
noncomputable def functionField.equivOfEq
    {J : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k)} [J.toIdeal.IsPrime]
    (h : I = J) : functionField I ≃ₐ[k] functionField J := by
  subst h
  exact AlgEquiv.refl

variable {I} in
/-- The isomorphism `k(V(I)) ≅ k(V(J))` for `I = J` sends `f / g` to `f / g`. -/
@[simp]
theorem functionField.equivOfEq_mk
    {J : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k)} [J.toIdeal.IsPrime]
    (h : I = J) {f g : MvPolynomial (Fin (n + 1)) k} (hf : f.IsHomogeneous d)
    (hg : g.IsHomogeneous d) (hgI : g ∉ I) :
    functionField.equivOfEq h (functionField.mk hf hg hgI) =
      functionField.mk hf hg (h ▸ hgI) := by
  subst h
  rfl

namespace varietyLocalRing

variable {I P}

variable (I P) in
/-- The value at `P` of an element of `𝒪_P(V)`: the `k`-algebra hom `𝒪_P(V) →ₐ[k] k` sending
`f / g` to `f(v) / g(v)`, for any set of homogeneous coordinates `v` of `P` (`evalAt_mk`). -/
noncomputable def evalAt : varietyLocalRing I P →ₐ[k] k :=
  HomogeneousLocalization.liftAlgHom _
    (quotientPointIdeal I P).toIdeal.primeCompl_le_nonZeroDivisors _ liftₐ_ne_zero

variable (I P) in
theorem evalAt_def : evalAt I P =
    HomogeneousLocalization.liftAlgHom _
      (quotientPointIdeal I P).toIdeal.primeCompl_le_nonZeroDivisors _ liftₐ_ne_zero :=
  (rfl)

/-- The value at `P` of `f / g` is `f(P) / g(P)`, computed at the representative of `P`. -/
theorem evalAt_mk_rep {f g : MvPolynomial (Fin (n + 1)) k} (hf : f.IsHomogeneous d)
    (hg : g.IsHomogeneous d) (hgP : eval P.1.rep g ≠ 0) :
    evalAt I P (mk hf hg hgP) = eval P.1.rep f / eval P.1.rep g := by
  rw [evalAt_def, mk_def, HomogeneousLocalization.liftAlgHom_mk]
  rfl

/-- The value at `P` of `f / g` is `f(v) / g(v)`, for every set of homogeneous coordinates `v` of
`P`. -/
theorem evalAt_mk {v : Fin (n + 1) → k} (hv : v ≠ 0) (hvP : Projectivization.mk k v hv = P.1)
    {f g : MvPolynomial (Fin (n + 1)) k} (hf : f.IsHomogeneous d) (hg : g.IsHomogeneous d)
    (hgP : eval P.1.rep g ≠ 0) : evalAt I P (mk hf hg hgP) = eval v f / eval v g := by
  obtain ⟨u, hu⟩ := exists_smul_eq_mk_rep k v hv
  rw [evalAt_mk_rep, ← hvP, ← hu, Units.smul_def, hf.eval_smul, hg.eval_smul,
    mul_div_mul_left _ _ (pow_ne_zero _ u.ne_zero)]

/-- The value at `P` of a constant is that constant. -/
@[simp]
theorem evalAt_algebraMap (a : k) : evalAt I P (algebraMap k (varietyLocalRing I P) a) = a :=
  (evalAt I P).commutes a

variable (I P) in
/-- Every element of `k` is the value at `P` of a constant. -/
theorem evalAt_surjective : Function.Surjective (evalAt I P) :=
  fun a ↦ ⟨algebraMap k _ a, evalAt_algebraMap a⟩

variable (I P) in
/-- The maximal ideal of `𝒪_P(V)` consists of the elements that vanish at `P`. -/
theorem ker_evalAt : RingHom.ker (evalAt I P) = IsLocalRing.maximalIdeal (varietyLocalRing I P) :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ (evalAt_surjective I P))

/-- An element of `𝒪_P(V)` is a unit iff it does not vanish at `P`. -/
theorem isUnit_iff_evalAt_ne_zero {z : varietyLocalRing I P} : IsUnit z ↔ evalAt I P z ≠ 0 := by
  rw [Ne, ← RingHom.mem_ker, ker_evalAt, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]

variable (I P) in
/-- The inclusion of `𝒪_P(V)` into the function field `k(V)`, sending `f / g` to `f / g`. -/
noncomputable def toFunctionField : varietyLocalRing I P →ₐ[k] functionField I where
  __ := HomogeneousLocalization.mapId I.quotientGrading
    ((quotientPointIdeal I P).toIdeal.primeCompl_le_nonZeroDivisors.trans
      Ideal.primeCompl_bot.ge)
  commutes' _ := rfl

variable (I P) in
theorem toRingHom_toFunctionField : (toFunctionField I P : varietyLocalRing I P →+* _) =
    HomogeneousLocalization.mapId I.quotientGrading
      ((quotientPointIdeal I P).toIdeal.primeCompl_le_nonZeroDivisors.trans
        Ideal.primeCompl_bot.ge) :=
  (rfl)

@[simp]
theorem toFunctionField_mk {f g : MvPolynomial (Fin (n + 1)) k} (hf : f.IsHomogeneous d)
    (hg : g.IsHomogeneous d) (hgP : eval P.1.rep g ≠ 0) :
    toFunctionField I P (mk hf hg hgP) =
      functionField.mk hf hg (notMem_of_eval_rep_ne_zero P.2 hg hgP) :=
  (rfl)

variable (I P) in
/-- The inclusion of `𝒪_P(V)` into `k(V)` is injective. -/
theorem toFunctionField_injective : Function.Injective (toFunctionField I P) :=
  HomogeneousLocalization.mapId_atPrime_bot_injective _
    ((quotientPointIdeal I P).toIdeal.primeCompl_le_nonZeroDivisors.trans Ideal.primeCompl_bot.ge)

end varietyLocalRing

/-! ### The local subring of the function field at a point -/

/-- The local ring `𝒪_P(V)` of `V = V(I)` at `P`, as a local subring of the function field: the
rational functions `f / g` with `f`, `g` forms of the same degree and `g(P) ≠ 0`
(`mem_localSubring_iff`). -/
noncomputable def localSubring : LocalSubring (functionField I) :=
  LocalSubring.range (varietyLocalRing.toFunctionField I P : varietyLocalRing I P →+* _)

theorem localSubring_toSubring : (localSubring I P).toSubring =
    (varietyLocalRing.toFunctionField I P : varietyLocalRing I P →+* _).range :=
  LocalSubring.range_toSubring _

variable {I P} in
/-- An element of `k(V)` lies in `𝒪_P(V)` iff it lies in the image of `varietyLocalRing I P`. -/
theorem mem_localSubring_iff_exists {z : functionField I} :
    z ∈ (localSubring I P).toSubring ↔ ∃ y, varietyLocalRing.toFunctionField I P y = z := by
  rw [localSubring_toSubring]
  rfl

/-- The local subring `𝒪_P(V)` is a `k`-algebra: it contains the constants. -/
noncomputable instance : Algebra k (localSubring I P).toSubring :=
  ((algebraMap k (functionField I)).codRestrict _ fun a ↦
    mem_localSubring_iff_exists.2 ⟨_, (varietyLocalRing.toFunctionField I P).commutes a⟩).toAlgebra

@[simp]
theorem coe_algebraMap_localSubring (a : k) :
    ((algebraMap k (localSubring I P).toSubring a : (localSubring I P).toSubring) :
      functionField I) = algebraMap k (functionField I) a :=
  (rfl)

/-- The equivalence between the homogeneous localization `varietyLocalRing I P` and the local
subring `𝒪_P(V)` of the function field. -/
noncomputable def localSubringEquiv : varietyLocalRing I P ≃ₐ[k] (localSubring I P).toSubring :=
  AlgEquiv.ofBijective
    { toRingHom := (varietyLocalRing.toFunctionField I P : varietyLocalRing I P →+* _).codRestrict
        (localSubring I P).toSubring fun y ↦ mem_localSubring_iff_exists.2 ⟨y, rfl⟩
      commutes' := fun a ↦ Subtype.ext <| by
        exact (varietyLocalRing.toFunctionField I P).commutes a }
    ⟨fun _ _ h ↦ varietyLocalRing.toFunctionField_injective I P (congrArg Subtype.val h),
      fun ⟨_, hz⟩ ↦ by
        obtain ⟨y, rfl⟩ := mem_localSubring_iff_exists.1 hz
        exact ⟨y, rfl⟩⟩

@[simp]
theorem coe_localSubringEquiv (y : varietyLocalRing I P) :
    (localSubringEquiv I P y : functionField I) = varietyLocalRing.toFunctionField I P y :=
  (rfl)

variable {I P} in
/-- An element of `k(V)` lies in `𝒪_P(V)` iff it is a fraction `f / g` of forms of the same
degree with `g(P) ≠ 0`. -/
theorem mem_localSubring_iff {z : functionField I} :
    z ∈ (localSubring I P).toSubring ↔
      ∃ (d : ℕ) (f g : MvPolynomial (Fin (n + 1)) k) (hf : f.IsHomogeneous d)
        (hg : g.IsHomogeneous d) (hgP : eval P.1.rep g ≠ 0),
        z = functionField.mk hf hg (notMem_of_eval_rep_ne_zero P.2 hg hgP) := by
  rw [mem_localSubring_iff_exists]
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨d, f, g, hf, hg, hgP, rfl⟩ := varietyLocalRing.exists_eq_mk y
    exact ⟨d, f, g, hf, hg, hgP, rfl⟩
  · rintro ⟨d, f, g, hf, hg, hgP, rfl⟩
    exact ⟨varietyLocalRing.mk hf hg hgP, rfl⟩

variable {I P} in
/-- An element of `𝒪_P(V)` lies in its maximal ideal iff it is a fraction `f / g` of forms of the
same degree with `f(P) = 0` and `g(P) ≠ 0`. -/
theorem mem_maximalIdeal_localSubring_iff {z : (localSubring I P).toSubring} :
    z ∈ IsLocalRing.maximalIdeal (localSubring I P).toSubring ↔
      ∃ (d : ℕ) (f g : MvPolynomial (Fin (n + 1)) k) (hf : f.IsHomogeneous d)
        (hg : g.IsHomogeneous d) (hgP : eval P.1.rep g ≠ 0), eval P.1.rep f = 0 ∧
        (z : functionField I) = functionField.mk hf hg (notMem_of_eval_rep_ne_zero P.2 hg hgP) := by
  obtain ⟨y, rfl⟩ := (localSubringEquiv I P).surjective z
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    MulEquiv.isUnit_map (f := localSubringEquiv I P), ← mem_nonunits_iff,
    ← IsLocalRing.mem_maximalIdeal, ← varietyLocalRing.ker_evalAt, RingHom.mem_ker,
    coe_localSubringEquiv]
  constructor
  · intro hy
    obtain ⟨d, f, g, hf, hg, hgP, rfl⟩ := varietyLocalRing.exists_eq_mk y
    rw [varietyLocalRing.evalAt_mk_rep, div_eq_zero_iff, or_iff_left hgP] at hy
    exact ⟨d, f, g, hf, hg, hgP, hy, rfl⟩
  · rintro ⟨d, f, g, hf, hg, hgP, hfP, h⟩
    rw [← varietyLocalRing.toFunctionField_mk hf hg hgP] at h
    rw [varietyLocalRing.toFunctionField_injective I P h, varietyLocalRing.evalAt_mk_rep, hfP,
      zero_div]

/-- **`k(V)` is the field of fractions of `𝒪_P(V)`**: `f / g = (f / Xᵢᵐ) / (g / Xᵢᵐ)` for a
coordinate `Xᵢ` not vanishing at `P`. -/
instance isFractionRing_localSubring :
    IsFractionRing (localSubring I P).toSubring (functionField I) := by
  refine IsFractionRing.of_field _ _ fun z ↦ ?_
  obtain ⟨i, hi⟩ := P.1.exists_mem_affineOpen
  have hiP : eval P.1.rep (X i) ≠ 0 := by simpa using (mem_affineOpen_iff _ _).1 hi
  obtain ⟨m, f, g, hf, hg, hgI, rfl⟩ := functionField.exists_eq_mk z
  have hXP : eval P.1.rep (X i ^ m) ≠ 0 := by simpa using pow_ne_zero m hiP
  have hXI := notMem_of_eval_rep_ne_zero P.2 (isHomogeneous_X_pow i m) hXP
  refine ⟨⟨_, mem_localSubring_iff.2 ⟨m, f, _, hf, isHomogeneous_X_pow i m, hXP, rfl⟩⟩,
    ⟨_, mem_localSubring_iff.2 ⟨m, g, _, hg, isHomogeneous_X_pow i m, hXP, rfl⟩⟩, ?_⟩
  exact (functionField.mk_div_mk hf hg (isHomogeneous_X_pow i m) hgI hXI).symm

/-! ### The coordinate ring is not contained in the function field -/

/-- The embedding of the function field `k(V)` into the fraction field of `R ⧸ I`, sending
`f / g` to `[f] / [g]`: `HomogeneousLocalization.val`, into the localization of `R ⧸ I` at
`⊥.primeCompl`, followed by the map of localizations. -/
noncomputable def functionField.toFractionRing :
    functionField I →+* FractionRing (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal) :=
  (IsLocalization.map
    (S := Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal)))
    (M := (⊥ : Ideal (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal)).primeCompl)
    (T := nonZeroDivisors (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal)) _ (RingHom.id _)
    (fun _ hx ↦ Ideal.primeCompl_le_nonZeroDivisors _ hx)).comp
    (algebraMap (functionField I)
      (Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal))))

variable {I} in
/-- The embedding of `k(V)` into the fraction field sends `z` to the image of `z.val`. -/
theorem functionField.toFractionRing_apply (z : functionField I) :
    functionField.toFractionRing I z =
      IsLocalization.map
        (S := Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal)))
        (M := (⊥ : Ideal (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal)).primeCompl)
        (T := nonZeroDivisors (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal)) _ (RingHom.id _)
        (fun _ hx ↦ Ideal.primeCompl_le_nonZeroDivisors _ hx) z.val :=
  (rfl)

variable {I} in
/-- **`Γ_h(V) ⊄ k(V)`.** If the zero locus `V(I)` is nonempty, some element of the homogeneous
coordinate ring `Γ_h(V) = R ⧸ I` does not lie in the function field: its image in the fraction
field of `R ⧸ I` is not the image of any element of `k(V)`. The class of a variable `Xᵢ` that
does not vanish at a point of `V(I)` is such an element. -/
theorem exists_algebraMap_notMem_range_toFractionRing
    (hV : (zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty) :
    ∃ a : MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal,
      algebraMap _ (FractionRing (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal)) a ∉
        Set.range (functionField.toFractionRing I) := by
  obtain ⟨P, hP⟩ := hV
  obtain ⟨i, hi⟩ := Function.ne_iff.1 P.rep_ne_zero
  have hXI : X i ∉ I := notMem_of_eval_rep_ne_zero hP (isHomogeneous_X k i) (by simpa using hi)
  have hle : (⊥ : Ideal (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal)).primeCompl ≤
      (nonZeroDivisors _).comap (RingHom.id _) :=
    fun _ hx ↦ Ideal.primeCompl_le_nonZeroDivisors _ hx
  refine ⟨Ideal.Quotient.mk _ (X i), fun ⟨z, hz⟩ ↦ ?_⟩
  rw [functionField.toFractionRing_apply, ← RingHom.id_apply (Ideal.Quotient.mk I.toIdeal (X i)),
    ← IsLocalization.map_eq
      (S := Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal))) hle] at hz
  refine HomogeneousLocalization.algebraMap_notMem_range_val
    (Ideal.primeCompl_le_nonZeroDivisors _) one_ne_zero
    (I.mk_X_mem_quotientGrading i)
    (fun h ↦ hXI (Ideal.Quotient.eq_zero_iff_mem.1 h)) ⟨z, ?_⟩
  exact IsLocalization.map_injective_of_injective' _ _
    (Rₘ := Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal)))
    (FractionRing _) hle zero_notMem_nonZeroDivisors (fun _ _ h ↦ h) hz

/-! ### The pole set of a rational function -/

variable {I} in
/-- Two fractions `f / g` and `f' / g'` of forms are equal in `k(V)` iff `f g' - f' g ∈ I`. -/
theorem functionField.mk_eq_mk_iff {d' : ℕ} {f g f' g' : MvPolynomial (Fin (n + 1)) k}
    (hf : f.IsHomogeneous d) (hg : g.IsHomogeneous d) (hgI : g ∉ I)
    (hf' : f'.IsHomogeneous d') (hg' : g'.IsHomogeneous d') (hgI' : g' ∉ I) :
    functionField.mk hf hg hgI = functionField.mk hf' hg' hgI' ↔ f * g' - f' * g ∈ I := by
  rw [functionField.mk_def, functionField.mk_def, HomogeneousLocalization.ext_iff_val,
    HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  change (∃ c : (⊥ : Ideal (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal)).primeCompl,
      (c : MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal) *
        (Ideal.Quotient.mk I.toIdeal g' * Ideal.Quotient.mk I.toIdeal f) =
      c * (Ideal.Quotient.mk I.toIdeal g * Ideal.Quotient.mk I.toIdeal f')) ↔ _
  rw [← HomogeneousIdeal.mem_iff, ← Ideal.Quotient.eq, map_mul, map_mul,
    mul_comm _ (Ideal.Quotient.mk _ g'),
    mul_comm _ (Ideal.Quotient.mk _ g)]
  refine ⟨fun ⟨c, hc⟩ ↦ mul_left_cancel₀ c.2 hc, fun h ↦ ⟨1, by rw [h]⟩⟩

section Fractions

variable {I}

/-- For a homogeneous prime `I`, a power of a coordinate `Xᵢ ∉ I` is not in `I`. -/
theorem X_pow_notMem_of_X_notMem {i : Fin (n + 1)} (hi : X i ∉ I) (m : ℕ) : X i ^ m ∉ I :=
  fun h ↦ hi (HomogeneousIdeal.mem_iff.1
    (Ideal.IsPrime.mem_of_pow_mem inferInstance m (HomogeneousIdeal.mem_iff.2 h)))

/-- A form `f` of degree `m` evaluated at the fractions `Xⱼ / Xᵢ` of `k(V)` is `f / Xᵢᵐ`. -/
theorem functionField.aeval_mk_X {i : Fin (n + 1)} (hi : X i ∉ I) {m : ℕ}
    {f : MvPolynomial (Fin (n + 1)) k} (hf : f.IsHomogeneous m) :
    aeval (fun j ↦ functionField.mk (isHomogeneous_X k j) (isHomogeneous_X k i) hi) f =
      functionField.mk hf (isHomogeneous_X_pow i m) (X_pow_notMem_of_X_notMem hi m) := by
  set A := MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal
  set Loc := Localization.AtPrime (⊥ : Ideal A)
  set φ : MvPolynomial (Fin (n + 1)) k →+* Loc := (algebraMap A Loc).comp (Ideal.Quotient.mk _)
  have hXi : Ideal.Quotient.mk I.toIdeal (X i) ∈ (⊥ : Ideal A).primeCompl :=
    fun h ↦ hi (HomogeneousIdeal.mem_iff.1 (Ideal.Quotient.eq_zero_iff_mem.1 h))
  set u : Loc := Localization.mk 1 ⟨_, hXi⟩
  have hC : (algebraMap (functionField I) Loc).comp (algebraMap k (functionField I)) =
      φ.comp C := by
    ext a
    rfl
  have hX : (algebraMap (functionField I) Loc) ∘
      (fun j ↦ functionField.mk (isHomogeneous_X k j) (isHomogeneous_X k i) hi) =
      u • (φ ∘ X) := by
    funext j
    rw [Function.comp_apply, HomogeneousLocalization.algebraMap_apply, functionField.mk_def,
      HomogeneousLocalization.val_mk, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
    simp only [φ, u, RingHom.comp_apply]
    rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul, one_mul, mul_one]
  apply HomogeneousLocalization.val_injective
  have := hf.map (φ.comp C)
  change algebraMap (functionField I) Loc _ = _
  rw [aeval_def, eval₂_comp_left, hC, hX, ← eval_map, this.eval_smul, eval_map,
    ← eval₂_comp_left, eval₂_eta, functionField.mk_def, HomogeneousLocalization.val_mk]
  simp only [φ, u, RingHom.comp_apply]
  rw [← Localization.mk_one_eq_algebraMap, Localization.mk_pow, Localization.mk_mul, one_pow,
    one_mul, mul_one]
  rfl

/-- A fraction `f / g` is zero in `k(V)` iff `f ∈ I`. -/
theorem functionField.mk_eq_zero_iff {d : ℕ} {f g : MvPolynomial (Fin (n + 1)) k}
    (hf : f.IsHomogeneous d) (hg : g.IsHomogeneous d) (hgI : g ∉ I) :
    functionField.mk hf hg hgI = 0 ↔ f ∈ I := by
  have h0 : (0 : functionField I) = functionField.mk (isHomogeneous_zero _ _ d) hg hgI := by
    rw [HomogeneousLocalization.ext_iff_val, functionField.mk_def, HomogeneousLocalization.val_mk,
      HomogeneousLocalization.val_zero]
    exact (Localization.mk_zero _).symm
  rw [h0, functionField.mk_eq_mk_iff, zero_mul, sub_zero, ← HomogeneousIdeal.mem_iff,
    ← HomogeneousIdeal.mem_iff, Ideal.IsPrime.mul_mem_iff_mem_or_mem inferInstance,
    or_iff_left (by rwa [HomogeneousIdeal.mem_iff])]

/-- In `k(V)`, `(f / g) * (g / f) = 1` for forms `f`, `g` of the same degree not in `I`. -/
theorem functionField.mk_mul_mk_swap {d : ℕ} {f g : MvPolynomial (Fin (n + 1)) k}
    (hf : f.IsHomogeneous d) (hg : g.IsHomogeneous d) (hfI : f ∉ I) (hgI : g ∉ I) :
    functionField.mk hf hg hgI * functionField.mk hg hf hfI = 1 := by
  rw [functionField.mk_def, functionField.mk_def]
  exact HomogeneousLocalization.mk_mul_mk_swap (𝒜 := I.quotientGrading)
    ⟨_, I.mk_mem_quotientGrading hf⟩ ⟨_, I.mk_mem_quotientGrading hg⟩
    (fun h ↦ hfI (Ideal.Quotient.eq_zero_iff_mem.1 (Ideal.mem_bot.1 h)))
    (fun h ↦ hgI (Ideal.Quotient.eq_zero_iff_mem.1 (Ideal.mem_bot.1 h)))

/-- In `k(V)`, `f / f = 1` for a form `f ∉ I`. -/
@[simp]
theorem functionField.mk_self {d : ℕ} {f : MvPolynomial (Fin (n + 1)) k}
    (hf : f.IsHomogeneous d) (hfI : f ∉ I) : functionField.mk hf hf hfI = 1 := by
  have h := functionField.mk_div_mk hf hf hf hfI hfI
  rwa [div_self (functionField.mk_ne_zero hf hf hfI hfI), eq_comm] at h

/-- A constant `a ∈ k` is the fraction `a / 1` in `k(V)`. -/
theorem functionField.algebraMap_eq_mk (a : k) (h1 : (1 : MvPolynomial (Fin (n + 1)) k) ∉ I) :
    algebraMap k (functionField I) a =
      functionField.mk (isHomogeneous_C (Fin (n + 1)) a) (isHomogeneous_one _ _) h1 := by
  rw [HomogeneousLocalization.ext_iff_val, functionField.mk_def, HomogeneousLocalization.val_mk]
  simp
  rfl

/-- A fraction `f / g` of forms of degree `m` is the quotient of `f` and `g` evaluated at the
fractions `Xⱼ / Xᵢ`, for any `Xᵢ ∉ I`. -/
theorem functionField.mk_eq_aeval_div_aeval {i : Fin (n + 1)} (hi : X i ∉ I) {m : ℕ}
    {f g : MvPolynomial (Fin (n + 1)) k} (hf : f.IsHomogeneous m) (hg : g.IsHomogeneous m)
    (hgI : g ∉ I) :
    functionField.mk hf hg hgI =
      aeval (fun j ↦ functionField.mk (isHomogeneous_X k j) (isHomogeneous_X k i) hi) f /
        aeval (fun j ↦ functionField.mk (isHomogeneous_X k j) (isHomogeneous_X k i) hi) g := by
  rw [functionField.aeval_mk_X hi hf, functionField.aeval_mk_X hi hg, functionField.mk_div_mk]

end Fractions

variable {I} in
/-- The denominators of `z ∈ k(V)`: the forms `g ∉ I` such that `z = f / g` for some form `f` of
the same degree. -/
def denominators (z : functionField I) : Set (MvPolynomial (Fin (n + 1)) k) :=
  {g | ∃ (d : ℕ) (f : MvPolynomial (Fin (n + 1)) k) (hf : f.IsHomogeneous d)
    (hg : g.IsHomogeneous d) (hgI : g ∉ I), z = functionField.mk hf hg hgI}

variable {I} in
theorem denominators_def (z : functionField I) : denominators z =
    {g | ∃ (d : ℕ) (f : MvPolynomial (Fin (n + 1)) k) (hf : f.IsHomogeneous d)
      (hg : g.IsHomogeneous d) (hgI : g ∉ I), z = functionField.mk hf hg hgI} :=
  (rfl)

variable {I} {z : functionField I} {g : MvPolynomial (Fin (n + 1)) k}

theorem mem_denominators_iff : g ∈ denominators z ↔
    ∃ (d : ℕ) (f : MvPolynomial (Fin (n + 1)) k) (hf : f.IsHomogeneous d)
      (hg : g.IsHomogeneous d) (hgI : g ∉ I), z = functionField.mk hf hg hgI := by
  rw [denominators_def]
  rfl

/-- The denominator `g` of a fraction `f / g` is a denominator of it. -/
theorem mem_denominators_mk {f : MvPolynomial (Fin (n + 1)) k} (hf : f.IsHomogeneous d)
    (hg : g.IsHomogeneous d) (hgI : g ∉ I) : g ∈ denominators (functionField.mk hf hg hgI) :=
  mem_denominators_iff.2 ⟨d, f, hf, hg, hgI, rfl⟩

/-- A denominator is a form. -/
theorem exists_isHomogeneous_of_mem_denominators (hg : g ∈ denominators z) :
    ∃ d, g.IsHomogeneous d := by
  obtain ⟨d, -, -, hg, -⟩ := mem_denominators_iff.1 hg
  exact ⟨d, hg⟩

/-- A denominator does not lie in `I`. -/
theorem notMem_of_mem_denominators (hg : g ∈ denominators z) : g ∉ I := by
  obtain ⟨-, -, -, -, hgI, -⟩ := mem_denominators_iff.1 hg
  exact hgI

variable (z) in
/-- Every element of `k(V)` has a denominator. -/
theorem denominators_nonempty : (denominators z).Nonempty := by
  obtain ⟨d, f, g, hf, hg, hgI, rfl⟩ := functionField.exists_eq_mk z
  exact ⟨g, mem_denominators_mk hf hg hgI⟩

variable (z) in
/-- The ideal of denominators of `z ∈ k(V)`: the homogeneous ideal of `R` spanned by the forms
`g ∉ I` with `z = f / g` for a form `f` of the same degree. -/
def denominatorIdeal : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k) where
  __ := Ideal.span (denominators z)
  is_homogeneous' := Ideal.homogeneous_span _ _ fun _ hg ↦
    (exists_isHomogeneous_of_mem_denominators hg).imp fun d hd ↦
      (mem_homogeneousSubmodule d _).2 hd

variable (z) in
theorem denominatorIdeal_toIdeal :
    (denominatorIdeal z).toIdeal = Ideal.span (denominators z) :=
  (rfl)

theorem subset_denominatorIdeal : denominators z ⊆ denominatorIdeal z := by
  intro g hg
  rw [SetLike.mem_coe, ← HomogeneousIdeal.mem_iff, denominatorIdeal_toIdeal]
  exact Ideal.subset_span hg

variable (z) in
/-- The zero locus of the ideal of denominators is the common zero locus of the denominators. -/
theorem zeroLocus_denominatorIdeal :
    zeroLocus (denominatorIdeal z : Set (MvPolynomial (Fin (n + 1)) k)) =
      zeroLocus (denominators z) := by
  rw [← zeroLocus_span (denominators z), ← denominatorIdeal_toIdeal]
  rfl

/-- A point `P` is a common zero of the denominators of `z` iff each of them vanishes at the
representative `P.rep`. -/
theorem mem_zeroLocus_denominators_iff {P : ℙ k (Fin (n + 1) → k)} :
    P ∈ zeroLocus (denominators z) ↔ ∀ g ∈ denominators z, eval P.rep g = 0 :=
  mem_zeroLocus_iff_eval_rep fun _ ↦ exists_isHomogeneous_of_mem_denominators

variable {P} in
/-- An element of `k(V)` lies in `𝒪_P(V)` iff one of its denominators does not vanish at `P`. -/
theorem mem_localSubring_iff_exists_mem_denominators :
    z ∈ (localSubring I P).toSubring ↔ ∃ g ∈ denominators z, eval P.1.rep g ≠ 0 := by
  rw [mem_localSubring_iff]
  constructor
  · rintro ⟨d, f, g, hf, hg, hgP, rfl⟩
    exact ⟨g, mem_denominators_mk hf hg _, hgP⟩
  · rintro ⟨g, hgz, hgP⟩
    obtain ⟨d, f, hf, hg, hgI, rfl⟩ := mem_denominators_iff.1 hgz
    exact ⟨d, f, g, hf, hg, hgP, rfl⟩

variable (z) in
/-- The pole set of `z ∈ k(V)`: the points `P ∈ V(I)` with `z ∉ 𝒪_P(V)`. -/
def poleSet : Set (ℙ k (Fin (n + 1) → k)) :=
  {P | ∃ hP : P ∈ zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)),
    z ∉ (localSubring I ⟨P, hP⟩).toSubring}

variable (z) in
theorem poleSet_def : poleSet z =
    {P | ∃ hP : P ∈ zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)),
      z ∉ (localSubring I ⟨P, hP⟩).toSubring} :=
  (rfl)

theorem mem_poleSet_iff {P : ℙ k (Fin (n + 1) → k)} :
    P ∈ poleSet z ↔ ∃ hP : P ∈ zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)),
      z ∉ (localSubring I ⟨P, hP⟩).toSubring := by
  rw [poleSet_def]
  rfl

variable (z) in
/-- The pole set of `z ∈ k(V)` is the set of zeros of `I` at which every denominator of `z`
vanishes. -/
theorem poleSet_eq_inter : poleSet z = zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)) ∩
    zeroLocus (denominatorIdeal z : Set (MvPolynomial (Fin (n + 1)) k)) := by
  ext P
  rw [mem_poleSet_iff, Set.mem_inter_iff, zeroLocus_denominatorIdeal,
    mem_zeroLocus_denominators_iff]
  simp only [mem_localSubring_iff_exists_mem_denominators, not_exists, not_and, not_not,
    exists_prop]

variable (z) in
/-- The common zeros of the denominators of `z ∈ k(V)` lie in `V(I)`. -/
theorem zeroLocus_denominatorIdeal_subset :
    zeroLocus (denominatorIdeal z : Set (MvPolynomial (Fin (n + 1)) k)) ⊆
      zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)) := by
  -- If `z = f / g` with `g(P) = 0` and `h ∈ I` is a form of degree `e` with `h(P) ≠ 0`, then
  -- `z = f g^e / (g^(e+1) + (h Xᵢ)^d)` for `Xᵢ(P) ≠ 0`, a denominator that does not vanish at `P`.
  intro P hP
  rw [zeroLocus_denominatorIdeal, mem_zeroLocus_denominators_iff] at hP
  by_contra hPI
  obtain ⟨e, h, he, hI, hhP⟩ :=
    exists_isHomogeneous_eval_rep_ne_zero_of_notMem_zeroLocus I.isHomogeneous hPI
  obtain ⟨i, hi⟩ := Function.ne_iff.1 P.rep_ne_zero
  obtain ⟨d, f, g, hf, hg, hgI, rfl⟩ := functionField.exists_eq_mk z
  have hgP := hP g (mem_denominators_mk hf hg hgI)
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hg0 : g ≠ 0 := fun h0 ↦ hgI (h0 ▸ zero_mem _)
    have hC := totalDegree_eq_zero_iff_eq_C.1 (hg.totalDegree hg0)
    rw [hC, eval_C] at hgP
    exact hg0 (by rw [hC, hgP, C_0])
  set h₁ := h * X i
  have hh₁ : h₁ ∈ I := Ideal.mul_mem_right _ _ hI
  have hpowI : h₁ ^ d ∈ I := Ideal.pow_mem_of_mem _ hh₁ d hd
  have hnum : (f * g ^ e).IsHomogeneous (d * (e + 1)) := by
    convert hf.mul (hg.pow e) using 1; ring
  have hden : (g ^ (e + 1) + h₁ ^ d).IsHomogeneous (d * (e + 1)) := by
    refine (hg.pow (e + 1)).add ?_
    convert (he.mul (isHomogeneous_X k i)).pow d using 1; ring
  have hdenI : g ^ (e + 1) + h₁ ^ d ∉ I := fun h' ↦
    hgI (‹I.toIdeal.IsPrime›.mem_of_pow_mem (e + 1) ((Ideal.add_mem_iff_left _ hpowI).1 h'))
  have hz : functionField.mk hf hg hgI = functionField.mk hnum hden hdenI := by
    rw [functionField.mk_eq_mk_iff,
      show f * (g ^ (e + 1) + h₁ ^ d) - f * g ^ e * g = f * h₁ ^ d by ring]
    exact Ideal.mul_mem_left _ f hpowI
  have hP' := hP _ (hz ▸ mem_denominators_mk hnum hden hdenI)
  rw [map_add, map_pow, map_pow, hgP, map_mul, eval_X, zero_pow (Nat.succ_ne_zero e),
    zero_add] at hP'
  exact pow_ne_zero _ (mul_ne_zero hhP hi) hP'

variable (z) in
/-- **The pole set of a rational function is algebraic.** The pole set of `z ∈ k(V)` is the zero
locus of the ideal of denominators of `z`. -/
theorem poleSet_eq_zeroLocus_denominatorIdeal :
    poleSet z = zeroLocus (denominatorIdeal z : Set (MvPolynomial (Fin (n + 1)) k)) := by
  rw [poleSet_eq_inter, Set.inter_eq_right.2 (zeroLocus_denominatorIdeal_subset z)]

variable (z) in
/-- **The pole set of a rational function is algebraic.** The pole set of `z ∈ k(V)` is the zero
locus of a set of forms. -/
theorem exists_poleSet_eq_zeroLocus : ∃ S : Set (MvPolynomial (Fin (n + 1)) k),
    (∀ f ∈ S, ∃ d, f.IsHomogeneous d) ∧ poleSet z = zeroLocus S :=
  ⟨denominators z, fun _ ↦ exists_isHomogeneous_of_mem_denominators,
    by rw [poleSet_eq_zeroLocus_denominatorIdeal, zeroLocus_denominatorIdeal]⟩

end Variety

end PlaneCurves.ProjectiveSpace

end

end
