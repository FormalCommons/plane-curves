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
* `PlaneCurves.ProjectiveSpace.varietyLocalRing I P`: the local ring `𝒪_P(V)`, the homogeneous
  localization of `R ⧸ I` at `quotientPointIdeal I P`, with its value map
  `varietyLocalRing.evalAt I P : 𝒪_P(V) →ₐ[k] k` and its inclusion
  `varietyLocalRing.toFunctionField I P` into `k(V)`.
* `PlaneCurves.ProjectiveSpace.localSubring I P`: `𝒪_P(V)` as a local subring of `k(V)`, and
  `localSubringEquiv I P : varietyLocalRing I P ≃ₐ[k] localSubring I P`.
* `PlaneCurves.ProjectiveSpace.functionField.toFractionRing I`: the embedding of `k(V)` into
  the fraction field of `R ⧸ I`.

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
* `exists_algebraMap_notMem_range_toFractionRing`: `Γ_h(V) ⊄ k(V)` inside the fraction field of
  `Γ_h(V)`, when `V` is nonempty.

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

variable {I} in
/-- The class of a form in the homogeneous coordinate ring `R ⧸ I`, as an element of a graded
piece. -/
theorem mk_mem_quotientGrading {f : MvPolynomial (Fin (n + 1)) k}
    (hf : f.IsHomogeneous d) : Ideal.Quotient.mk I.toIdeal f ∈ I.quotientGrading d :=
  TauCeti.GradedAlgebra.mk_mem_quotientPiece _ _ ((mem_homogeneousSubmodule d f).2 hf)

variable {I} in
/-- Every element of a graded piece of `R ⧸ I` is the class of a form of that degree. -/
theorem exists_isHomogeneous_mk_eq {x : MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal}
    (hx : x ∈ I.quotientGrading d) :
    ∃ f : MvPolynomial (Fin (n + 1)) k, f.IsHomogeneous d ∧ Ideal.Quotient.mk I.toIdeal f = x := by
  obtain ⟨f, hf, rfl⟩ := (TauCeti.GradedAlgebra.mem_quotientPiece_iff _ _).1 hx
  exact ⟨f, (mem_homogeneousSubmodule d f).1 hf, rfl⟩

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
  HomogeneousLocalization.mk ⟨d, ⟨_, mk_mem_quotientGrading hf⟩, ⟨_, mk_mem_quotientGrading hg⟩,
    fun h ↦ hgP ((mk_mem_quotientPointIdeal_iff_of_isHomogeneous hg).1 h)⟩

theorem mk_def {f g : MvPolynomial (Fin (n + 1)) k} (hf : f.IsHomogeneous d)
    (hg : g.IsHomogeneous d) (hgP : eval P.1.rep g ≠ 0) :
    mk (I := I) hf hg hgP =
      HomogeneousLocalization.mk ⟨d, ⟨_, mk_mem_quotientGrading hf⟩,
        ⟨_, mk_mem_quotientGrading hg⟩,
        fun h ↦ hgP ((mk_mem_quotientPointIdeal_iff_of_isHomogeneous hg).1 h)⟩ :=
  (rfl)

/-- Every element of `𝒪_P(V)` is a fraction `f / g` of forms of the same degree with
`g(P) ≠ 0`. -/
theorem exists_eq_mk (z : varietyLocalRing I P) :
    ∃ (d : ℕ) (f g : MvPolynomial (Fin (n + 1)) k) (hf : f.IsHomogeneous d)
      (hg : g.IsHomogeneous d) (hgP : eval P.1.rep g ≠ 0), z = mk hf hg hgP := by
  obtain ⟨⟨d, ⟨_, hx⟩, ⟨_, hy⟩, hden⟩, rfl⟩ := HomogeneousLocalization.mk_surjective z
  obtain ⟨f, hf, rfl⟩ := exists_isHomogeneous_mk_eq hx
  obtain ⟨g, hg, rfl⟩ := exists_isHomogeneous_mk_eq hy
  exact ⟨d, f, g, hf, hg, fun h ↦ hden ((mk_mem_quotientPointIdeal_iff_of_isHomogeneous hg).2 h),
    rfl⟩

/-- A homogeneous element of `R ⧸ I` outside the ideal of `P` does not vanish at `P`. -/
theorem liftₐ_ne_zero ⦃i : ℕ⦄ ⦃x : MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal⦄
    (hx : x ∈ I.quotientGrading i) (hxP : x ∈ (quotientPointIdeal I P).toIdeal.primeCompl) :
    Ideal.Quotient.liftₐ I.toIdeal (aeval P.1.rep) (fun _ h ↦
      (mem_zeroLocus_iff_le_ker I.isHomogeneous).1 P.2 h) x ≠ 0 := by
  obtain ⟨g, hg, rfl⟩ := exists_isHomogeneous_mk_eq hx
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
  HomogeneousLocalization.mk ⟨d, ⟨_, mk_mem_quotientGrading hf⟩, ⟨_, mk_mem_quotientGrading hg⟩,
    fun h ↦ hgI (Ideal.Quotient.eq_zero_iff_mem.1 h)⟩

variable {I} in
theorem functionField.mk_def {f g : MvPolynomial (Fin (n + 1)) k} (hf : f.IsHomogeneous d)
    (hg : g.IsHomogeneous d) (hgI : g ∉ I) :
    functionField.mk hf hg hgI =
      HomogeneousLocalization.mk ⟨d, ⟨_, mk_mem_quotientGrading hf⟩,
        ⟨_, mk_mem_quotientGrading hg⟩, fun h ↦ hgI (Ideal.Quotient.eq_zero_iff_mem.1 h)⟩ :=
  (rfl)

variable {I} in
/-- Every element of `k(V)` is a fraction `f / g` of forms of the same degree with `g ∉ I`. -/
theorem functionField.exists_eq_mk (z : functionField I) :
    ∃ (d : ℕ) (f g : MvPolynomial (Fin (n + 1)) k) (hf : f.IsHomogeneous d)
      (hg : g.IsHomogeneous d) (hgI : g ∉ I), z = functionField.mk hf hg hgI := by
  obtain ⟨⟨d, ⟨_, hx⟩, ⟨_, hy⟩, hden⟩, rfl⟩ := HomogeneousLocalization.mk_surjective z
  obtain ⟨f, hf, rfl⟩ := exists_isHomogeneous_mk_eq hx
  obtain ⟨g, hg, rfl⟩ := exists_isHomogeneous_mk_eq hy
  exact ⟨d, f, g, hf, hg, fun h ↦ hden (Ideal.Quotient.eq_zero_iff_mem.2 h), rfl⟩

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
/-- The elements of `R ⧸ I` outside the ideal of `P` are nonzero. -/
theorem primeCompl_le_bot :
    (quotientPointIdeal I P).toIdeal.primeCompl ≤
      (⊥ : Ideal (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal)).primeCompl :=
  fun _ hx h0 ↦ hx ((Ideal.mem_bot.1 h0) ▸ zero_mem _)

variable (I P) in
/-- The inclusion of `𝒪_P(V)` into the function field `k(V)`, sending `f / g` to `f / g`. -/
noncomputable def toFunctionField : varietyLocalRing I P →ₐ[k] functionField I where
  __ := HomogeneousLocalization.mapId I.quotientGrading
    (primeCompl_le_bot I P)
  commutes' _ := rfl

variable (I P) in
theorem toRingHom_toFunctionField : (toFunctionField I P : varietyLocalRing I P →+* _) =
    HomogeneousLocalization.mapId I.quotientGrading
      (primeCompl_le_bot I P) :=
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
  HomogeneousLocalization.mapId_atPrime_bot_injective _ (primeCompl_le_bot I P)

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
    (mk_mem_quotientGrading (isHomogeneous_X k i))
    (fun h ↦ hXI (Ideal.Quotient.eq_zero_iff_mem.1 h)) ⟨z, ?_⟩
  exact IsLocalization.map_injective_of_injective' _ _
    (Rₘ := Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal)))
    (FractionRing _) hle zero_notMem_nonZeroDivisors (fun _ _ h ↦ h) hz

end Variety

end PlaneCurves.ProjectiveSpace

end

end
