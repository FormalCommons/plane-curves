# Design of the library

This file says how the library is organized: its folders and files, its core
definitions and their API, which parts build on which, and where each of the
atlas's 96 milestones is proved. `AGENTS.md` asks every pull request to follow
it; a pull request that finds it wrong or incomplete proposes a change to it,
in an issue of its own.

The plan is the atlas
[FormalCommons/plane-curves-atlas](https://github.com/FormalCommons/plane-curves-atlas),
whose front page `atlas/README.md` has a section "Building the library". This
design follows that advice; the places where it departs from it are listed in
[Departures from the atlas](#departures-from-the-atlas). All library
declarations named here were located in the pinned sources (Tau Ceti at
`cd41bff`, Mathlib at `048fffa`, as in `lake-manifest.json`); nothing was
compiled. Names of new declarations are proposals: the pull request that adds
one may improve its name, and then updates this file.

## Contents

1. [Principles](#principles)
2. [Folders and files](#folders-and-files)
3. [Core definitions](#core-definitions)
4. [Parts and their order](#parts-and-their-order)
5. [Milestones](#milestones)
6. [Departures from the atlas](#departures-from-the-atlas)

## Principles

**Two layers.** The *polynomial layer* (curves as polynomials, multiplicities,
local rings, intersection numbers, linear systems, Bézout, Noether, cubics,
blowing up, quadratic transformations, adjoints) is the heart of the work and
is built here. The *function-field layer* (places, divisors, `L(D)`, genus,
differentials, Riemann–Roch) is Tau Ceti's and is used, not rebuilt. The
library's own work in Chapters 7 and 8 is the bridge between them: the centre
of a place on a plane curve, the order of a form at a place, divisors of
forms, adjoints, the genus formula.

**Representations.**

- An affine plane curve is a nonzero `F : MvPolynomial (Fin 2) k`, a
  projective one a nonzero `F : MvPolynomial (Fin 3) k` with
  `F.IsHomogeneous d`. There is no curve type: every invariant is defined on
  polynomials and proved invariant under `c • F`, `c ≠ 0` (and under
  associates). `X 0, X 1, X 2` are Fulton's `X, Y, Z`. Nonzero constants are
  allowed as curves of degree 0 where this avoids case splits (Noether).
- Points of `𝔸ⁿ` are `Fin n → k`; points of `ℙⁿ` are
  `ℙ k (Fin (n+1) → k)` (Mathlib's `Projectivization`). A function of a
  point of `ℙⁿ` is defined at `P.rep` and comes with a lemma `_mk` for every
  representative, for homogeneous `F` only.
- Multiplicity is Tau Ceti's `MvPolynomial.orderAt` (`ℕ∞`, `⊤` only at 0).
  The affine multiplicity *is* `F.orderAt P`; there is no new definition.
- "No common component" is `IsRelPrime`, never `IsCoprime`.
- Local rings: `𝒪_P(𝔸ⁿ)` is `Localization.AtPrime (vanishingIdeal k {P})`;
  `𝒪_P(ℙⁿ)` is `HomogeneousLocalization.AtPrime` of the polynomial ring at
  the homogeneous prime of `P`, with no chart. For an irreducible projective
  plane curve, `k(C)` is `HomogeneousLocalization.AtPrime 𝒜 ⊥` for the
  grading `𝒜` of `k[X,Y,Z]/(F)` (Tau Ceti's
  `HomogeneousIdeal.quotientGrading`), and `𝒪_P(C)` is a `LocalSubring` of
  `k(C)`, the range of `HomogeneousLocalization.mapId`. The other
  descriptions (quotients of `𝒪_P(ℙ²)` and of `𝒪_P(𝔸²)` in a chart, the
  scheme function field of Tau Ceti's `projectivePlaneCurve`) are
  isomorphisms to these. For reducible or non-reduced `F` there is no
  `k(C)`: one works in `𝒪_P(𝔸²)/(F)` and `𝒪_P(ℙ²)/(F_*)`.
- Intersection numbers are `Module.length` (in `ℕ∞`) of
  `𝒪 ⧸ Ideal.span {F, G}`, over the local ring `𝒪`, so that the lemmas of
  Tau Ceti's `RingTheory/Intersection.lean` apply as they are. Never
  `Module.finrank`. The equality with `dim_k` is a lemma
  (`IsLocalRing.length_restrictScalars`).
- Linear systems are `Submodule`s of `MvPolynomial.homogeneousSubmodule`,
  counted with `Module.finrank` (vector-space dimension, one more than
  Fulton's projective dimension). Zero-cycles are `ℙ k (Fin 3 → k) →₀ ℤ`
  (or `→₀ ℕ`).
- Changes of coordinates are Tau Ceti's `MvPolynomial.linearSubst M`
  (`eval x (linearSubst M F) = eval (M *ᵥ x) F`) with `M` invertible, and
  translations are Tau Ceti's `MvPolynomial.taylor`. Points are moved by
  `Projectivization.map` of `Matrix.mulVecLin M`.
- No general theory of varieties and no Zariski topology. Irreducibility is
  stated algebraically (prime vanishing ideals, minimal primes); on a curve
  "open" means cofinite. Fulton's `∅` is not irreducible and the unit ideal
  is not prime, as in Mathlib.
- The nonsingular model of a curve is the set of places of its function
  field, `TauCeti.Place k K`. A dominating rational map of curves is a
  `K →ₐ[k] K'`; birational equivalence is `Nonempty (K ≃ₐ[k] K')`; all local
  rings of a curve are `LocalSubring`s of one field. Domination is Mathlib's
  order on `LocalSubring` (`A ≤ B` means that `B` dominates `A`).
- Orders at places take values in `WithTop ℤ`, with `⊤` at 0 (Fulton's `∞`):
  the order is `TauCeti.Place.addValuation`, because Tau Ceti's `Place.ord`
  has the junk value `0` at `0`.
- The genus of a curve is `TauCeti.genus k K`, divisors are
  `TauCeti.Divisor k K`, `L(D)` is `TauCeti.riemannRochSpace`, its dimension
  `TauCeti.Divisor.dim`. None of them gets a wrapper.
- The group law on a nonsingular cubic is proved as Fulton does, for any base
  point and any characteristic, on a type of points carrying the base point;
  it is identified with Mathlib's group of a Weierstrass curve by an
  `AddEquiv`, not by a second group law there.

**Conventions for statements.** Each statement has the generality it needs:
an arbitrary field (or ring) where the algebra allows, `[IsAlgClosed k]` only
where points are needed, and the characteristic hypothesis that the milestone
states. Results about Mathlib or Tau Ceti types (`MvPolynomial`,
`Projectivization`, `HomogeneousLocalization`, `TauCeti.Place`,
`WeierstrassCurve`, …) go in that type's namespace; the library's own
definitions are in `PlaneCurves`, in the sub-namespaces `PlaneCurves.AffineSpace`,
`PlaneCurves.ProjectiveSpace`, `PlaneCurves.Affine` (affine plane curves) and
`PlaneCurves.Projective` (projective plane curves), so that the affine and
projective versions of a notion can share a name (as Mathlib's
`WeierstrassCurve.Affine` and `WeierstrassCurve.Projective` do).

**Traps.** `MvPolynomial.gradedAlgebra` is not an instance: every file that
uses `HomogeneousLocalization` or `HomogeneousIdeal` on polynomial rings
writes `attribute [local instance] MvPolynomial.gradedAlgebra`, as Mathlib
and Tau Ceti do. `IsHomogeneous 0 d` holds for every `d`, and
`totalDegree 0 = 0`: treat `0` separately. In `ℕ∞`, `⊤ * 0 = 0`.
`Algebra.trdeg` is a cardinal. Tau Ceti's `Scheme.IsCurveOver` includes
properness. Tau Ceti's `Place.center` is for Dedekind affine models, not the
centre on a plane curve defined here. There is no `GCDMonoid` instance on
`MvPolynomial`, so statements avoid `gcd`.

## Folders and files

Folders are Mathlib's top-level areas, then topics. Every file is a few
hundred lines; a file that would pass 1000 lines is split into a folder.
`(n)` after a file names the part (see [Parts](#parts-and-their-order)) that
creates it.

```
PlaneCurves/
├── Algebra/
│   ├── MvPolynomial/
│   │   ├── Derivation.lean              chain rule Derivation.map_aeval_mvPolynomial (D12)
│   │   └── SetVarZero.lean              setting X i to zero, X i ∣ p - p(X i = 0) (Q11)
│   └── Polynomial/
│       └── Bivariate.lean               R[X][Y] ≃ R[X, Y]: constants (A6), coefficients, Y-degree (R6)
├── RingTheory/
│   ├── Polynomial/
│   │   └── GaussLemma.lean              relatively prime p, q ∈ R[X] give C r ∈ (p, q) (A6)
│   ├── MvPolynomial/
│   │   ├── VanishingIdeal.lean          ideal of a point, separating polynomials (A1)
│   │   ├── Taylor.lean                  the Taylor shift p ↦ p(X + a) as an AlgEquiv (A9)
│   │   ├── LinearForm.lean              linear forms ∑ C (a i) * X i (P8)
│   │   ├── Homogenize/
│   │   │   ├── Basic.lean               homogenization in any variable to a degree (A2)
│   │   │   ├── Factorization.lean       Fulton's f*, F_*, Proposition 5 of §2.6 (A3)
│   │   │   └── Ideal.lean               J*, primality, (F)* = (F*) (P13)
│   │   ├── BinaryForm/
│   │   │   ├── Basic.lean               binary forms split into linear forms (A4)
│   │   │   ├── Basis.lean               bases of products of linear forms (A5)
│   │   │   └── Ideal.lean               forms of degree ≥ m+n−1 in (A, B) (L8)
│   │   ├── PowIdealOfVars.lean          k[X]/I_P^m and its dimension (A5)
│   │   ├── LinearSubst.lean             invertible linear changes of variables as automorphisms
│   │   ├── LeadingForm.lean             leading form at a point, products, substitutions (L1)
│   │   ├── OrderAtDehomogenize.lean     order of a form on a line and in affine charts (Q1)
│   │   ├── HomogeneousIdeal.lean        homogeneous ideals: finite generation by forms (P2)
│   │   ├── HilbertFunction.lean         dim (k[X,Y,Z]/(F))_d (P3)
│   │   ├── QuotientSpanPair.lean        Steps 1–2 of Bézout's proof (Q11)
│   │   ├── PolarDerivative.lean         D_v F = Σ v_i ∂F/∂X_i (T1)
│   │   └── Hessian.lean                 the Hessian matrix in n variables, Euler, covariance (Q16)
│   ├── Ideal/
│   │   └── AssociatedGraded.lean        (Iⁿ : f) = Iⁿ⁻ᵐ, dim A/Iⁿ⁺¹ = dim A/Iⁿ + dim Iⁿ/Iⁿ⁺¹ (L5)
│   ├── Length.lean                      lengths under ring isomorphisms, over a residue field (L5)
│   ├── Regular/
│   │   └── IsRelPrime.lean              coprime pairs: relations, weakly regular sequences (Q11)
│   ├── GradedAlgebra/
│   │   └── HomogeneousLocalization.lean field of fractions of degree 0, mapId injective (P10)
│   ├── Localization/
│   │   ├── Quotient.lean                (A/I)_𝔭 ≅ A_𝔭/I A_𝔭 (A9)
│   │   └── RegularFunctions.lean        ⋂ of localizations, R[1/f] (R1)
│   ├── Artinian/
│   │   └── QuotientPiLocalization.lean  A/I ≅ ∏ A_𝔪/I A_𝔪 for A/I Artinian (A11)
│   ├── DiscreteValuationRing/
│   │   └── Colength.lean                order = colength, expansions (A12)
│   ├── KrullDimension/
│   │   └── TrdegOne.lean                domains of transcendence degree one (R3)
│   └── UniqueFactorizationDomain/
│       └── Radical.lean                 radicals of principal ideals, no normalization (A7)
├── LinearAlgebra/
│   ├── FiniteDimensional/
│   │   └── Lemmas.lean                  extending linear equivalences, hyperplanes (P8)
│   └── Projectivization/
│       ├── AffineChart.lean             hyperplane at infinity ≅ ℙⁿ⁻¹ (P1)
│       ├── LinearSubspace.lean          linear subvarieties, lines, general position (P8)
│       └── Duality.lean                 points and hyperplanes, frames of hyperplanes (P9)
├── FieldTheory/
│   ├── PrimitiveElement/
│   │   └── OneSeparable.lean            F(α, β) simple with only β separable (R8)
│   └── FunctionField/
│       ├── TwoGenerators.lean           K = k(x, y) (R5, R8)
│       ├── ResidueRing.lean             residue rings of subrings of K (R2)
│       ├── PlaneModel.lean              K ≅ k(F) for an irreducible plane F (R6)
│       ├── RationalMap.lean             domination, rational maps of curves (R7)
│       ├── Place/
│       │   └── AddValuation.lean        TauCeti.Place.addValuation : K → WithTop ℤ (V1)
│       ├── HolomorphyRing/
│       │   └── Length.lean              ℓ(𝒪_S/g) = Σ ord_Q g (V7)
│       ├── KaehlerDifferential.lean     divisor of a Kähler differential (D1)
│       ├── RiemannRoch.lean             corollaries of Riemann and Riemann–Roch (D2)
│       └── Rational.lean                genus-zero criteria (D3)
└── AlgebraicGeometry/
    ├── AffineSpace/
    │   ├── PlaneZeroLocus.lean          coprime F, G have finitely many zeros (A6)
    │   ├── Hypersurface.lean            I(V(F)), components, subsets of 𝔸² (A7)
    │   ├── FiniteZeroLocus.lean         #V(I) ≤ dim k[X]/I (A8)
    │   ├── LocalRing.lean               𝒪_P(𝔸ⁿ), evaluation, quotients (A9)
    │   ├── RationalFunction.lean        k(V), 𝒪_P(V) in k(V), poles (A10)
    │   ├── QuotientPiLocalRing.lean     k[X]/I ≅ ∏ 𝒪_P/I𝒪_P (A11)
    │   └── PlaneCurveDimension.lean     primes of k[X,Y] of dimension one (R4)
    ├── ProjectiveSpace/
    │   ├── ZeroLocus.lean               V(S), I(X), cones (P4)
    │   ├── Nullstellensatz.lean         projective Nullstellensatz (P5)
    │   ├── Irreducible.lean             varieties, components (P6)
    │   ├── Hypersurface.lean            I(V(F)), hypersurfaces, hyperplanes (P7)
    │   ├── LinearSubvariety.lean        zero loci of linear forms, coordinates (P8)
    │   ├── FunctionField.lean           k(V), 𝒪_P(ℙⁿ), 𝒪_P(V), values, poles (P11)
    │   ├── ChangeOfCoordinates.lean     V^T and the induced isomorphisms (P12)
    │   ├── ProjectiveClosure.lean       V*, V_*, Proposition 3 of §4.3 (P14)
    │   ├── Subvariety.lean              Problems 4.21–4.23 (P15)
    │   ├── ChartLocalRing.lean          charts preserve k(V) and 𝒪_P(V) (P16)
    │   └── PlaneCurveDimension.lean     homogeneous primes of dimension one (R4)
    └── PlaneCurve/
        ├── Affine/
        │   ├── Multiplicity.lean        simple and multiple points (L2)
        │   ├── Tangent.lean             tangent lines, ordinary multiple points (L2)
        │   ├── MultiplePoint.lean       finiteness of multiple points (L3)
        │   ├── LocalRing.lean           𝒪_P(𝔸²)/(F), DVR at simple points (L4)
        │   ├── HilbertSamuel.lean       dim 𝔪ⁿ/𝔪ⁿ⁺¹, embedding dimension (L5)
        │   ├── IntersectionNumber/
        │   │   ├── Basic.lean           I(P, F∩G), properties (1)–(4), (7) (L6)
        │   │   ├── Additivity.lean      property (6) (L7)
        │   │   ├── Multiplicity.lean    property (5), Lemma of §3.3, tangency (L8)
        │   │   ├── Uniqueness.lean      Fulton's seven properties characterize I (L9)
        │   │   ├── SimplePoint.lean     property (8) (L10)
        │   │   ├── Line.lean            intersection with a line (L10)
        │   │   └── Sum.lean             property (9) (L11)
        │   ├── OrdinaryMultiplePoint.lean local-ring criterion (L12)
        │   └── Blowup/
        │       ├── Basic.lean           strict transform, fibre (B1)
        │       ├── Chart.lean           Γ(W') finite over Γ(W), conductor (B2)
        │       └── IntersectionNumber.lean Noether's formula, local form (B4)
        ├── Projective/
        │   ├── Multiplicity.lean        m_P(F) on ℙ² (Q1)
        │   ├── Singular.lean            simple points, IsNonsingular (Q2)
        │   ├── Tangent.lean             tangent lines, Problems 5.5–5.6 (Q3)
        │   ├── LocalRing.lean           local equations F_*, localized ideals in 𝒪_P(ℙ²) (Q4)
        │   ├── CurveLocalRing.lean      k(C), 𝒪_P(C) of a plane curve, charts (Q5)
        │   ├── IntersectionNumber/
        │   │   ├── Basic.lean           I(P, F∩G) on ℙ² (Q6)
        │   │   └── Properties.lean      properties (5), (6), (8), tangency (Q7)
        │   ├── Finiteness.lean          V(F) ∩ V(G) finite, curves meet (Q8)
        │   ├── LinearSystem/
        │   │   ├── Basic.lean           V(d; r_i P_i), lower bound (Q9)
        │   │   └── Independence.lean    equality for d ≥ Σ r_i − 1 (Q10)
        │   ├── Bezout/
        │   │   ├── Basic.lean           Bézout's theorem (Q12)
        │   │   └── Corollaries.lean     its corollaries (Q13)
        │   ├── MultiplePoints.lean      polar bound, Σ m(m−1)/2 ≤ (n−1)(n−2)/2 (Q14)
        │   ├── GenericLine.lean         lines through a point (Q15)
        │   ├── Hessian/
        │   │   ├── Basic.lean           the Hessian, its covariance and identity (Q16)
        │   │   └── Flex.lean            flexes, nine flexes of a cubic (Q17)
        │   ├── Conic.lean               irreducible conics (Q18)
        │   ├── Center.lean              centre of a valuation ring on a plane curve (V2)
        │   ├── IntersectionCycle.lean   F • G as a zero-cycle (N1)
        │   ├── Noether/
        │   │   ├── Basic.lean           Max Noether's fundamental theorem (N1)
        │   │   └── Conditions.lean      local criteria, residual corollary (N2)
        │   ├── Pascal.lean              Pascal and Pappus (N4)
        │   └── TerriblePoint.lean       terrible points, lines in n points (T1)
        ├── Cubic/
        │   ├── Residual.lean            residual points, eight determine the ninth (N3)
        │   ├── NormalForm.lean          singular cubics, Weierstrass form (N5)
        │   ├── Chord.lean               the chord–tangent map φ (N6)
        │   ├── GroupLaw.lean            the group of a nonsingular cubic (N6)
        │   ├── Weierstrass.lean         bridge to Mathlib's WeierstrassCurve (N7)
        │   ├── Flex.lean                flexes and torsion (N8)
        │   ├── CutOut.lean              points cut out by a curve of degree m (N9)
        │   ├── DivisorClass.lean        the group as the divisor class group (D6)
        │   └── GenusOne.lean            curves of genus one (D11)
        ├── Place/
        │   ├── Basic.lean               places over a point, order of a form (V3)
        │   ├── SimplePoint.lean         the place at a simple point (V3)
        │   ├── RationalMap.lean         rational maps defined at simple points (V4)
        │   ├── IntersectionNumber.lean  I(P, C∩G) = Σ ord_Q G (V8)
        │   ├── OrdinaryMultiplePoint.lean places over an ordinary point (B3)
        │   └── Conductor.lean           Noether's conditions via orders (O1)
        ├── NonsingularModel/
        │   ├── Basic.lean               existence and uniqueness (V5)
        │   ├── Normalization.lean       finiteness of the normalization (V6)
        │   └── OrdinaryMultiplePoints.lean resolution by blowing up (B5)
        ├── QuadraticTransformation/
        │   ├── Basic.lean               F^Q, proper transform F' (T2)
        │   ├── Position.lean            good and excellent position (T3)
        │   ├── Singularities.lean       new singularities, g* (T3)
        │   ├── Resolution.lean          reduction to ordinary points (T4)
        │   └── NeighbouringSingularities.lean Noether's formula, global form (T5)
        ├── Divisor.lean                 div G of a form (D4)
        ├── Adjoint/
        │   ├── Basic.lean               E, adjoints V_m (D5)
        │   ├── Residue.lean             adjoint division lemma, residue theorem (D7)
        │   └── RiemannRochSpace.lean    V_m → L(E_m) (D8)
        ├── Genus/
        │   ├── Basic.lean               genus formula (D9)
        │   ├── VirtualGenus.lean        g ≤ g* (D10)
        │   └── Examples.lean            a curve of genus 2 (D10)
        ├── CanonicalDivisor/
        │   ├── Basic.lean               canonical classes from adjoints, effective canonical divisors (D12)
        │   ├── Position.lean            IsTransversePosition, existence of such coordinates (D12)
        │   └── Differential.lean        dx/f_y and its divisor, holomorphic differentials (D12)
        └── RiemannRoch.lean             plane form of Riemann–Roch (D13)
```

## Core definitions

Each entry gives the definition, its representation, its file, and the API it
comes with (besides `_def`, `@[simp]` normal forms and `@[ext]` that
`AGENTS.md` asks for). Existing definitions that the library uses are named
with their files.

### Polynomials (`RingTheory/MvPolynomial/`)

- **Ideal of a point** (no new definition; `MvPolynomial.vanishingIdeal k {P}`,
  Mathlib `RingTheory/Nullstellensatz.lean`). API, namespace `MvPolynomial`:
  `vanishingIdeal_singleton_eq_span` (`= span {X i - C (P i)}`), the
  `k`-algebra isomorphism `k[X] ⧸ I_P ≃ₐ[k] k`,
  `exists_eval_eq_indicator` (Problem 1.17), `zeroLocus_sup`,
  `zeroLocus_inf`, `vanishingIdeal_union`.
- **`MvPolynomial.homogenize (i : Fin (n+1)) (N : ℕ) : MvPolynomial (Fin n) R →ₗ[R] MvPolynomial (Fin (n+1)) R`**:
  `∑ j ≤ N, homogeneousComponent j (rename i.succAbove f) * X i ^ (N - j)`.
  Dehomogenization is Tau Ceti's `TauCeti.dehomogenize i`
  (`RingTheory/MvPolynomial/Dehomogenization.lean`). API:
  `isHomogeneous_homogenize` (for `totalDegree f ≤ N`),
  `dehomogenize_homogenize`, `homogenize_dehomogenize` (for forms of degree
  `N`), `homogenize_mul`, `homogenize_succ` (`= X i * homogenize i N f`),
  `homogenize_C`, `homogenize_X`, `homogenize_monomial`, a `rename` lemma to
  Tau Ceti's `MvPolynomial.blockHomogenize`, and the relation to Mathlib's
  `Polynomial.homogenize`. Fulton's `f*` is `homogenize i f.totalDegree f`,
  with no definition of its own; `Homogenize/Factorization.lean` proves
  Proposition 5 of §2.6 and its corollary for it.
- **`Ideal.homogenization`** is Tau Ceti's (`RingTheory/MvPolynomial/Homogenization.lean`);
  `Homogenize/Ideal.lean` adds `Ideal.homogenization_eq_span_homogenize`
  (Fulton's `J*`), `Ideal.IsPrime.homogenization`,
  `Ideal.homogenization_span_singleton`.
- **`MvPolynomial.leadingFormAt (p) (a) : MvPolynomial σ R`**:
  `homogeneousComponent (p.orderAt a).toNat (taylor a p)`, the leading
  (lowest) form at `a`. API: `isHomogeneous_leadingFormAt`,
  `leadingFormAt_eq_zero_iff`, `leadingFormAt_of_eval_ne_zero`,
  `leadingFormAt_eq_sum_pderiv` (order one), `leadingFormAt_mul`,
  `leadingFormAt_pow`, `leadingFormAt_prod` (domains), `leadingFormAt_smul`,
  `leadingFormAt_taylor`, `leadingFormAt_linearSubst`, `orderAt_linearSubst`
  (invertible `M`), `orderAt_aeval_eq_of_isUnit_det` and
  `leadingFormAt_aeval_of_isUnit_det` (Problem 3.8(b); 3.8(a) is Tau Ceti's
  `MvPolynomial.orderAt_le_orderAt_aeval`).
- **`MvPolynomial.polarDerivative (v) (F)`**: `∑ i, v i • pderiv i F`. API:
  homogeneity, linearity in `v`, behaviour under `linearSubst`.

### Commutative algebra (`RingTheory/`)

- **Homogeneous localization of a graded domain**
  (`GradedAlgebra/HomogeneousLocalization.lean`, namespace
  `HomogeneousLocalization`): a `Field` instance on `AtPrime 𝒜 ⊥` for a
  graded domain, `mapId_injective`, `mem_range_mapId_iff`.
- **Regular functions on a set of maximal ideals**
  (`Localization/RegularFunctions.lean`): `PlaneCurves.regularFunctionsOn R U`,
  the infimum over `m ∈ U` of `Localization.subalgebra.ofField K m.primeCompl`
  in the fraction field `K` (Fulton's `Γ(U)`). API:
  `mem_regularFunctionsOn_iff`, `regularFunctionsOn_univ`
  (`MaximalSpectrum.iInf_localization_eq_bot`), antitonicity,
  `regularFunctionsOn_basicOpen` (`= R[1/f]`), finiteness of poles for a
  one-dimensional Noetherian domain.
- **Order = colength** (`DiscreteValuationRing/Colength.lean`) and
  **Artinian decomposition** (`Artinian/QuotientPiLocalization.lean`) are
  statements about Mathlib's types and need no definitions.

### Affine space (`AlgebraicGeometry/AffineSpace/`)

- **`PlaneCurves.AffineSpace.localRing k P`**: an `abbrev` for
  `Localization.AtPrime (MvPolynomial.vanishingIdeal k {P})`, `𝒪_P(𝔸ⁿ)`.
  API: `evalAt : localRing k P →ₐ[k] k` with `evalAt_algebraMap`,
  `ker_evalAt` (the maximal ideal), the residue field is `k`, the
  `IsRegularLocalRing` instance and `ringKrullDim = n`,
  `algebraMap_mem_maximalIdeal_pow_iff` (`↔ n ≤ F.orderAt P`),
  `isUnit_algebraMap_iff`, the isomorphisms induced by `taylor` and by
  `linearSubst` with invertible `M`, and the quotient isomorphisms
  `𝒪_P/J𝒪_P ≅ 𝒪_P(k[X]/I)/J'` of §2.8 (from `Localization/Quotient.lean`).
- **Affine varieties** are not a type: a variety is given by a prime ideal
  `I` (`Γ(V) = k[X] ⧸ I`, `k(V) = FractionRing Γ(V)`), its local rings by
  `LocalSubring.ofPrime` in `k(V)` (`RationalFunction.lean`):
  `AffineSpace.functionField I` and `AffineSpace.localSubring P hI` for
  `hI : I ≤ vanishingIdeal k {P}`, with the value map `evalAt`, the
  isomorphism `quotientAlgEquiv` to `𝒪_P(𝔸ⁿ) ⧸ I 𝒪_P(𝔸ⁿ)`, and `map`.

### Projective space (`AlgebraicGeometry/ProjectiveSpace/`, `LinearAlgebra/Projectivization/`)

- **Charts** are Tau Ceti's `Projectivization.affineOpen` and
  `Projectivization.affineChart` (`LinearAlgebra/Projectivization/AffineChart.lean`);
  the library adds `Projectivization.insertZero i : ℙ K (Fin n → K) → ℙ K (Fin (n+1) → K)`
  with `range_insertZero` (`= (affineOpen i)ᶜ`).
- **Linear subvarieties** have no definition: they are Mathlib's
  `Submodule.projectivization p`, of dimension `m` when
  `finrank K p = m + 1`; lines have `finrank 2`, hyperplanes are
  `(LinearMap.ker f).projectivization` for `f ≠ 0`, and linear forms are
  `∑ i, C (a i) * X i` (see [`design/P8.md`](design/P8.md)).
- **`PlaneCurves.ProjectiveSpace.zeroLocus (S) : Set (ℙ k (Fin (n+1) → k))`**:
  the points at whose representatives every element of `S` vanishes, in the
  every-vector convention. API: `mk_mem_zeroLocus_iff` (one representative
  suffices for forms), the cone lemma `mk_mem_zeroLocus_iff_mem_zeroLocus`
  (to Mathlib's affine `MvPolynomial.zeroLocus`), `zeroLocus_span`,
  `zeroLocus_homogeneousComponent` (infinite `k`, Problem 4.2),
  antitonicity, unions and intersections, `zeroLocus_linearSubst`,
  `mem_zeroLocus_iff_affineChart`.
- **`PlaneCurves.ProjectiveSpace.vanishingIdeal (X) : HomogeneousIdeal (homogeneousSubmodule (Fin (n+1)) k)`**.
  API: `mem_vanishingIdeal_iff`, radical, the Galois connection with
  `zeroLocus`, `vanishingIdeal_singleton` (`= span {aᵢXⱼ − aⱼXᵢ}`, prime),
  `vanishingIdeal_cone`.
  It is the largest homogeneous ideal vanishing on `X` (spanned by the forms
  vanishing on `X`); over an infinite field it contains every polynomial
  vanishing on `X`.
- **`PlaneCurves.ProjectiveSpace.cone (X) : Set (Fin (n+1) → k)`**: the affine
  cone, the lines of the points of `X` with the origin. API: `cone_zeroLocus`
  (`C(V(I)) = ` the affine zero locus of homogeneous `I`, for `V(I) ≠ ∅`).
- **`PlaneCurves.ProjectiveSpace.pointIdeal P`**: the homogeneous prime
  `vanishingIdeal {P}` with its `IsPrime` instance, and its image in a graded
  quotient `R ⧸ I` for `P ∈ zeroLocus I`.
- **`PlaneCurves.ProjectiveSpace.localRing P`**: `𝒪_P(ℙⁿ)`,
  `HomogeneousLocalization.AtPrime (homogeneousSubmodule (Fin (n+1)) k) (pointIdeal P)`.
  API: local ring, residue field `k`, value map, the chart isomorphism
  `chartEquiv i : localRing P ≃ₐ[k] AffineSpace.localRing k (affineChart i P)`
  explicit on fractions (`G/Xᵢᵐ ↦ dehomogenize i G`).
- **Function field and local rings of a homogeneous prime** `I`
  (`FunctionField.lean`): `ProjectiveSpace.functionField I`
  (`HomogeneousLocalization.AtPrime I.quotientGrading ⊥`, a field by the
  graded-domain instance), `ProjectiveSpace.varietyLocalRing I P`
  (`AtPrime` at the image of `pointIdeal P`, for `P ∈ zeroLocus I`),
  `ProjectiveSpace.localSubring I P : LocalSubring (functionField I)` (its
  range under `mapId`), and the value map. API: `mem_localSubring_iff`
  (`z = f/g` with `g(P) ≠ 0`), evaluation, `ker` of evaluation, the pole set
  is a zero locus (Problem 4.17), isomorphisms under `linearSubst`
  (`ChangeOfCoordinates.lean`) and in charts (`ChartLocalRing.lean`,
  explicit on fractions). A projective variety `V` uses
  `I = vanishingIdeal V`; a plane curve uses `I = (F)`.

### Affine plane curves (`AlgebraicGeometry/PlaneCurve/Affine/`), namespace `PlaneCurves.Affine`

- **Multiplicity**: `F.orderAt P` (Tau Ceti). Predicates
  `IsSimplePoint F P` (`eval P F = 0 ∧ ∃ i, eval P (pderiv i F) ≠ 0`) and
  `IsMultiplePoint F P` (`2 ≤ F.orderAt P`). API:
  `isSimplePoint_iff_orderAt_eq_one`, `isMultiplePoint_iff_eval_pderiv`,
  `isSimplePoint_mul_iff`, invariance under associates, `taylor` and
  `linearSubst`.
- **Tangents**: `IsTangentAt F P L` (`L` a nonzero linear form dividing
  `leadingFormAt F P`), `tangentMultiplicity F P L : ℕ`
  (`multiplicity L (leadingFormAt F P)`), `IsOrdinaryMultiplePoint F P`
  (`IsMultiplePoint` and `Squarefree (leadingFormAt F P)`). API:
  `tangentMultiplicity_mul`, `sum_tangentMultiplicity` (`= m_P(F)`, `k`
  algebraically closed), the tangent at a simple point,
  `isOrdinaryMultiplePoint_iff` (`m` distinct tangents).
- **`IntersectProperlyAt F G P`**: every irreducible common factor of `F`
  and `G` is nonzero at `P` (no common component through `P`). API:
  symmetry, `IsRelPrime.intersectProperlyAt`, products, `G + A * F`, and
  `radical (span {F, G}) = 𝔪` in `𝒪_P` when both vanish at `P`.
- **`intersectionNumber P F G : ℕ∞`**:
  `Module.length 𝒪 (𝒪 ⧸ Ideal.span {algebraMap _ 𝒪 F, algebraMap _ 𝒪 G})`
  with `𝒪 = AffineSpace.localRing k P`. API: `intersectionNumber_eq_length_restrictScalars`
  (`dim_k`), `_comm`, `_eq_zero_iff`, `_ne_top_iff` (`IntersectProperlyAt`),
  `_add_mul`, `_mul_left`, `_mul_right`, invariance under `taylor` and
  `linearSubst`, `mul_orderAt_le_intersectionNumber` with its equality case,
  `_eq_ord` at a simple point, `intersectionNumber_X_X = 1`.
- **Local ring of a curve**: `AffineSpace.localRing k P ⧸ Ideal.span {F}`,
  with Mathlib's `Ring.ord` as the order; no new definition.
- **Fulton's axioms**: a structure `IntersectionNumberAxioms` on functions
  `(Fin 2 → k) → MvPolynomial (Fin 2) k → MvPolynomial (Fin 2) k → ℕ∞`,
  with the uniqueness theorem.
- **Blow-up**: `blowupStrictTransform F` (`X^{-r} F(X, XZ)` with
  `r = F.orderAt 0`), with its product rule, irreducibility, value on
  `X = 0`, and `k(C) ≅ k(C')`.

### Projective plane curves (`AlgebraicGeometry/PlaneCurve/Projective/`), namespace `PlaneCurves.Projective`

- **`mult F P : ℕ∞`**: `F.orderAt P.rep`. API: `mult_mk` (homogeneous `F`),
  `mult_eq_orderAt_dehomogenize` (any chart containing `P`), `mult_smul`,
  `mult_linearSubst`, `mult_eq_zero_iff`, `mult_mul`, `mult_le_degree`.
- **`IsSimplePoint F P`, `IsMultiplePoint F P`, `IsNonsingular F`**
  (`IsNonsingular`: every nonzero `v` with `F(v) = 0` has a partial
  derivative nonzero at `v`, which is Tau Ceti's hypothesis). API:
  `isMultiplePoint_iff_eval_pderiv` (Problem 5.1),
  `isNonsingular_iff_forall_isSimplePoint`, `IsNonsingular.irreducible`.
- **`tangentLine F v`** (`∑ i, C (eval v (pderiv i F)) * X i`), tangent forms
  and ordinary multiple points, as in the affine case, through the chart.
- **`localEquation P F : ProjectiveSpace.localRing P`** (`F/L^d` for a
  linear `L` with `L(P) ≠ 0`, independent of `L` up to a unit) and
  **`localIdeal P I : Ideal (ProjectiveSpace.localRing P)`** (the fractions
  `a/s` with `a ∈ I` and `s ∉ pointIdeal P` homogeneous of the same degree).
  API: `localIdeal_span_pair` (`= span {F_*, G_*}`), `localEquation_mul`,
  `chartEquiv` sends `localEquation P F` to `dehomogenize i F` up to a unit.
- **`functionField F`, `localSubring F P`** for irreducible `F`
  (`[Fact (Irreducible F)]`, as in Tau Ceti): `ProjectiveSpace.functionField`
  and `ProjectiveSpace.localSubring` of the ideal `(F)` (Tau Ceti's
  `projectivePlaneCurve.ideal`). API: `localRing P ⧸ span {F_*} ≃ₐ[k] localSubring F P`,
  the chart isomorphisms `functionField F ≃ₐ[k] FractionRing (k[X,Y] ⧸ (dehomogenize i F))`
  and `localSubring F P ≃ₐ[k] AffineSpace.localRing ⧸ (F_(i))`, the
  isomorphism with Tau Ceti's `projectivePlaneCurve.functionFieldEquiv`, and
  `TauCeti.IsFunctionField k (functionField F)`.
- **`intersectionNumber P F G : ℕ∞`**:
  `Module.length (localRing P) (localRing P ⧸ localIdeal P (span {F, G}))`.
  API: `intersectionNumber_eq_affine` (any chart), and the properties
  (1)–(8) transported from the affine case.
- **`intersectionCycle F G : ℙ k (Fin 3 → k) →₀ ℕ`** (zero when the
  support is infinite). API: `intersectionCycle_apply`, `_comm`, `_mul`,
  `_add_mul`, `degree_intersectionCycle` (`= deg F * deg G`).
- **`linearSystem d r : Submodule k (MvPolynomial (Fin 3) k)`** for
  `r : ℙ k (Fin 3 → k) →₀ ℕ`: forms of degree `d` with `r P ≤ mult F P`. API:
  `mem_linearSystem`, `finrank_linearSystem_ge`, `finrank_linearSystem_eq`,
  behaviour under `linearSubst`.
- **The Hessian** has no new definition: it is
  `(TauCeti.hessian MvPolynomial.pderiv F).det`, the determinant of Tau
  Ceti's Hessian matrix (`TauCeti/RingTheory/LocalRing/Hessian.lean`, with
  `hessian_apply`). New: `IsFlex F P`, `IsOrdinaryFlex F P`. API, stated for
  that determinant: homogeneity, covariance (`(det M)^2`), the identity
  relating `h` to `f`, `g` in a chart.
- **`IsCenter F R P`, `center F Q`**: for a valuation subring `R` of a field
  `L` with `ψ : functionField F →ₐ[k] L`, `R` dominates `ψ (localSubring F P)`;
  `center F Q` is the unique such point for a place `Q`. API:
  `existsUnique_isCenter`, `center_eq_iff`, `center_surjective`,
  finiteness of fibres.

### Places over a plane curve (`AlgebraicGeometry/PlaneCurve/Place/`)

- **`TauCeti.Place.addValuation (Q) : AddValuation K (WithTop ℤ)`**
  (`FieldTheory/FunctionField/Place/AddValuation.lean`): `⊤` at 0,
  `Q.ord z` otherwise. API: `addValuation_of_ne_zero`, `addValuation_eq_top_iff`,
  `addValuation_nonneg_iff` (`↔ z ∈ Q.integers`), `addValuation_pos_iff`,
  `addValuation_algebraMap` (0 on `kˣ`), the relation to
  `IsDiscreteValuationRing.addVal` and to `Ring.ord` (with the cast from `ℕ∞`).
- **`PlaneCurves.Projective.placesOver F P : Set (Place k (functionField F))`**
  and **`ordForm Q G : WithTop ℤ`** (`addValuation Q (G / L^{deg G})` for a
  linear `L` not vanishing at `center F Q`). API: independence of `L`,
  `ordForm_mul`, `ordForm_eq_top_iff` (`F ∣ G`), `ordForm_pos_iff`, the
  relation to the chart, `placesOver_finite`, `placesOver_nonempty`, the
  unique place over a simple point.

### Quadratic transformations (`PlaneCurve/QuadraticTransformation/`)

- **`quadraticTransform F`** (`F(YZ, XZ, XY)`, by `MvPolynomial.bind₁`) and
  **`properTransform F`** (`F'`, with `F^Q = X^{r''} Y^{r'} Z^r F'`); the
  predicates `IsGoodPosition`, `IsExcellentPosition`; `virtualGenus F : ℤ`
  (`g*`, `(n−1)(n−2)/2 − Σ m(m−1)/2`); and
  `IsTerriblePoint F v` (`2 ≤ deg F ∧ polarDerivative v F = 0`).

### Divisors and adjoints (`PlaneCurve/Divisor.lean`, `Adjoint/`)

- **`formQuotient F G H : (functionField F)ˣ`** for forms of equal degree with
  `F ∤ G`, `F ∤ H`, and **`formDivisor F G : TauCeti.Divisor k (functionField F)`**
  (coefficient `ordForm Q G` at `Q`). API: `coeff_formDivisor`, effectivity,
  `coeff_formDivisor_pos_iff`, `formDivisor_mul`, `principal_formQuotient`
  (`= div G − div H`), `sum_coeff_formDivisor_center` (`= I(P, C∩G)`),
  `degree_formDivisor` (`= deg F * deg G`), the comparison with Tau Ceti's
  `poles x ⊔ poles y` for a nonsingular curve.
- **`adjointDivisor F`** (`E`, coefficient `mult F (center Q) − 1`, or 0),
  **`IsAdjoint F G`**, and **`adjointSubmodule F m : Submodule k (MvPolynomial (Fin 3) k)`**
  (`V_m`). API: effectivity, support, `degree_adjointDivisor`, multiples of
  `F` are adjoint, `isAdjoint_iff_le_formDivisor`, the linear map
  `V_m → TauCeti.riemannRochSpace (m • div L − E)` (`G ↦ G/L^m`), its kernel
  and surjectivity.

### Differentials (`FieldTheory/FunctionField/KaehlerDifferential.lean`)

- **`PlaneCurves.kaehlerDifferentialDivisor hK hex (ω : Ω[K⁄k]) (hω : ω ≠ 0) : TauCeti.Divisor k K`**
  for a perfect `k` (`hK : IsFunctionField k K`, `hex : IsIntegrallyClosedIn k K`): the Weil
  divisor of the image of `ω` under Tau Ceti's
  `kaehlerDifferentialEquivWeilDifferentialOfSeparating`, at a separating
  element chosen from
  `TauCeti.IsFunctionField.exists_transcendental_and_isSeparable_adjoin_of_perfectField`.
  API: independence of the separating element (`kaehlerDifferentialDivisor_eq`), the order at
  `Q` is `ord_Q (ω / dt)` for a uniformizer `t` (`coeff_kaehlerDifferentialDivisor`),
  `div (f • ω) = div f + div ω` (`kaehlerDifferentialDivisor_smul`), the class is Tau Ceti's
  `canonicalClass` (`divisorClass_kaehlerDifferentialDivisor`, and
  `divisorClass_eq_canonicalClass_iff_exists_kaehlerDifferentialDivisor_eq` for
  **8-differential**), and Riemann–Roch for it
  (`isRiemannRochDivisor_kaehlerDifferentialDivisor`).

## Parts and their order

Each part below is meant to become one issue and one pull request of a few
hundred lines (a part marked *large* may be split again). The parts follow
the atlas's five stages. A part needs the parts in its "Needs" column, and
nothing later; parts of a stage whose "Needs" are met can be done in
parallel. Milestones are cited by the short names of the
[milestone table](#milestones).

### Stage 1: core

Affine varieties (Chapters 1–2):

| Part | Files | Content and milestones | Needs |
|---|---|---|---|
| A1 | `RingTheory/MvPolynomial/VanishingIdeal.lean` | ideal of a point, separating polynomials | — |
| A2 | `RingTheory/MvPolynomial/Homogenize/Basic.lean` | `MvPolynomial.homogenize` and its API | — |
| A3 | `RingTheory/MvPolynomial/Homogenize/Factorization.lean` | **aff-hom** | A2 |
| A4 | `RingTheory/MvPolynomial/BinaryForm/Basic.lean` | **aff-binary** | — |
| A5 | `RingTheory/MvPolynomial/BinaryForm/Basis.lean`, `PowIdealOfVars.lean` | **aff-dim** | A1, A4 |
| A6 | `Algebra/Polynomial/Bivariate.lean`, `RingTheory/Polynomial/GaussLemma.lean`, `AffineSpace/PlaneZeroLocus.lean` | **aff-coprime** | — |
| A7 | `RingTheory/UniqueFactorizationDomain/Radical.lean`, `AffineSpace/Hypersurface.lean` | **aff-hypersurface** | A1, A6 |
| A8 | `AffineSpace/FiniteZeroLocus.lean` | **aff-finite** | A1 |
| A9 | `RingTheory/Localization/Quotient.lean`, `AffineSpace/LocalRing.lean` | `AffineSpace.localRing`; **aff-quotient**; parts (a)–(c), (e) of **aff-local** | A1 |
| A10 | `AffineSpace/RationalFunction.lean` | **aff-local** (complete) | A9 |
| A11 | `RingTheory/Artinian/QuotientPiLocalization.lean`, `AffineSpace/QuotientPiLocalRing.lean` | **aff-global** | A8, A9 |
| A12 | `RingTheory/DiscreteValuationRing/Colength.lean` | **aff-dvr** | — |

Local properties of plane curves (Chapter 3):

| Part | Files | Content and milestones | Needs |
|---|---|---|---|
| L1 | `RingTheory/MvPolynomial/LeadingForm.lean` | `leadingFormAt`, its API, Problem 3.8 | — |
| L2 | `PlaneCurve/Affine/Multiplicity.lean`, `Tangent.lean` | **3-mult**, **3-product** | L1, A4 |
| L3 | `PlaneCurve/Affine/MultiplePoint.lean` | **3-finite** | L2, A6 |
| L4 | `PlaneCurve/Affine/LocalRing.lean` | **3-dvr** | L2, A9 |
| L5 | `RingTheory/Ideal/AssociatedGraded.lean`, `RingTheory/Length.lean`, `PlaneCurve/Affine/HilbertSamuel.lean` | **3-ring**, **3-embdim** | L2, A5, A9 |
| L6 | `Affine/IntersectionNumber/Basic.lean` | `IntersectProperlyAt`, `intersectionNumber`; **3-finvan** | A6, A9 |
| L7 | `Affine/IntersectionNumber/Additivity.lean` | **3-add** | L6 |
| L8 | `RingTheory/MvPolynomial/BinaryForm/Ideal.lean`, `Affine/IntersectionNumber/Multiplicity.lean` | **3-power**, **3-prodmult**, **3-tangency** | L2, L6, L7, A5 |
| L9 | `Affine/IntersectionNumber/Uniqueness.lean` | **3-axioms** | L7, L8 |
| L10 | `Affine/IntersectionNumber/SimplePoint.lean`, `Line.lean` | **3-order**, **3-line** | L4, L7 |
| L11 | `Affine/IntersectionNumber/Sum.lean` | **3-sum** | L6, A11 |
| L12 | `PlaneCurve/Affine/OrdinaryMultiplePoint.lean` | **3-ordinary** | L5, L8 |

Projective varieties (Chapter 4), beside Chapter 3:

| Part | Files | Content and milestones | Needs |
|---|---|---|---|
| P1 | `LinearAlgebra/Projectivization/AffineChart.lean` | **proj-charts** (part (c); the rest exists) | — |
| P2 | `RingTheory/MvPolynomial/HomogeneousIdeal.lean` | parts (a), (e) of **proj-ideals** | — |
| P3 | `RingTheory/MvPolynomial/HilbertFunction.lean` | **proj-ideals** (complete, part (f) in `ℤ`) | P2 |
| P4 | `ProjectiveSpace/ZeroLocus.lean` | `zeroLocus`, `vanishingIdeal`; parts (a)–(c) of **proj-sets** | P2 |
| P5 | `ProjectiveSpace/Nullstellensatz.lean` | parts (1)–(3) of **proj-null** | P4 |
| P6 | `ProjectiveSpace/Irreducible.lean` | **proj-sets** (complete) | P4 |
| P7 | `ProjectiveSpace/Hypersurface.lean` | **proj-null** (complete) | P5, P6, A3 |
| P8 | `LinearAlgebra/Projectivization/LinearSubspace.lean`, `LinearAlgebra/FiniteDimensional/Lemmas.lean`, `RingTheory/MvPolynomial/LinearForm.lean`, `ProjectiveSpace/LinearSubvariety.lean` | parts (a)–(e), (h), (i) of **proj-linear** ([`design/P8.md`](design/P8.md)) | P4 |
| P9 | `LinearAlgebra/Projectivization/Duality.lean` | **proj-linear** (complete) | P8 |
| P10 | `RingTheory/GradedAlgebra/HomogeneousLocalization.lean` | field instance, `mapId_injective` | — |
| P11 | `ProjectiveSpace/FunctionField.lean` | `pointIdeal`, `localRing`, `functionField`, `localSubring`; parts (a)–(c) of **proj-coord** | P5, P6, P10 |
| P12 | `ProjectiveSpace/ChangeOfCoordinates.lean` | **proj-coord** (complete) | P11 |
| P13 | `RingTheory/MvPolynomial/Homogenize/Ideal.lean` | part (a) of **proj-closure** | A3 |
| P14 | `ProjectiveSpace/ProjectiveClosure.lean` | parts (b)–(d), (f) of **proj-closure** (*large*) | P1, P7, P13 |
| P15 | `ProjectiveSpace/Subvariety.lean` | **proj-closure** (complete) | P14, A7 |
| P16 | `ProjectiveSpace/ChartLocalRing.lean` | **proj-charts-local**; `ProjectiveSpace.localRing.chartEquiv` | P11, P14, A10 |

Varieties and rational maps (Chapter 6), beside Chapter 3:

| Part | Files | Content and milestones | Needs |
|---|---|---|---|
| R1 | `RingTheory/Localization/RegularFunctions.lean` | **var-principal** | A10 |
| R2 | `FieldTheory/FunctionField/ResidueRing.lean` | **var-residue** | — |
| R3 | `RingTheory/KrullDimension/TrdegOne.lean` | parts (3)–(4) of **var-dim**; pole finiteness | R2 |
| R4 | `AffineSpace/PlaneCurveDimension.lean`, `ProjectiveSpace/PlaneCurveDimension.lean` | **var-dim** (complete) | R3, A7, P14, P16 |
| R5 | `FieldTheory/FunctionField/TwoGenerators.lean` | **var-twogen** for a separable `K/k(x)` | — |
| R6 | `FieldTheory/FunctionField/PlaneModel.lean` | **var-plane** (with a separating `x`) | R5 |
| R7 | `FieldTheory/FunctionField/RationalMap.lean` | **var-dominate**, **var-birational**, **var-finite** | R1, R3 |
| R8 | `FieldTheory/PrimitiveElement/OneSeparable.lean`, `FieldTheory/FunctionField/TwoGenerators.lean` | **var-twogen** (complete: any `x ∉ k`, any characteristic) | R5 |

### Stage 2: §§5.1–5.4, §7.1, and the nonsingular model of §7.5

| Part | Files | Content and milestones | Needs |
|---|---|---|---|
| Q1 | `PlaneCurve/Projective/Multiplicity.lean`, `RingTheory/MvPolynomial/OrderAtDehomogenize.lean` | **5-mult** | L2, P1 |
| Q2 | `PlaneCurve/Projective/Singular.lean` | parts (a), (b) of **5-sing**; **5-nonsing** (bridge to Tau Ceti) | Q1 |
| Q3 | `PlaneCurve/Projective/Tangent.lean` | part (d) of **5-sing**, Problem 5.6 | Q2 |
| Q4 | `PlaneCurve/Projective/LocalRing.lean` | `localEquation`, `localIdeal` | P16, A3 |
| Q5 | `PlaneCurve/Projective/CurveLocalRing.lean` | `functionField F`, `localSubring F P`; **5-local** | Q4, P11 |
| Q6 | `Projective/IntersectionNumber/Basic.lean` | `intersectionNumber`; properties (1)–(4), (7) | Q4, L7 |
| Q7 | `Projective/IntersectionNumber/Properties.lean` | **5-int**; **5-sing** (complete) | Q3, Q5, Q6, L8, L10 |
| Q8 | `PlaneCurve/Projective/Finiteness.lean` | **5-finite** | Q2, A3, A6 |
| Q9 | `Projective/LinearSystem/Basic.lean` | `linearSystem`; parts (a), (b) of **5-linsys** | Q1, Q3, P8 |
| Q10 | `Projective/LinearSystem/Independence.lean` | **5-linsys** (complete) | Q9 |
| Q11 | `RingTheory/MvPolynomial/QuotientSpanPair.lean`, `RingTheory/Regular/IsRelPrime.lean`, `Algebra/MvPolynomial/SetVarZero.lean` | Steps 1–2 of Bézout's proof | P3 |
| Q12 | `Projective/Bezout/Basic.lean` | **5-bezout** | Q7, Q8, Q11, L11, P8 |
| Q13 | `Projective/Bezout/Corollaries.lean` | **5-bezout-cor** | Q12 |
| Q14 | `Projective/MultiplePoints.lean` | **5-polar**, **5-bound** | Q10, Q13 |
| Q15 | `Projective/GenericLine.lean` | **5-generic** | Q13 |
| Q16 | `RingTheory/MvPolynomial/Hessian.lean`, `Projective/Hessian/Basic.lean` | the determinant of `TauCeti.hessian MvPolynomial.pderiv F`: homogeneity, covariance, the chart identity (*large*) | — |
| Q17 | `Projective/Hessian/Flex.lean` | **5-hessian** | Q16, Q13 |
| Q18 | `Projective/Conic.lean` | part (a) of **5-normal** | Q13 |
| V1 | `FieldTheory/FunctionField/Place/AddValuation.lean` | `TauCeti.Place.addValuation` | — |
| V2 | `PlaneCurve/Projective/Center.lean` | `IsCenter`, `center`; **7-centre** | Q5, R2 |
| V3 | `PlaneCurve/Place/Basic.lean`, `SimplePoint.lean` | `placesOver`, `ordForm`; **7-points** | V1, V2, L4 |
| V4 | `PlaneCurve/Place/RationalMap.lean` | **7-ratmap** | V2, R7 |
| V6 | `PlaneCurve/NonsingularModel/Normalization.lean` | **7-normalization** | V3, R1 |
| V7 | `FieldTheory/FunctionField/HolomorphyRing/Length.lean` | `ℓ(𝒪_S/g) = Σ ord_Q g`; the index lemma is Tau Ceti's `TauCeti.length_quotient_range_restrict` | V1 |
| V8 | `PlaneCurve/Place/IntersectionNumber.lean` | **7-intsum** | V6, V7, Q7, A12 |
| V5 | `PlaneCurve/NonsingularModel/Basic.lean` | **7-model**; **7-classify** (existing, with plane-curve corollaries) | V3, V8 |

### Stage 3: §§5.5–5.6 and §§7.2–7.4

| Part | Files | Content and milestones | Needs |
|---|---|---|---|
| N1 | `Projective/IntersectionCycle.lean`, `Projective/Noether/Basic.lean` | `intersectionCycle`; **5-noether** | Q12, Q5, A11 |
| N2 | `Projective/Noether/Conditions.lean` | **5-noether-local** | N1, L4, L8 |
| N3 | `PlaneCurve/Cubic/Residual.lean` | **5-residual**, **5-ninth** | N2, Q14 |
| N4 | `PlaneCurve/Projective/Pascal.lean` | **5-pascal**, **5-pappus** | N3 |
| N5 | `PlaneCurve/Cubic/NormalForm.lean` | **5-normal** (complete) | Q18, Q14, Q17 |
| N6 | `PlaneCurve/Cubic/Chord.lean`, `GroupLaw.lean` | **5-group** (*large*) | N3, Q2 |
| N7 | `PlaneCurve/Cubic/Weierstrass.lean` | **5-weierstrass** (*large*) | N6, N5, L10 |
| N8 | `PlaneCurve/Cubic/Flex.lean` | **5-torsion** | N7, Q17 |
| N9 | `PlaneCurve/Cubic/CutOut.lean` | **5-cutout** | N6, N2, N8 |
| B1 | `PlaneCurve/Affine/Blowup/Basic.lean` | parts (1)–(2) of **7-blowup** | L8, L10, A4 |
| B2 | `PlaneCurve/Affine/Blowup/Chart.lean` | **7-blowup** (complete) | B1 |
| B3 | `PlaneCurve/Place/OrdinaryMultiplePoint.lean` | **7-ordinary** | V3, B2, L12 |
| B4 | `PlaneCurve/Affine/Blowup/IntersectionNumber.lean` | **7-noether-formula** (local form) | B2, V8 |
| B5 | `PlaneCurve/NonsingularModel/OrdinaryMultiplePoints.lean` | **7-resolve** | V5, B3 |
| T1 | `RingTheory/MvPolynomial/PolarDerivative.lean`, `Projective/TerriblePoint.lean` | **7-terrible** | Q13, L10 |
| T2 | `QuadraticTransformation/Basic.lean` | **7-quadratic** | Q3 |
| T3 | `QuadraticTransformation/Position.lean`, `Singularities.lean` | **7-quadratic-centre** (*large*) | T1, T2, B1, L5, L12, Q14, P9 |
| T4 | `QuadraticTransformation/Resolution.lean` | **7-reduce** | T3 |
| T5 | `QuadraticTransformation/NeighbouringSingularities.lean` | the global form of **7-noether-formula** | T4, B4, Q12 |

### Stage 4: Noether's conditions at an ordinary multiple point

| Part | Files | Content and milestones | Needs |
|---|---|---|---|
| O1 | `PlaneCurve/Place/Conductor.lean` | **7-conductor** | B3, N2 |

### Stage 5: Chapter 8

D1–D3 need only Tau Ceti and can start at once; D4 needs only stage 2.

| Part | Files | Content and milestones | Needs |
|---|---|---|---|
| D1 | `FieldTheory/FunctionField/KaehlerDifferential.lean` | `kaehlerDifferentialDivisor`; **8-differential**; Riemann–Roch for Kähler canonical divisors | — |
| D2 | `FieldTheory/FunctionField/RiemannRoch.lean` | **8-riemann** (corollaries of Tau Ceti); **8-reduction** | D1 |
| D3 | `FieldTheory/FunctionField/Rational.lean` | part (a) of **8-genus01** | — |
| D4 | `PlaneCurve/Divisor.lean` | `formQuotient`, `formDivisor`; **8-divisor** | V5, V8, Q12 |
| D5 | `PlaneCurve/Adjoint/Basic.lean` | `adjointDivisor`, `IsAdjoint`, `adjointSubmodule`; **8-adjoint** | D4, B3 |
| D6 | `PlaneCurve/Cubic/DivisorClass.lean` | **8-cubic** | D4, N6, V3 |
| D7 | `PlaneCurve/Adjoint/Residue.lean` | adjoint division lemma; **8-residue** | D5, N2, O1 |
| D8 | `PlaneCurve/Adjoint/RiemannRochSpace.lean` | **8-lem** | D7, Q10 |
| D9 | `PlaneCurve/Genus/Basic.lean` | **8-genus** | D8, D2 |
| D10 | `PlaneCurve/Genus/VirtualGenus.lean`, `Examples.lean` | **8-virtual** | D9, T4, D3 |
| D11 | `PlaneCurve/Cubic/GenusOne.lean` | **8-genus01** (complete) | D9, D3, N5, N7 |
| D12 | `PlaneCurve/CanonicalDivisor/Basic.lean`, `Position.lean`, `Differential.lean`; `Algebra/MvPolynomial/Derivation.lean` | **8-canonical** (*large*) | D1, D9, B3, T1 |
| D13 | `PlaneCurve/RiemannRoch.lean` | **8-rr**, **8-independence** | D12, D2 |

The order departs from the atlas's stages only in placing D1–D3 at the
start (the atlas allows §8.4 to start early, and D2–D3 are statements about
Tau Ceti's function fields), and the projective half of R4 after P16.

## Milestones

Every milestone of the atlas, by page, with its short name (used above), the
file that proves it and its part, or the existing declaration that already
proves it in full. Paths are under `PlaneCurves/` unless they start with
`TauCeti/`. Count: 10 + 16 + 8 + 24 + 8 + 16 + 14 = 96.

### `auxiliary/affine-varieties.md` (10)

| Short name | Milestone | File (part) |
|---|---|---|
| aff-coprime | Coprime plane polynomials have finitely many common zeros | `AlgebraicGeometry/AffineSpace/PlaneZeroLocus.lean` (A6) |
| aff-hypersurface | Reduced equations and irreducible components of affine hypersurfaces | `AlgebraicGeometry/AffineSpace/Hypersurface.lean` (A7) |
| aff-finite | Finite zero sets and finite-dimensional quotients of polynomial rings | `AlgebraicGeometry/AffineSpace/FiniteZeroLocus.lean` (A8) |
| aff-local | Local ring of an affine variety at a point | `AlgebraicGeometry/AffineSpace/RationalFunction.lean` (A10) |
| aff-hom | Homogenization and dehomogenization of polynomials | `RingTheory/MvPolynomial/Homogenize/Factorization.lean` (A3) |
| aff-binary | Binary forms over an algebraically closed field split into linear forms | `RingTheory/MvPolynomial/BinaryForm/Basic.lean` (A4) |
| aff-quotient | Local rings of a subvariety as quotients of the local ring of affine space | `AlgebraicGeometry/AffineSpace/LocalRing.lean` (A9) |
| aff-dim | Dimensions of spaces of forms and of polynomials modulo a power of the ideal of a point | `RingTheory/MvPolynomial/PowIdealOfVars.lean` (A5); part (a) is Tau Ceti's `TauCeti.finrank_homogeneousSubmodule_eq_multichoose` |
| aff-global | Global-to-local decomposition of a polynomial ring modulo an ideal with finitely many zeros | `AlgebraicGeometry/AffineSpace/QuotientPiLocalRing.lean` (A11) |
| aff-dvr | Order equals colength in a discrete valuation ring with residue field k | `RingTheory/DiscreteValuationRing/Colength.lean` (A12) |

### `atlas/01-local-properties.md` (16)

| Short name | Milestone | File (part) |
|---|---|---|
| 3-mult | Multiplicity and simple points of an affine plane curve | `PlaneCurve/Affine/Multiplicity.lean` (L2) |
| 3-product | Multiplicity and tangent lines of a product of plane curves | `PlaneCurve/Affine/Tangent.lean` (L2) |
| 3-finite | Finiteness of the multiple points of a reduced plane curve | `PlaneCurve/Affine/MultiplePoint.lean` (L3) |
| 3-dvr | Simple points of a plane curve are those with a discrete valuation local ring | `PlaneCurve/Affine/LocalRing.lean` (L4) |
| 3-ring | Multiplicity of a plane curve is determined by its local ring | `PlaneCurve/Affine/HilbertSamuel.lean` (L5) |
| 3-embdim | Embedding dimension of a plane curve at a point | `PlaneCurve/Affine/HilbertSamuel.lean` (L5) |
| 3-finvan | Finiteness and vanishing of the local intersection number | `PlaneCurve/Affine/IntersectionNumber/Basic.lean` (L6) |
| 3-add | Additivity of local intersection numbers | `PlaneCurve/Affine/IntersectionNumber/Additivity.lean` (L7) |
| 3-power | Powers of the maximal ideal in the ideal of two curves without common tangents | `PlaneCurve/Affine/IntersectionNumber/Multiplicity.lean` (L8) |
| 3-prodmult | Intersection number is at least the product of the multiplicities | `PlaneCurve/Affine/IntersectionNumber/Multiplicity.lean` (L8) |
| 3-axioms | Characterization of the local intersection number by Fulton's seven properties | `PlaneCurve/Affine/IntersectionNumber/Uniqueness.lean` (L9) |
| 3-order | Intersection number at a simple point is an order of vanishing | `PlaneCurve/Affine/IntersectionNumber/SimplePoint.lean` (L10) |
| 3-sum | Sum of local intersection numbers equals the dimension of the intersection ring | `PlaneCurve/Affine/IntersectionNumber/Sum.lean` (L11) |
| 3-tangency | Tangency of a line detected by the intersection number | `PlaneCurve/Affine/IntersectionNumber/Multiplicity.lean` (L8) |
| 3-line | Intersection of a plane curve with a line | `PlaneCurve/Affine/IntersectionNumber/Line.lean` (L10) |
| 3-ordinary | Local-ring characterization of ordinary multiple points | `PlaneCurve/Affine/OrdinaryMultiplePoint.lean` (L12) |

(`PlaneCurve/` stands for `AlgebraicGeometry/PlaneCurve/` here and below.)

### `auxiliary/projective-varieties.md` (8)

| Short name | Milestone | File (part) |
|---|---|---|
| proj-charts | Standard affine charts of projective space | `LinearAlgebra/Projectivization/AffineChart.lean` (P1), for part (c); parts (a), (b), (e) are Tau Ceti's `Projectivization.affineChart`, `Projectivization.iUnion_affineOpen`, `RingHom.mapProjective_injective` (`TauCeti/LinearAlgebra/Projectivization/AffineChart.lean`, `BaseChange.lean`), part (d) Mathlib's `OnePoint.equivProjectivization` |
| proj-ideals | Homogeneous ideals and graded quotients of the polynomial ring | `RingTheory/MvPolynomial/HilbertFunction.lean` (P3), with `HomogeneousIdeal.lean` (P2); parts (b)–(d) are Mathlib's `Ideal.IsHomogeneous.isPrime_iff`, `Ideal.IsHomogeneous.radical` (and `sup`, `inf`, `mul`) and Tau Ceti's `TauCeti.GradedAlgebra.isInternal_quotientPiece` |
| proj-sets | Projective algebraic sets, their ideals and affine cones | `AlgebraicGeometry/ProjectiveSpace/Irreducible.lean` (P6), with `ZeroLocus.lean` (P4) |
| proj-null | Projective Nullstellensatz | `AlgebraicGeometry/ProjectiveSpace/Hypersurface.lean` (P7), with `Nullstellensatz.lean` (P5) |
| proj-coord | Homogeneous coordinate ring, function field and local rings of a projective variety | `AlgebraicGeometry/ProjectiveSpace/ChangeOfCoordinates.lean` (P12), with `FunctionField.lean` (P11) |
| proj-linear | Linear subvarieties and projective changes of coordinates in projective space | `LinearAlgebra/Projectivization/Duality.lean` (P9), with `LinearSubspace.lean` (P8) |
| proj-closure | Projective closure of affine algebraic sets | `AlgebraicGeometry/ProjectiveSpace/Subvariety.lean` (P15), with `ProjectiveClosure.lean` (P14) and `RingTheory/MvPolynomial/Homogenize/Ideal.lean` (P13) |
| proj-charts-local | Affine charts preserve function fields and local rings | `AlgebraicGeometry/ProjectiveSpace/ChartLocalRing.lean` (P16) |

A milestone with several parts in several files is one theorem in the last
file listed first (for example `proj-null`), which combines the parts proved
before it; its docstring carries the milestone line.

### `atlas/02-projective-plane-curves.md` (24)

| Short name | Milestone | File (part) |
|---|---|---|
| 5-mult | Multiplicity of a projective plane curve at a point | `PlaneCurve/Projective/Multiplicity.lean` (Q1) |
| 5-sing | Singular points and tangent lines of a projective plane curve via partial derivatives | `PlaneCurve/Projective/IntersectionNumber/Properties.lean` (Q7), with `Singular.lean` (Q2) and `Tangent.lean` (Q3) |
| 5-local | Local ring of an irreducible projective plane curve as a quotient and in affine charts | `PlaneCurve/Projective/CurveLocalRing.lean` (Q5) |
| 5-int | Intersection number of projective plane curves at a point | `PlaneCurve/Projective/IntersectionNumber/Properties.lean` (Q7) |
| 5-finite | Finiteness of the intersection of two projective plane curves | `PlaneCurve/Projective/Finiteness.lean` (Q8) |
| 5-linsys | Dimension of linear systems of plane curves with assigned multiple points | `PlaneCurve/Projective/LinearSystem/Independence.lean` (Q10) |
| 5-bezout | Bézout's theorem for projective plane curves | `PlaneCurve/Projective/Bezout/Basic.lean` (Q12) |
| 5-bezout-cor | Corollaries of Bézout's theorem on multiplicities and common points | `PlaneCurve/Projective/Bezout/Corollaries.lean` (Q13) |
| 5-nonsing | Nonsingular projective plane curves are irreducible | existing: Tau Ceti's `TauCeti.irreducible_of_isHomogeneous` (`TauCeti/RingTheory/MvPolynomial/CommonZero.lean`); the library adds only `Projective.IsNonsingular.irreducible` in `PlaneCurve/Projective/Singular.lean` (Q2) |
| 5-polar | Polar bound on the multiple points of an irreducible plane curve | `PlaneCurve/Projective/MultiplePoints.lean` (Q14) |
| 5-hessian | Hessian criterion for flexes and the nine flexes of a nonsingular cubic | `PlaneCurve/Projective/Hessian/Flex.lean` (Q17) |
| 5-normal | Projective normal forms of irreducible conics and cubics (Weierstrass form) | `PlaneCurve/Cubic/NormalForm.lean` (N5), with `Projective/Conic.lean` (Q18) |
| 5-bound | Bound on the multiple points of an irreducible plane curve | `PlaneCurve/Projective/MultiplePoints.lean` (Q14) |
| 5-generic | Generic lines through a point meet an irreducible curve in distinct points | `PlaneCurve/Projective/GenericLine.lean` (Q15) |
| 5-noether | Max Noether's fundamental theorem | `PlaneCurve/Projective/Noether/Basic.lean` (N1) |
| 5-noether-local | Local criteria for Noether's conditions and the residual intersection corollary | `PlaneCurve/Projective/Noether/Conditions.lean` (N2) |
| 5-residual | Residual points of a conic on a cubic are collinear | `PlaneCurve/Cubic/Residual.lean` (N3) |
| 5-pascal | Pascal's theorem for a hexagon inscribed in an irreducible conic | `PlaneCurve/Projective/Pascal.lean` (N4) |
| 5-pappus | Pappus's theorem | `PlaneCurve/Projective/Pascal.lean` (N4) |
| 5-ninth | Eight simple points of an irreducible cubic determine the ninth | `PlaneCurve/Cubic/Residual.lean` (N3) |
| 5-group | Group law on a nonsingular plane cubic | `PlaneCurve/Cubic/GroupLaw.lean` (N6) |
| 5-weierstrass | Chord–tangent addition on a Weierstrass cubic agrees with Mathlib's group law | `PlaneCurve/Cubic/Weierstrass.lean` (N7) |
| 5-torsion | Flexes of a nonsingular cubic and the torsion of its group | `PlaneCurve/Cubic/Flex.lean` (N8) |
| 5-cutout | Points of a nonsingular cubic cut out by a curve of degree m | `PlaneCurve/Cubic/CutOut.lean` (N9) |

### `auxiliary/varieties-and-rational-maps.md` (8)

| Short name | Milestone | File (part) |
|---|---|---|
| var-principal | Regular functions on a principal open subset of an affine variety | `RingTheory/Localization/RegularFunctions.lean` (R1) |
| var-twogen | Two-generator presentation of a function field of one variable | `FieldTheory/FunctionField/TwoGenerators.lean` (R5, R8); part (1) is Tau Ceti's `TauCeti.IsFunctionField.finiteDimensional_adjoin` |
| var-residue | Residue rings of subrings of a function field of one variable | `FieldTheory/FunctionField/ResidueRing.lean` (R2) |
| var-dim | Dimension of curves and of closed subvarieties of the plane | `AlgebraicGeometry/ProjectiveSpace/PlaneCurveDimension.lean` (R4), with `RingTheory/KrullDimension/TrdegOne.lean` (R3) and `AffineSpace/PlaneCurveDimension.lean` (R4) |
| var-dominate | Dominating rational maps correspond to function-field embeddings | `FieldTheory/FunctionField/RationalMap.lean` (R7) |
| var-birational | Birational equivalence is isomorphism of function fields | `FieldTheory/FunctionField/RationalMap.lean` (R7) |
| var-plane | Every curve is birational to an affine plane curve | `FieldTheory/FunctionField/PlaneModel.lean` (R6) |
| var-finite | Rational maps between curves are constant or finite | `FieldTheory/FunctionField/RationalMap.lean` (R7) |

For `var-twogen`, R5 proves the theorem for a separable `K/k(x)`, and R8
completes it, in `TwoGenerators.lean`, for every `x ∉ k`.

### `atlas/03-resolution-of-singularities.md` (16)

| Short name | Milestone | File (part) |
|---|---|---|
| 7-centre | Centre of a discrete valuation ring on a projective curve | `PlaneCurve/Projective/Center.lean` (V2) |
| 7-ratmap | Rational maps from a curve to a projective curve are defined at simple points | `PlaneCurve/Place/RationalMap.lean` (V4) |
| 7-points | Points of a nonsingular projective curve are the places of its function field | `PlaneCurve/Place/SimplePoint.lean` (V3) |
| 7-blowup | Blowing up a plane curve at a point: strict transform, fibre and local finiteness | `PlaneCurve/Affine/Blowup/Chart.lean` (B2), with `Blowup/Basic.lean` (B1) |
| 7-ordinary | Orders at the places over an ordinary multiple point | `PlaneCurve/Place/OrdinaryMultiplePoint.lean` (B3) |
| 7-resolve | Resolution of a plane curve with only ordinary multiple points by blowing up | `PlaneCurve/NonsingularModel/OrdinaryMultiplePoints.lean` (B5) |
| 7-quadratic | Proper transform of a plane curve under the standard quadratic transformation | `PlaneCurve/QuadraticTransformation/Basic.lean` (T2) |
| 7-terrible | Terrible points and lines meeting a plane curve in n distinct points | `PlaneCurve/Projective/TerriblePoint.lean` (T1) |
| 7-quadratic-centre | Quadratic transformation centred at a point and its new singularities | `PlaneCurve/QuadraticTransformation/Singularities.lean` (T3) |
| 7-reduce | Reduction of a plane curve to ordinary multiple points by quadratic transformations | `PlaneCurve/QuadraticTransformation/Resolution.lean` (T4) |
| 7-noether-formula | Noether's formula for intersection numbers at infinitely near points | `PlaneCurve/QuadraticTransformation/NeighbouringSingularities.lean` (T5), with the local form in `Affine/Blowup/IntersectionNumber.lean` (B4) |
| 7-model | Existence and uniqueness of the nonsingular model of a projective curve | `PlaneCurve/NonsingularModel/Basic.lean` (V5) |
| 7-classify | Nonsingular projective curves correspond to function fields of one variable | existing: Tau Ceti's `AlgebraicGeometry.Scheme.homOfFunctionFieldAlgHom`, `AlgebraicGeometry.Scheme.functionFieldAlgHom_homOfFunctionFieldAlgHom`, `AlgebraicGeometry.Scheme.homOfFunctionFieldAlgHom_functionFieldAlgHom`, `AlgebraicGeometry.Scheme.isoOfFunctionFieldAlgEquiv` (`TauCeti/AlgebraicGeometry/Birational/AlgHom.lean`) and `TauCeti.AlgebraicGeometry.RegularProjectiveCurveCat.equivFunctionFieldCat` (`TauCeti/AlgebraicGeometry/Curves/TwoChartModel/AntiEquivalence.lean`); "dominant morphisms are surjective" (Problem 8.18) was not found and is proved in `PlaneCurve/NonsingularModel/Basic.lean` (V5) |
| 7-normalization | Finiteness of the normalization of a plane curve near a point | `PlaneCurve/NonsingularModel/Normalization.lean` (V6) |
| 7-intsum | Intersection numbers as sums of orders at places | `PlaneCurve/Place/IntersectionNumber.lean` (V8) |
| 7-conductor | Noether's conditions at an ordinary multiple point via orders at places | `PlaneCurve/Place/Conductor.lean` (O1) |

### `atlas/04-riemann-roch.md` (14)

| Short name | Milestone | File (part) |
|---|---|---|
| 8-divisor | Divisors cut out by forms on the nonsingular model of a plane curve | `PlaneCurve/Divisor.lean` (D4) |
| 8-adjoint | Adjoint curves of a plane curve with ordinary multiple points | `PlaneCurve/Adjoint/Basic.lean` (D5) |
| 8-residue | Brill–Noether residue theorem for plane curves | `PlaneCurve/Adjoint/Residue.lean` (D7) |
| 8-cubic | Chord–tangent group of a nonsingular cubic as its divisor class group | `PlaneCurve/Cubic/DivisorClass.lean` (D6) |
| 8-riemann | Riemann's theorem on the nonsingular model of a plane curve | existing: Tau Ceti's `TauCeti.genus`, `TauCeti.Divisor.degree_add_one_sub_genus_le_dim`, `TauCeti.exists_degree_add_one_sub_dim_eq_genus`, `TauCeti.exists_forall_dim_eq_degree_add_one_sub_genus` (`TauCeti/FieldTheory/FunctionField/RiemannRoch/Genus.lean`), `TauCeti.genus_eq_of_ringEquiv` (`…/RiemannRoch/Equiv.lean`); Corollaries 1 and 2, which Tau Ceti does not state, in `FieldTheory/FunctionField/RiemannRoch.lean` (D2) |
| 8-lem | Adjoints of degree m compute the Riemann–Roch spaces L(E_m) | `PlaneCurve/Adjoint/RiemannRochSpace.lean` (D8) |
| 8-genus | Genus formula for plane curves with only ordinary multiple points | `PlaneCurve/Genus/Basic.lean` (D9) |
| 8-virtual | Genus bound by the virtual genus of a plane curve | `PlaneCurve/Genus/VirtualGenus.lean` (D10) |
| 8-genus01 | Curves of genus zero and one and their plane models | `PlaneCurve/Cubic/GenusOne.lean` (D11), with `FieldTheory/FunctionField/Rational.lean` (D3) |
| 8-differential | Order and divisor of a differential on the nonsingular model | `FieldTheory/FunctionField/KaehlerDifferential.lean` (D1) |
| 8-canonical | Canonical divisors of a plane curve are cut out by adjoints of degree n − 3 | `PlaneCurve/CanonicalDivisor/Differential.lean` (D12) |
| 8-reduction | Noether's reduction lemma | `FieldTheory/FunctionField/RiemannRoch.lean` (D2) |
| 8-rr | Riemann–Roch theorem for the nonsingular model of a plane curve | `PlaneCurve/RiemannRoch.lean` (D13), with the function-field form in `FieldTheory/FunctionField/KaehlerDifferential.lean` (D1) |
| 8-independence | Independence of adjoint conditions in degree at least n − 3 | `PlaneCurve/RiemannRoch.lean` (D13) |

Three milestones are already proved in full and are not counted as work:
**5-nonsing**, **7-classify** and **8-riemann**, as the atlas's front page
says. For each, the library adds only the bridge or the corollaries named.

## Departures from the atlas

1. **Chart-free localized ideals in `𝒪_P(ℙ²)`.** The projective intersection
   number is the length of `𝒪_P(ℙ²) ⧸ localIdeal P (span {F, G})`, not of a
   quotient by `F_*, G_*` for a chosen `L`. The two agree (`localIdeal_span_pair`),
   and the definition then needs no choice. Noether's conditions are stated
   with the same `localIdeal`.
2. **Function fields and local rings of any homogeneous prime.** `k(V)` and
   `𝒪_P(V)` are defined once, for a homogeneous prime ideal of the
   polynomial ring (`ProjectiveSpace.functionField`, `localSubring`), and
   used both for `I(V)` (Chapter 4) and for `(F)` (Chapter 5). This is the
   atlas's representation, shared.
3. **Theorem 1 of §3.2 through regular local rings.** The atlas suggests the
   cotangent-space route; `IsLocalRing.finrank_CotangentSpace_eq_one_iff`
   assumes a domain, which `𝒪_P(𝔸²)/(F)` need not be. The design uses Tau
   Ceti's `TauCeti.IsRegularLocalRing.quotient_span_singleton_iff` and
   `TauCeti.IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one`,
   which prove the general (reducible) form in both directions.
4. **"Proper intersection" without `gcd`.** The atlas writes
   `eval P (gcd F G) ≠ 0`; `MvPolynomial` has no `GCDMonoid` instance, so
   the design uses `IntersectProperlyAt` (no irreducible common factor
   vanishes at `P`).
5. **Pure linear algebra of `ℙⁿ` under `LinearAlgebra/Projectivization/`.**
   The hyperplane at infinity, linear subvarieties and duality are about
   Mathlib's `Projectivization`, so they live in its namespace and folder,
   ready to move upstream; only their translation into zero loci is in
   `AlgebraicGeometry/ProjectiveSpace/`.
6. **Problem 4.10 in `ℤ`.** `dim (k[X,Y,Z]/(F))_d = dm − m(m−3)/2` is stated
   in `ℤ` (or in the additive form of Tau Ceti's
   `TauCeti.GradedAlgebra.finrank_quotientPiece_span_singleton_add`), since
   `m(m−3)` is negative for `m = 1, 2`.
7. **The blow-up of `ℙ²` (§7.3) through the nonsingular model.** Fulton's
   `B ⊆ ℙ² × (ℙ¹)ᵗ` needs multiprojective varieties, which the atlas
   defers. Part B5 proves the milestone on the atlas's recommended route:
   the places of `k(C)` with the centre map are the nonsingular model, the
   centre map is bijective off the `P_i`, and the places over `P_i` are in
   bijection with the tangents. If the pull request finds that this is not
   the milestone's statement, it either builds `C'` with Tau Ceti's scheme
   blow-up (`AlgebraicGeometry.Scheme.IdealSheafData.blowup`) or records the
   change in `ERRATA.md`, as `AGENTS.md` says.
8. **Rational maps between curves (Problem 6.45).** A rational map to an
   affine curve is given on the points side, as a `k`-algebra map from its
   coordinate ring to the function field of the source, so that "constant or
   dominating" has content; the function-field form follows.
9. **Group of a cubic as its class group without the residue theorem.** Part
   D6 proves the milestone from the definition of `⊕`, the divisors of
   quotients of lines, and Tau Ceti's `TauCeti.Place.eq_of_linearlyEquivalent_ofPoint_of_genus_pos`
   and `TauCeti.Place.degreeOneAddEquivDegreeZeroClassGroup`, so that it does
   not wait for Max Noether's theorem (the atlas allows either route).
10. **Chapter 8's function-field results in `FieldTheory/FunctionField/`.**
    The Kähler divisor, Noether's reduction lemma, the corollaries of
    Riemann's theorem and the genus-zero criteria are statements about any
    function field, so they are placed with Tau Ceti's function fields, not
    under `PlaneCurve/`, and can be done first (stage 5 parts D1–D3).
11. **No wrapper for `𝒪_P(𝔸²)/(F)` or for the genus.** The local ring of an
    affine plane curve is written as the quotient, with `Ring.ord` as its
    order, and the genus is `TauCeti.genus k K`, as the atlas advises.
    `AffineSpace.localRing` and `ProjectiveSpace.localRing` are `abbrev`s
    for the standard objects, used everywhere.
