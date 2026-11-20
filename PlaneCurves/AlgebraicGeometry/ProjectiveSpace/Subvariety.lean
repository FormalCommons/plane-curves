/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.AffineSpace.Hypersurface
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.ProjectiveClosure
public import PlaneCurves.RingTheory.MvPolynomial.Homogeneous

/-!
# Subvarieties of projective space

A projective variety is a set `W ⊆ ℙⁿ` with `zeroLocus (vanishingIdeal W) = W` and
`(vanishingIdeal W).toIdeal` prime. This file proves Fulton's Problems 4.21–4.23: a variety
containing a hypersurface is that hypersurface or `ℙⁿ`, and the subvarieties of `ℙ¹` and `ℙ²`
are listed. It then assembles the statements of §4.3 on projective closures.

## Main results

* `eq_zeroLocus_singleton_or_eq_univ`: if `V(F) ⊆ W` for a form `F` of positive degree and a
  projective variety `W`, then `W = V(F)` or `W = ℙⁿ` (Problem 4.21).
* `eq_compl_affineOpen_or_eq_univ`: a projective variety containing the hyperplane at infinity
  `H_∞ = (affineOpen i)ᶜ` is `H_∞` or `ℙⁿ` (Problem 4.22).
* `isPrime_vanishingIdeal_projectiveLine_iff`: over an infinite field, the subvarieties of `ℙ¹`
  are its points and `ℙ¹`.
* `isPrime_vanishingIdeal_projectivePlane_iff`: over an algebraically closed field, the
  subvarieties of `ℙ²` are its points, the curves `V(F)` with `F` an irreducible form, and `ℙ²`
  (Problem 4.23).
* `not_subset_and_not_superset_compl_affineOpen`: Proposition 3 (6) for the components of `V*`.
* `projectiveClosure_spec`: the statements of Fulton's §4.3 on the projective closure, in his
  form.

## Implementation notes

Problem 4.21 holds over any algebraically closed field and every `n` (for `n = 0`, `ℙ⁰` is a
point), and for every hypersurface `V(F)`, irreducible or not: `I(W) ⊆ Rad (F) ⊆ (p)` for an
irreducible factor `p` of `F` forces `I(W) = (p)` when `I(W) ≠ 0`. The lists of Problem 4.23 are
proved by moving a variety `W` to a chart `Uⱼ` that it meets: then `W = (W_*)*`, and `W_*` is a
variety of `𝔸¹` or `𝔸²`, which `isPrime_vanishingIdeal_line_iff` and
`isPrime_vanishingIdeal_plane_iff` list.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §4.3, Proposition 3 and Problems 4.19–4.23
-/

public section

open MvPolynomial Projectivization TauCeti
open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PlaneCurves.ProjectiveSpace

variable {k : Type*} [Field k] {n : ℕ}


/-- **Fulton, Problem 4.21.** Over an algebraically closed field, a projective variety `W`
containing a hypersurface `V(F)`, `F` a form of positive degree, is `V(F)` or `ℙⁿ`. The
hypersurface need not be irreducible. -/
theorem eq_zeroLocus_singleton_or_eq_univ [IsAlgClosed k] {F : MvPolynomial (Fin (n + 1)) k}
    {d : ℕ} (hF : F.IsHomogeneous d) (hd : d ≠ 0)
    {W : Set (ℙ k (Fin (n + 1) → k))} (hW : zeroLocus (vanishingIdeal W) = W)
    (hWp : (vanishingIdeal W).toIdeal.IsPrime) (h : zeroLocus {F} ⊆ W) :
    W = zeroLocus {F} ∨ W = Set.univ := by
  obtain hn | hn := eq_or_ne n 0
  · exact .inr (eq_univ_of_isPrime_vanishingIdeal_of_eq_zero hn hWp)
  obtain rfl | hF0 := eq_or_ne F 0
  · rw [zeroLocus_singleton_zero] at h
    exact .inr (Set.univ_subset_iff.1 h)
  by_cases hbot : vanishingIdeal W = ⊥
  · right
    rw [← hW, hbot, HomogeneousIdeal.coe_bot]
    exact zeroLocus_singleton_zero
  left
  have hFu : ¬ IsUnit F := fun hu ↦ hd (hF.eq_zero_of_isUnit hu)
  obtain ⟨p, hp, hpF⟩ := WfDvdMonoid.exists_irreducible_factor hFu hF0
  -- `I(W) ⊆ I(V(F)) = Rad (F) ⊆ (p)`, so the nonzero prime `I(W)` is `(p)`, and then
  -- `I(V(F)) ⊆ (p) = I(W)`.
  have hle : (vanishingIdeal (zeroLocus ({F} : Set (MvPolynomial (Fin (n + 1)) k)))).toIdeal ≤
      Ideal.span {p} := by
    rw [vanishingIdeal_zeroLocus_singleton hn hF]
    exact ((Ideal.span_singleton_prime hp.ne_zero).2 hp.prime).radical_le_iff.2
      (Ideal.span_singleton_le_span_singleton.2 hpF)
  have hWV := vanishingIdeal_anti_mono h
  have hWV' : (vanishingIdeal W).toIdeal ≤ _ := hWV
  have hWeq := hWp.eq_span_singleton_of_le (fun h0 ↦ hbot (HomogeneousIdeal.toIdeal_injective
    (h0.trans HomogeneousIdeal.toIdeal_bot.symm))) hp (hWV'.trans hle)
  have : vanishingIdeal W = vanishingIdeal (zeroLocus {F}) :=
    hWV.antisymm fun x hx ↦ HomogeneousIdeal.mem_iff.1 (hWeq ▸ hle (HomogeneousIdeal.mem_iff.2 hx))
  rw [← hW, this, zeroLocus_vanishingIdeal_zeroLocus_of_isHomogeneous fun g hg ↦
    ⟨d, (Set.mem_singleton_iff.1 hg) ▸ hF⟩]

/-- **Fulton, Problem 4.22.** Over an algebraically closed field, a projective variety
containing the hyperplane at infinity `H_∞ = (affineOpen i)ᶜ` is `H_∞` or `ℙⁿ`. -/
theorem eq_compl_affineOpen_or_eq_univ [IsAlgClosed k] (i : Fin (n + 1))
    {W : Set (ℙ k (Fin (n + 1) → k))} (hW : zeroLocus (vanishingIdeal W) = W)
    (hWp : (vanishingIdeal W).toIdeal.IsPrime) (h : (affineOpen i)ᶜ ⊆ W) :
    W = (affineOpen i)ᶜ ∨ W = Set.univ := by
  rw [← zeroLocus_singleton_X] at h ⊢
  exact eq_zeroLocus_singleton_or_eq_univ (isHomogeneous_X k i) one_ne_zero hW hWp h

/-! ### Subvarieties of the projective line and plane -/

/-- **Subvarieties of `ℙ¹`.** Over an infinite field, a subset of `ℙ¹` is a projective variety
exactly when it is a point or `ℙ¹`. -/
theorem isPrime_vanishingIdeal_projectiveLine_iff [Infinite k] {W : Set (ℙ k (Fin 2 → k))} :
    (zeroLocus (vanishingIdeal W) = W ∧ (vanishingIdeal W).toIdeal.IsPrime) ↔
      (∃ P, W = {P}) ∨ W = Set.univ := by
  refine ⟨fun ⟨hW, hWp⟩ ↦ ?_, ?_⟩
  · obtain ⟨j, hj⟩ := exists_not_subset_compl_affineOpen (nonempty_of_isPrime_vanishingIdeal hWp)
    rw [← projectiveClosure_affinePart hW hWp hj]
    rcases isPrime_vanishingIdeal_line_iff.1 ⟨⟨_, (zeroLocus_vanishingIdeal_affinePart W).symm⟩,
      isPrime_vanishingIdeal_affinePart hW hWp hj⟩ with h | ⟨x, h⟩
    · exact .inr (by rw [h, projectiveClosure_univ])
    · exact .inl ⟨_, by rw [h, projectiveClosure_singleton]⟩
  · rintro (⟨P, rfl⟩ | rfl)
    · exact ⟨zeroLocus_vanishingIdeal_singleton P, inferInstance⟩
    · exact ⟨zeroLocus_vanishingIdeal_univ, isPrime_vanishingIdeal_univ⟩

/-- **Fulton, Problem 4.23: subvarieties of `ℙ²`.** Over an algebraically closed field, a subset
of `ℙ²` is a projective variety exactly when it is a point, a curve `V(F)` with `F` an irreducible
form, or `ℙ²`. -/
theorem isPrime_vanishingIdeal_projectivePlane_iff [IsAlgClosed k] {W : Set (ℙ k (Fin 3 → k))} :
    (zeroLocus (vanishingIdeal W) = W ∧ (vanishingIdeal W).toIdeal.IsPrime) ↔
      (∃ P, W = {P}) ∨
        (∃ (F : MvPolynomial (Fin 3) k) (d : ℕ), F.IsHomogeneous d ∧ Irreducible F ∧
          W = zeroLocus {F}) ∨
        W = Set.univ := by
  refine ⟨fun ⟨hW, hWp⟩ ↦ ?_, ?_⟩
  · obtain ⟨j, hj⟩ := exists_not_subset_compl_affineOpen (nonempty_of_isPrime_vanishingIdeal hWp)
    rw [← projectiveClosure_affinePart hW hWp hj]
    rcases isPrime_vanishingIdeal_plane_iff.1 ⟨⟨_, (zeroLocus_vanishingIdeal_affinePart W).symm⟩,
      isPrime_vanishingIdeal_affinePart hW hWp hj⟩ with h | ⟨x, h⟩ | ⟨f, hf, -, h⟩
    · exact .inr (.inr (by rw [h, projectiveClosure_univ]))
    · exact .inl ⟨_, by rw [h, projectiveClosure_singleton]⟩
    · exact .inr (.inl ⟨_, _, isHomogeneous_homogenize j _ f,
        irreducible_homogenize_totalDegree hf,
        by rw [h, projectiveClosure_zeroLocus_span_singleton]⟩)
  · rintro (⟨P, rfl⟩ | ⟨F, d, hF, hFi, rfl⟩ | rfl)
    · exact ⟨zeroLocus_vanishingIdeal_singleton P, inferInstance⟩
    · exact ⟨zeroLocus_vanishingIdeal_zeroLocus_of_isHomogeneous fun g hg ↦
        ⟨d, (Set.mem_singleton_iff.1 hg) ▸ hF⟩,
        (isPrime_vanishingIdeal_zeroLocus_singleton_iff two_ne_zero hF hFi.squarefree).2 hFi⟩
    · exact ⟨zeroLocus_vanishingIdeal_univ, isPrime_vanishingIdeal_univ⟩

/-! ### The projective closure -/

/-- **Fulton, §4.3, Proposition 3 (6)**, for the components. Over an infinite field, let `C` be a
set of affine varieties whose union `V` is not `𝔸ⁿ`, such as an irreducible decomposition of an
algebraic set `V ⊊ 𝔸ⁿ`. Then no closure `U*`, `U ∈ C`, lies in or contains the hyperplane at
infinity; by `projectiveClosure_irreducibleDecomposition`, these are the components of `V*`. -/
theorem not_subset_and_not_superset_compl_affineOpen [Infinite k] (i : Fin (n + 1))
    {V : Set (Fin n → k)} (hne : V ≠ Set.univ) {C : Set (Set (Fin n → k))}
    (hCW : ∀ W ∈ C, MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k W) = W ∧
      (MvPolynomial.vanishingIdeal k W).IsPrime) (hCU : ⋃₀ C = V) :
    ∀ W ∈ projectiveClosure i '' C, ¬ W ⊆ (affineOpen i)ᶜ ∧ ¬ (affineOpen i)ᶜ ⊆ W := by
  rintro _ ⟨U, hU, rfl⟩
  have hUne : U.Nonempty := Set.nonempty_iff_ne_empty.2 fun h ↦
    (hCW U hU).2.ne_top (by rw [h, MvPolynomial.vanishingIdeal_empty])
  refine ⟨not_projectiveClosure_subset_compl_affineOpen hUne,
    compl_affineOpen_not_subset_projectiveClosure (hCW U hU).1 (fun h ↦ hne ?_) hUne⟩
  rw [← hCU, Set.eq_univ_iff_forall]
  exact fun a ↦ ⟨U, hU, h ▸ Set.mem_univ a⟩

/-- **Projective closure of affine algebraic sets.** Let `k` be algebraically closed, identify
`𝔸ⁿ` with `U_{n+1} ⊆ ℙⁿ` through `φ = (affineChart (Fin.last n)).symm`, and let
`H_∞ = (affineOpen (Fin.last n))ᶜ`.

* (a) For an ideal `J ⊆ k[X₁, …, Xₙ]`, `J*` (`Ideal.homogenization`, a homogeneous ideal) is
  generated by the `F*`, `F ∈ J`; a form `G` lies in `J*` iff `G_* ∈ J`; `(J*)_* = J`;
  `X_{n+1} G ∈ J*` implies `G ∈ J*`; `J` prime implies `J*` prime; `(F)* = (F*)`
  (Problem 4.19); and for the twisted cubic `J = (Y - X², Z - X³)`, `ZW - XY ∈ J*` but
  `ZW - XY ∉ ((Y - X²)*, (Z - X³)*)` (Problem 4.20).
* (b) `V* = V(I(V)*)` and `V_* = V(I(V)_*)`, which is `φ⁻¹(V)` for an algebraic `V ⊆ ℙⁿ`.
* (c) Proposition 3: (1) `φ(V) = V* ∩ U_{n+1}` and `(V*)_* = V` for algebraic `V`; (2) both
  operations are monotone; (3) `V` irreducible implies `V*` irreducible; (4) an irreducible
  decomposition of `V` gives one of `V*`; (5) `V*` is the smallest algebraic set containing
  `φ(V)`; (6) if `∅ ≠ V ⊊ 𝔸ⁿ`, no component of `V*` lies in or contains `H_∞`; (7) if `V` is a
  finite union of projective varieties none of which lies in or contains `H_∞`, then
  `V_* ⊊ 𝔸ⁿ` and `(V_*)* = V`.
* (d) `V(F)* = V(F*)`.
* (e) (Problems 4.21, 4.22) A projective variety containing a hypersurface `V(F)` is `V(F)` or
  `ℙⁿ`; one containing `H_∞` is `ℙⁿ`, with `(ℙⁿ)_* = 𝔸ⁿ`, or `H_∞`, with `(H_∞)_* = ∅`.
* (f) `V ↦ V*` and `W ↦ W_*` are inverse bijections between affine varieties (nonempty, since
  their ideal is prime) and projective varieties not contained in `H_∞`.
* (g) (Problem 4.23) The subvarieties of `ℙ¹` are its points and `ℙ¹`; those of `ℙ²` are its
  points, the curves `V(F)` with `F` an irreducible form, and `ℙ²`.

Milestone: *Projective closure of affine algebraic sets*. -/
theorem projectiveClosure_spec [IsAlgClosed k] :
    -- (a)
    (∀ J : Ideal (MvPolynomial (Fin n) k),
      (J.homogenization (Fin.last n)).toIdeal = Ideal.span
        ((fun f ↦ homogenize (Fin.last n) f.totalDegree f) '' (J : Set (MvPolynomial (Fin n) k))) ∧
      (∀ (G : MvPolynomial (Fin (n + 1)) k) (d : ℕ), G.IsHomogeneous d →
        (G ∈ J.homogenization (Fin.last n) ↔ dehomogenize (Fin.last n) G ∈ J)) ∧
      (J.homogenization (Fin.last n)).toIdeal.map (dehomogenize (Fin.last n)) = J ∧
      (∀ G : MvPolynomial (Fin (n + 1)) k, X (Fin.last n) * G ∈ J.homogenization (Fin.last n) →
        G ∈ J.homogenization (Fin.last n)) ∧
      (J.IsPrime → (J.homogenization (Fin.last n)).toIdeal.IsPrime)) ∧
    (∀ F : MvPolynomial (Fin n) k, ((Ideal.span {F}).homogenization (Fin.last n)).toIdeal =
      Ideal.span {homogenize (Fin.last n) F.totalDegree F}) ∧
    ((X 2 * X 3 - X 0 * X 1 : MvPolynomial (Fin 4) k) ∈
        (Ideal.span {X 1 - X 0 ^ 2, X 2 - X 0 ^ 3}).homogenization 3 ∧
      (X 2 * X 3 - X 0 * X 1 : MvPolynomial (Fin 4) k) ∉ Ideal.span
        {homogenize 3 (X 1 - X 0 ^ 2 : MvPolynomial (Fin 3) k).totalDegree (X 1 - X 0 ^ 2),
          homogenize 3 (X 2 - X 0 ^ 3 : MvPolynomial (Fin 3) k).totalDegree (X 2 - X 0 ^ 3)}) ∧
    -- (b)
    (∀ V : Set (Fin n → k), projectiveClosure (Fin.last n) V =
      zeroLocus ((MvPolynomial.vanishingIdeal k V).homogenization (Fin.last n) : Set _)) ∧
    (∀ W : Set (ℙ k (Fin (n + 1) → k)), zeroLocus (vanishingIdeal W) = W →
      affinePart (Fin.last n) W = MvPolynomial.zeroLocus k
        ((vanishingIdeal W).toIdeal.map (dehomogenize (Fin.last n))) ∧
      affinePart (Fin.last n) W = (affineChart (Fin.last n)).symm ⁻¹' W) ∧
    -- (c) (1)
    (∀ V : Set (Fin n → k), MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k V) = V →
      projectiveClosure (Fin.last n) V ∩ affineOpen (Fin.last n) =
        (affineChart (Fin.last n)).symm '' V ∧
      affinePart (Fin.last n) (projectiveClosure (Fin.last n) V) = V) ∧
    -- (c) (2)
    Monotone (projectiveClosure (k := k) (Fin.last n)) ∧
    Monotone (affinePart (k := k) (Fin.last n)) ∧
    -- (c) (3)
    (∀ V : Set (Fin n → k), (MvPolynomial.vanishingIdeal k V).IsPrime →
      (vanishingIdeal (projectiveClosure (Fin.last n) V)).toIdeal.IsPrime) ∧
    -- (c) (4)
    (∀ (V : Set (Fin n → k)) (C : Set (Set (Fin n → k))), C.Finite →
      (∀ W ∈ C, MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k W) = W ∧
        (MvPolynomial.vanishingIdeal k W).IsPrime) →
      ⋃₀ C = V → (∀ W ∈ C, ∀ W' ∈ C, W ⊆ W' → W = W') →
      (projectiveClosure (Fin.last n) '' C).Finite ∧
        (∀ W ∈ projectiveClosure (Fin.last n) '' C,
          zeroLocus (vanishingIdeal W : Set (MvPolynomial (Fin (n + 1)) k)) = W ∧
            (vanishingIdeal W).toIdeal.IsPrime) ∧
        ⋃₀ (projectiveClosure (Fin.last n) '' C) = projectiveClosure (Fin.last n) V ∧
        ∀ W ∈ projectiveClosure (Fin.last n) '' C, ∀ W' ∈ projectiveClosure (Fin.last n) '' C,
          W ⊆ W' → W = W') ∧
    -- (c) (5)
    (∀ V : Set (Fin n → k),
      zeroLocus (vanishingIdeal (projectiveClosure (Fin.last n) V)) =
        projectiveClosure (Fin.last n) V ∧
      ∀ W : Set (ℙ k (Fin (n + 1) → k)), zeroLocus (vanishingIdeal W) = W →
        (projectiveClosure (Fin.last n) V ⊆ W ↔ (affineChart (Fin.last n)).symm '' V ⊆ W)) ∧
    -- (c) (6)
    (∀ (V : Set (Fin n → k)) (C : Set (Set (Fin n → k))),
      MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k V) = V → V ≠ Set.univ →
      (∀ W ∈ C, MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k W) = W ∧
        (MvPolynomial.vanishingIdeal k W).IsPrime) → ⋃₀ C = V →
      ∀ W ∈ projectiveClosure (Fin.last n) '' C,
        ¬ W ⊆ (affineOpen (Fin.last n))ᶜ ∧ ¬ (affineOpen (Fin.last n))ᶜ ⊆ W) ∧
    -- (c) (7)
    (∀ C : Set (Set (ℙ k (Fin (n + 1) → k))), C.Finite →
      (∀ W ∈ C, zeroLocus (vanishingIdeal W) = W ∧ (vanishingIdeal W).toIdeal.IsPrime) →
      (∀ W ∈ C, ¬ W ⊆ (affineOpen (Fin.last n))ᶜ ∧ ¬ (affineOpen (Fin.last n))ᶜ ⊆ W) →
      affinePart (Fin.last n) (⋃₀ C) ≠ Set.univ ∧
        projectiveClosure (Fin.last n) (affinePart (Fin.last n) (⋃₀ C)) = ⋃₀ C) ∧
    -- (d)
    (∀ F : MvPolynomial (Fin n) k,
      projectiveClosure (Fin.last n) (MvPolynomial.zeroLocus k (Ideal.span {F})) =
        zeroLocus {homogenize (Fin.last n) F.totalDegree F}) ∧
    -- (e)
    (∀ (F : MvPolynomial (Fin (n + 1)) k) (d : ℕ), F.IsHomogeneous d → d ≠ 0 →
      ∀ W : Set (ℙ k (Fin (n + 1) → k)), zeroLocus (vanishingIdeal W) = W →
        (vanishingIdeal W).toIdeal.IsPrime → zeroLocus {F} ⊆ W →
        W = zeroLocus {F} ∨ W = Set.univ) ∧
    (∀ W : Set (ℙ k (Fin (n + 1) → k)), zeroLocus (vanishingIdeal W) = W →
      (vanishingIdeal W).toIdeal.IsPrime → (affineOpen (Fin.last n))ᶜ ⊆ W →
      (W = Set.univ ∧ affinePart (Fin.last n) W = Set.univ) ∨
        (W = (affineOpen (Fin.last n))ᶜ ∧ affinePart (Fin.last n) W = ∅)) ∧
    -- (f)
    (∃ e : {V : Set (Fin n → k) // MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k V) = V ∧
        (MvPolynomial.vanishingIdeal k V).IsPrime} ≃
      {W : Set (ℙ k (Fin (n + 1) → k)) // zeroLocus (vanishingIdeal W) = W ∧
        (vanishingIdeal W).toIdeal.IsPrime ∧ ¬ W ⊆ (affineOpen (Fin.last n))ᶜ},
      (∀ V, (e V : Set (ℙ k (Fin (n + 1) → k))) = projectiveClosure (Fin.last n) V) ∧
        ∀ W, (e.symm W : Set (Fin n → k)) = affinePart (Fin.last n) W) ∧
    -- (g)
    (∀ W : Set (ℙ k (Fin 2 → k)),
      (zeroLocus (vanishingIdeal W) = W ∧ (vanishingIdeal W).toIdeal.IsPrime) ↔
        (∃ P, W = {P}) ∨ W = Set.univ) ∧
    (∀ W : Set (ℙ k (Fin 3 → k)),
      (zeroLocus (vanishingIdeal W) = W ∧ (vanishingIdeal W).toIdeal.IsPrime) ↔
        (∃ P, W = {P}) ∨
          (∃ (F : MvPolynomial (Fin 3) k) (d : ℕ), F.IsHomogeneous d ∧ Irreducible F ∧
            W = zeroLocus {F}) ∨
          W = Set.univ) := by
  refine ⟨fun J ↦ ⟨Ideal.homogenization_eq_span_homogenize J _,
      fun _ _ hG ↦ Ideal.mem_homogenization_iff_of_isHomogeneous hG,
      Ideal.map_dehomogenize_homogenization, fun _ ↦ Ideal.X_mul_mem_homogenization_iff.1,
      Ideal.IsPrime.homogenization⟩,
    fun F ↦ Ideal.homogenization_span_singleton F _,
    Ideal.X_mul_X_sub_X_mul_X_mem_homogenization_and_notMem_span_homogenize,
    projectiveClosure_def _, fun W hW ↦ ⟨affinePart_def _ W, Set.ext fun _ ↦ mem_affinePart_iff hW⟩,
    fun V hV ↦ ⟨projectiveClosure_inter_affineOpen hV, affinePart_projectiveClosure hV⟩,
    projectiveClosure_mono, affinePart_mono, fun V ↦ isPrime_vanishingIdeal_projectiveClosure,
    fun V C hC hCW hCU hCi ↦ projectiveClosure_irreducibleDecomposition hC hCW hCU hCi,
    fun V ↦ ⟨projectiveClosure_zeroLocus_vanishingIdeal V,
      fun W hW ↦ projectiveClosure_subset_iff hW⟩,
    fun V C _ hne hCW hCU ↦ not_subset_and_not_superset_compl_affineOpen _ hne hCW hCU,
    fun C hC hCW hCH ↦ ⟨affinePart_sUnion_ne_univ hC hCW (fun W hW ↦ (hCH W hW).1)
      (fun W hW ↦ (hCH W hW).2), projectiveClosure_affinePart_sUnion hC hCW
      (fun W hW ↦ (hCH W hW).1)⟩,
    projectiveClosure_zeroLocus_span_singleton,
    fun F d hF hd W hW hWp h ↦ eq_zeroLocus_singleton_or_eq_univ hF hd hW hWp h,
    fun W hW hWp h ↦ ?_,
    ⟨projectiveClosureEquiv _, projectiveClosureEquiv_apply, projectiveClosureEquiv_symm_apply⟩,
    fun W ↦ isPrime_vanishingIdeal_projectiveLine_iff,
    fun W ↦ isPrime_vanishingIdeal_projectivePlane_iff⟩
  rcases eq_compl_affineOpen_or_eq_univ _ hW hWp h with rfl | rfl
  · exact .inr ⟨rfl, affinePart_compl_affineOpen⟩
  · exact .inl ⟨rfl, affinePart_univ⟩

end PlaneCurves.ProjectiveSpace

end
