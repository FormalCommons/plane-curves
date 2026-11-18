/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Spectrum.Maximal.Localization

/-!
# Regular functions on a set of maximal ideals

Let `R` be a domain with fraction field `K`. For a set `U` of maximal ideals of `R`, the ring of
regular functions on `U` is the intersection, inside `K`, of the localizations `R_m` for
`m ∈ U`. When `R` is the coordinate ring of an affine variety `V` and `U` a set of points of `V`,
this is Fulton's `Γ(U) = ⋂_{P ∈ U} 𝒪_P(V)`.

* `PlaneCurves.regularFunctionsOn R K U`: the subalgebra `⋂_{m ∈ U} R_m` of `K`.
* `PlaneCurves.mem_regularFunctionsOn_iff`: `z` is regular on `U` if at each `m ∈ U` it is a
  fraction `a / s` with `s ∉ m`.
* `PlaneCurves.regularFunctionsOn_univ`: the functions regular everywhere are those of `R`.
* `PlaneCurves.antitone_regularFunctionsOn`: shrinking `U` enlarges the ring.
* `PlaneCurves.regularFunctionsOn_basicOpen`: for a Jacobson domain `R` and `f ≠ 0`, the
  functions regular on the principal open set `{m | f ∉ m}` form `R[1/f]`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §6.3, Proposition 5
-/

public section

namespace PlaneCurves

variable (R : Type*) [CommRing R] [IsDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- The ring of regular functions on a set `U` of maximal ideals of a domain `R`: the
intersection, inside the fraction field `K`, of the localizations `R_m` for `m ∈ U`. -/
noncomputable def regularFunctionsOn (U : Set (MaximalSpectrum R)) : Subalgebra R K :=
  ⨅ m ∈ U, Localization.subalgebra.ofField K _ m.asIdeal.primeCompl_le_nonZeroDivisors

theorem regularFunctionsOn_def (U : Set (MaximalSpectrum R)) :
    regularFunctionsOn R K U =
      ⨅ m ∈ U, Localization.subalgebra.ofField K _ m.asIdeal.primeCompl_le_nonZeroDivisors :=
  (rfl)

variable {R K}

/-- An element of `K` is regular on `U` if and only if at each `m ∈ U` it is a fraction whose
denominator is not in `m`. -/
theorem mem_regularFunctionsOn_iff {U : Set (MaximalSpectrum R)} {z : K} :
    z ∈ regularFunctionsOn R K U ↔
      ∀ m ∈ U, ∃ a s : R, s ∉ m.asIdeal ∧ z = algebraMap R K a * (algebraMap R K s)⁻¹ := by
  simp only [regularFunctionsOn_def, Algebra.mem_iInf]
  exact forall₂_congr fun m _ ↦ ⟨fun ⟨a, s, hs, h⟩ ↦ ⟨a, s, hs, h⟩,
    fun ⟨a, s, hs, h⟩ ↦ ⟨a, s, hs, h⟩⟩

/-- The ring of regular functions is antitone in the set of maximal ideals. -/
theorem antitone_regularFunctionsOn : Antitone (regularFunctionsOn R K) := fun _ _ h ↦
  biInf_mono h

theorem regularFunctionsOn_anti {U V : Set (MaximalSpectrum R)} (h : U ⊆ V) :
    regularFunctionsOn R K V ≤ regularFunctionsOn R K U :=
  antitone_regularFunctionsOn h

@[simp]
theorem regularFunctionsOn_empty : regularFunctionsOn R K ∅ = ⊤ := by
  simp [regularFunctionsOn_def]

variable (R K) in
/-- The functions regular at every maximal ideal of a domain `R` are the elements of `R`. -/
@[simp]
theorem regularFunctionsOn_univ : regularFunctionsOn R K Set.univ = ⊥ := by
  simpa [regularFunctionsOn_def] using MaximalSpectrum.iInf_localization_eq_bot R K

/-- Every element of `R` is regular on every set of maximal ideals. -/
theorem algebraMap_mem_regularFunctionsOn (U : Set (MaximalSpectrum R)) (a : R) :
    algebraMap R K a ∈ regularFunctionsOn R K U :=
  regularFunctionsOn_anti (Set.subset_univ U) <| by
    rw [regularFunctionsOn_univ]
    exact Subalgebra.algebraMap_mem _ a

/-- Let `R` be a Jacobson domain with fraction field `K` (for instance a finitely generated
algebra over a field, by `isJacobsonRing_of_finiteType`), and `f ≠ 0` in `R`. The functions
regular at every maximal ideal not containing `f` (the principal open set `V_f`) are the
fractions `a / f ^ n`, that is, `Γ(V_f) = R[1/f]` inside `K`.

Milestone: *Regular functions on a principal open subset of an affine variety*. -/
theorem regularFunctionsOn_basicOpen [IsJacobsonRing R] {f : R} (hf : f ≠ 0) :
    regularFunctionsOn R K {m | f ∉ m.asIdeal} =
      Localization.subalgebra.ofField K _ (powers_le_nonZeroDivisors_of_noZeroDivisors hf) := by
  set A := Localization.subalgebra.ofField K _ (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  refine le_antisymm (fun z hz ↦ ?_) (fun z ⟨a, s, hs, h⟩ ↦ ?_)
  · have : IsJacobsonRing A := isJacobsonRing_localization f
    have hz' : z ∈ (⊥ : Subalgebra A K) := by
      rw [← MaximalSpectrum.iInf_localization_eq_bot A K, Algebra.mem_iInf]
      intro n
      have hn := (IsLocalization.isMaximal_iff_isMaximal_disjoint A f n.asIdeal).1 n.isMaximal
      obtain ⟨a, s, hs, rfl⟩ := mem_regularFunctionsOn_iff.1 hz ⟨_, hn.1⟩ hn.2
      exact ⟨algebraMap R A a, algebraMap R A s, hs, by simp [← IsScalarTower.algebraMap_apply]⟩
    obtain ⟨y, rfl⟩ := Algebra.mem_bot.1 hz'
    exact y.2
  · obtain ⟨n, rfl⟩ := hs
    refine mem_regularFunctionsOn_iff.2 fun m hm ↦ ⟨a, f ^ n, ?_, h⟩
    exact fun h ↦ hm (m.isMaximal.isPrime.mem_of_pow_mem n h)

end PlaneCurves

end
