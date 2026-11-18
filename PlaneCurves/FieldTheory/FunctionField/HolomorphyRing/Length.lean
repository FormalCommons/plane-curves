/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.FieldTheory.FunctionField.Place.AddValuation
public import TauCeti.FieldTheory.FunctionField.HolomorphyRing.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Approximation
public import TauCeti.RingTheory.OrderOfVanishing

/-!
# Lengths of quotients of a holomorphy ring

Let `S` be a finite set of places of a field extension `F/k` and `𝒪_S` its holomorphy ring, the
functions regular at every place of `S`. For a nonzero `g ∈ 𝒪_S`, the length of `𝒪_S ⧸ (g)` over
`𝒪_S` is the sum of the orders of `g` at the places of `S`:
`ℓ(𝒪_S ⧸ (g)) = ∑_{Q ∈ S} ord_Q g`.

Since `𝒪_S` is a principal ideal domain (Tau Ceti's `TauCeti.isPrincipalIdealRing_holomorphyRing`)
whose units and associates are read off from the orders along `S`, `g` is associated to a product
`∏_{Q ∈ S} t_Q ^ ord_Q g`, where `t_Q` has order `1` at `Q` and `0` at the other places of `S`
(weak approximation). Each `t_Q` is irreducible, so `𝒪_S ⧸ (t_Q)` has length one, and the length
is additive along products of nonzero elements. No hypothesis on residue fields is needed, as
the length is taken over `𝒪_S`.

## Main results

* `TauCeti.isUnit_holomorphyRing_iff`: a nonzero `z ∈ 𝒪_S` is a unit exactly when it has order
  `0` at every place of `S`.
* `TauCeti.associated_holomorphyRing_iff`: two nonzero elements of `𝒪_S` are associated exactly
  when they have the same orders along `S`.
* `TauCeti.exists_holomorphyRing_forall_ord_eq`: for a finite `S`, any nonnegative orders along
  `S` are those of some nonzero element of `𝒪_S`.
* `TauCeti.irreducible_holomorphyRing_of_ord_eq`: an element of `𝒪_S` with order `1` at one place
  of `S` and `0` at the others is irreducible.
* `TauCeti.length_quotient_span_singleton_holomorphyRing`:
  `ℓ(𝒪_S ⧸ (g)) = ∑_{Q ∈ S} ord_Q g` for `g ≠ 0`, in `ℕ∞`.
* `TauCeti.map_natCast_length_quotient_span_singleton_holomorphyRing`: the same, with the orders
  read as the additive valuations `TauCeti.Place.addValuation` in `WithTop ℤ`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.5, Proposition 2
* [H. Stichtenoth, *Algebraic Function Fields and Codes*][Stichtenoth2009], §3.2
-/

public section

namespace TauCeti

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

section Set

variable {S : Set (Place k F)}

/-- A nonzero element of the holomorphy ring `𝒪_S` is a unit exactly when it has order `0` at
every place of `S`. -/
theorem isUnit_holomorphyRing_iff {z : ↥(holomorphyRing S)} (hz : (z : F) ≠ 0) :
    IsUnit z ↔ ∀ P ∈ S, P.ord (z : F) = 0 := by
  rw [isUnit_iff_dvd_one, dvd_holomorphyRing_iff_forall_ord_le hz (by simp)]
  refine forall₂_congr fun P hP ↦ ?_
  have := ord_nonneg_of_mem_holomorphyRing hP z
  simp only [OneMemClass.coe_one, Place.ord_one]
  omega

/-- Two nonzero elements of the holomorphy ring `𝒪_S` are associated exactly when they have the
same order at every place of `S`. -/
theorem associated_holomorphyRing_iff {y z : ↥(holomorphyRing S)} (hy : (y : F) ≠ 0)
    (hz : (z : F) ≠ 0) : Associated y z ↔ ∀ P ∈ S, P.ord (y : F) = P.ord (z : F) := by
  rw [← dvd_dvd_iff_associated, dvd_holomorphyRing_iff_forall_ord_le hy hz,
    dvd_holomorphyRing_iff_forall_ord_le hz hy]
  exact ⟨fun h P hP ↦ le_antisymm (h.1 P hP) (h.2 P hP),
    fun h ↦ ⟨fun P hP ↦ (h P hP).le, fun P hP ↦ (h P hP).ge⟩⟩

/-- An element of the holomorphy ring `𝒪_S` with order `1` at a place `Q` of `S` and order `0` at
the other places of `S` is irreducible. -/
theorem irreducible_holomorphyRing_of_ord_eq {t : ↥(holomorphyRing S)} {Q : Place k F}
    (hQ : Q ∈ S) (ht : (t : F) ≠ 0) (htQ : Q.ord (t : F) = 1)
    (htP : ∀ P ∈ S, P ≠ Q → P.ord (t : F) = 0) : Irreducible t := by
  refine ⟨fun hu ↦ by simp [(isUnit_holomorphyRing_iff ht).mp hu Q hQ] at htQ, ?_⟩
  rintro a b rfl
  have ha : (a : F) ≠ 0 := fun h ↦ ht (by simp [h])
  have hb : (b : F) ≠ 0 := fun h ↦ ht (by simp [h])
  have hord : ∀ P ∈ S, P.ord (a : F) + P.ord (b : F) = P.ord ((a * b : ↥(holomorphyRing S)) : F) :=
    fun P _ ↦ by rw [Subalgebra.coe_mul, P.ord_mul ha hb]
  have hPa : ∀ P ∈ S, P ≠ Q → P.ord (a : F) = 0 := fun P hP hPQ ↦ by
    have := hord P hP; have := htP P hP hPQ
    have := ord_nonneg_of_mem_holomorphyRing hP a; have := ord_nonneg_of_mem_holomorphyRing hP b
    omega
  have hPb : ∀ P ∈ S, P ≠ Q → P.ord (b : F) = 0 := fun P hP hPQ ↦ by
    have := hord P hP; have := htP P hP hPQ
    have := ord_nonneg_of_mem_holomorphyRing hP a; have := ord_nonneg_of_mem_holomorphyRing hP b
    omega
  rw [isUnit_holomorphyRing_iff ha, isUnit_holomorphyRing_iff hb]
  have := hord Q hQ
  have := ord_nonneg_of_mem_holomorphyRing hQ a; have := ord_nonneg_of_mem_holomorphyRing hQ b
  rcases (show Q.ord (a : F) = 0 ∨ Q.ord (b : F) = 0 by omega) with h | h
  · refine .inl fun P hP ↦ ?_
    by_cases hPQ : P = Q
    · exact hPQ ▸ h
    · exact hPa P hP hPQ
  · refine .inr fun P hP ↦ ?_
    by_cases hPQ : P = Q
    · exact hPQ ▸ h
    · exact hPb P hP hPQ

end Set

variable {S : Finset (Place k F)}

/-- For a finite set `S` of places, any nonnegative orders along `S` are the orders of some
nonzero element of the holomorphy ring `𝒪_S` (weak approximation). -/
theorem exists_holomorphyRing_forall_ord_eq (r : Place k F → ℕ) :
    ∃ t : ↥(holomorphyRing (S : Set (Place k F))), (t : F) ≠ 0 ∧ ∀ P ∈ S, P.ord (t : F) = r P := by
  obtain ⟨t, ht0, ht⟩ := Place.exists_ne_zero_forall_mem_ord_eq S fun P ↦ r P
  exact ⟨⟨t, mem_holomorphyRing_iff_forall_ord_nonneg.mpr fun P hP ↦ by
    simp [ht P (Finset.mem_coe.mp hP)]⟩, ht0, ht⟩

/-- **The length of `𝒪_S ⧸ (g)` is the sum of the orders of `g` along `S`.** For a finite set `S`
of places of `F/k` and a nonzero `g` in the holomorphy ring `𝒪_S`,
`ℓ(𝒪_S ⧸ (g)) = ∑_{Q ∈ S} ord_Q g`, the length being over `𝒪_S`. -/
theorem length_quotient_span_singleton_holomorphyRing
    {g : ↥(holomorphyRing (S : Set (Place k F)))} (hg : g ≠ 0) :
    Module.length (holomorphyRing (S : Set (Place k F)))
        (holomorphyRing (S : Set (Place k F)) ⧸ Ideal.span {g}) =
      ∑ Q ∈ S, ((Q.ord (g : F)).toNat : ℕ∞) := by
  classical
  have := isPrincipalIdealRing_holomorphyRing S.finite_toSet
  have hg' : (g : F) ≠ 0 := by simpa using hg
  choose t ht0 ht using fun Q : Place k F ↦
    exists_holomorphyRing_forall_ord_eq (S := S) fun P ↦ if P = Q then 1 else 0
  have ht0' : ∀ Q, t Q ≠ 0 := fun Q h ↦ ht0 Q (by simp [h])
  set n : Place k F → ℕ := fun Q ↦ (Q.ord (g : F)).toNat
  have hassoc : Associated (∏ Q ∈ S, t Q ^ n Q) g := by
    have hprod : ((∏ Q ∈ S, t Q ^ n Q : ↥(holomorphyRing (S : Set (Place k F)))) : F) =
        ∏ Q ∈ S, (t Q : F) ^ n Q := by
      simp
    refine (associated_holomorphyRing_iff ?_ hg').mpr fun P hP ↦ ?_
    · rw [hprod]
      exact Finset.prod_ne_zero_iff.mpr fun Q _ ↦ pow_ne_zero _ (ht0 Q)
    have hP' : P ∈ S := Finset.mem_coe.mp hP
    rw [hprod, P.ord_prod S fun Q _ ↦ pow_ne_zero _ (ht0 Q)]
    simp only [Place.ord_pow, ht _ _ hP', Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, hP', ite_true, n]
    exact Int.toNat_of_nonneg (ord_nonneg_of_mem_holomorphyRing hP g)
  rw [← Ring.ord, ← Ring.ord_eq_of_associated hassoc,
    Ring.ord_prod fun Q _ ↦ pow_mem (mem_nonZeroDivisors_of_ne_zero (ht0' Q)) _]
  refine Finset.sum_congr rfl fun Q hQ ↦ ?_
  rw [Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero (ht0' Q)),
    Ring.ord_of_irreducible (irreducible_holomorphyRing_of_ord_eq (Finset.mem_coe.mpr hQ)
      (ht0 Q) (by simpa using ht Q Q hQ) fun P hP hPQ ↦ by simpa [hPQ] using ht Q P hP),
    nsmul_one]

/-- `ℓ(𝒪_S ⧸ (g)) = ∑_{Q ∈ S} ord_Q g` for a nonzero `g` in the holomorphy ring of a finite set
`S` of places, with the orders read as the additive valuations `TauCeti.Place.addValuation` in
`WithTop ℤ` and the length cast from `ℕ∞`. -/
theorem map_natCast_length_quotient_span_singleton_holomorphyRing
    {g : ↥(holomorphyRing (S : Set (Place k F)))} (hg : g ≠ 0) :
    (Module.length (holomorphyRing (S : Set (Place k F)))
        (holomorphyRing (S : Set (Place k F)) ⧸ Ideal.span {g})).map (Nat.cast : ℕ → ℤ) =
      ∑ Q ∈ S, Q.addValuation (g : F) := by
  have hg' : (g : F) ≠ 0 := by simpa using hg
  rw [length_quotient_span_singleton_holomorphyRing hg, ← Nat.cast_sum, ENat.map_natCast]
  simp only [Place.addValuation_of_ne_zero _ hg', Nat.cast_sum, ← WithTop.coe_sum]
  refine congrArg _ (Finset.sum_congr rfl fun Q hQ ↦ ?_)
  exact Int.toNat_of_nonneg (ord_nonneg_of_mem_holomorphyRing (Finset.mem_coe.mpr hQ) g)

end TauCeti

end
