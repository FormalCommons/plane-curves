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
public import TauCeti.RingTheory.Length.Endomorphism
public import PlaneCurves.RingTheory.Length
public import PlaneCurves.RingTheory.LocalRing.Length

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
* `TauCeti.length_quotient_span_singleton_integralClosure`: for a local `k`-algebra `A` with
  residue field `k` (`k` algebraically closed) whose integral closure `Ã` in `F` is `𝒪_S` and
  finite over `A`, `ℓ_A(Ã ⧸ (z)) = ∑_{Q ∈ S} ord_Q z` for `z ≠ 0`.
* `TauCeti.ord_eq_sum_ord_of_integralClosure_eq_holomorphyRing`: if moreover `A ⊆ F` has a
  nonzero conductor element, then `ℓ_A(A ⧸ (g)) = ∑_{Q ∈ S} ord_Q g` for `g ≠ 0`, and
  `TauCeti.map_natCast_ord_eq_sum_addValuation_of_integralClosure_eq_holomorphyRing`, the same in
  `WithTop ℤ`. This is the general form of Fulton's Proposition 2 of §7.5.

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

/-! ### Lengths over a local ring whose integral closure is a holomorphy ring -/

section LocalRing

variable [IsAlgClosed k] {A : Type*} [CommRing A] [IsLocalRing A] [Algebra k A] [Algebra A F]
  [IsScalarTower k A F]

/-- Let `k` be algebraically closed and `A ⊆ F` a local `k`-algebra with residue field `k` whose
integral closure `Ã` in `F` is the holomorphy ring `𝒪_S` of a finite set `S` of places and is
module-finite over `A`. Then for every nonzero `z ∈ Ã`, the length of `Ã ⧸ zÃ` over `A` is the sum
of the orders of `z` at the places of `S`: lengths of `Ã`-modules over `A` and over `Ã` agree, the
residue fields of `Ã` being `k`. -/
theorem length_quotient_span_singleton_integralClosure
    (hS : (integralClosure A F).toSubring = (holomorphyRing (S : Set (Place k F))).toSubring)
    [Module.Finite A (integralClosure A F)]
    (hres : Function.Surjective (algebraMap k (IsLocalRing.ResidueField A)))
    {z : integralClosure A F} (hz : z ≠ 0) :
    Module.length A (integralClosure A F ⧸ Ideal.span {z}) =
      ∑ Q ∈ S, ((Q.ord (z : F)).toNat : ℕ∞) := by
  let e : integralClosure A F ≃+* holomorphyRing (S : Set (Place k F)) := RingEquiv.subringCongr hS
  rw [Module.length_restrictScalars_of_forall_isMaximal fun (m : Ideal (integralClosure A F)) _ ↦
      IsLocalRing.length_quotient_isMaximal_of_finite hres m, ← Ring.ord,
    ← Ring.ord_ringEquiv e, Ring.ord,
    length_quotient_span_singleton_holomorphyRing (by simpa using hz)]
  rfl

/-- **`ℓ(A ⧸ (g)) = ∑_Q ord_Q g`.** Let `k` be algebraically closed, `F/k` a field extension, and
`A` a local `k`-algebra with residue field `k` and an injection `A → F`, whose integral closure
`Ã` in `F` is the holomorphy ring `𝒪_S` of a finite set `S` of places, module-finite over `A`,
with a nonzero conductor element `t` (`t Ã ⊆ A`). Then for every nonzero `g ∈ A`, the length of
`A ⧸ (g)` is the sum of the orders of `g` at the places of `S`.

This is Fulton's Proposition 2 of §7.5 for the local ring `A = 𝒪_P(C)` of a curve at a point `P`,
where `S` is the set of places centred at `P`. The index lemma
(`TauCeti.length_quotient_range_restrict`) gives `ℓ_A(A ⧸ gA) = ℓ_A(Ã ⧸ gÃ)`, as `Ã ⧸ A` is a
quotient of `Ã ⧸ tÃ`, of finite length, and
`ℓ_A(Ã ⧸ gÃ) = ∑_Q ord_Q g` (`TauCeti.length_quotient_span_singleton_integralClosure`). -/
theorem ord_eq_sum_ord_of_integralClosure_eq_holomorphyRing
    (hinj : Function.Injective (algebraMap A F))
    (hS : (integralClosure A F).toSubring = (holomorphyRing (S : Set (Place k F))).toSubring)
    [Module.Finite A (integralClosure A F)]
    (hres : Function.Surjective (algebraMap k (IsLocalRing.ResidueField A))) {t : A} (ht0 : t ≠ 0)
    (ht : ∀ z ∈ integralClosure A F, algebraMap A F t * z ∈ (algebraMap A F).range)
    {g : A} (hg : g ≠ 0) :
    Ring.ord A g = ∑ Q ∈ S, ((Q.ord (algebraMap A F g)).toNat : ℕ∞) := by
  set B := integralClosure A F
  have hB : ∀ z : B, z ≠ 0 → Module.length A (B ⧸ Ideal.span {z}) =
      ∑ Q ∈ S, ((Q.ord (z : F)).toNat : ℕ∞) := fun z hz ↦
    length_quotient_span_singleton_integralClosure hS hres hz
  have hcoe : ∀ a : A, ((algebraMap A B a : B) : F) = algebraMap A F a := fun _ ↦ rfl
  have hne : ∀ {a : A}, a ≠ 0 → algebraMap A B a ≠ 0 := fun {a} ha h ↦
    ha (hinj (by rw [← hcoe, h, map_zero, ZeroMemClass.coe_zero]))
  let ι := Algebra.linearMap A B
  have hι : Function.Injective ι := fun a b h ↦ hinj (by
    rw [← hcoe, ← hcoe]; exact congrArg Subtype.val h)
  let φ := LinearMap.lsmul A B g
  have hφ : Function.Injective φ := fun y z h ↦ by
    have h' : algebraMap A B g * y = algebraMap A B g * z := by
      simpa [φ, Algebra.smul_def] using h
    exact mul_left_cancel₀ (hne hg) h'
  let N := LinearMap.range ι
  have hφN : ∀ x ∈ N, φ x ∈ N := by
    rintro _ ⟨a, rfl⟩
    exact ⟨g * a, by simp [φ, ι, Algebra.smul_def]⟩
  -- `B ⧸ A` has finite length, being a quotient of `B ⧸ tB`
  have hN : IsFiniteLength A (B ⧸ N) := by
    have hle : (Ideal.span {algebraMap A B t}).restrictScalars A ≤ N := by
      intro x hx
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      obtain ⟨a, ha⟩ := ht y y.2
      exact ⟨a, Subtype.ext (by rw [mul_comm]; exact ha)⟩
    rw [← Module.length_ne_top_iff]
    refine ne_top_of_le_ne_top ?_ (Module.length_le_of_surjective
      ((Submodule.factor hle).comp
        (Submodule.Quotient.restrictScalarsEquiv A
          (Ideal.span {algebraMap A B t})).symm.toLinearMap)
      ((Submodule.factor_surjective hle).comp (LinearEquiv.surjective _)))
    rw [hB _ (hne ht0)]
    exact WithTop.sum_ne_top.mpr fun _ _ ↦ ENat.natCast_ne_top _
  have key := length_quotient_range_restrict hφ hφN hN
  have hr : LinearMap.range (φ.restrict hφN) =
      Submodule.comap N.subtype (Submodule.map ι (Ideal.span {g})) := by
    ext ⟨x, hx⟩
    simp only [LinearMap.mem_range, Submodule.mem_comap, Submodule.mem_map,
      Submodule.subtype_apply, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨⟨_, a, rfl⟩, h⟩
      refine ⟨a * g, ⟨a, rfl⟩, ?_⟩
      have := congrArg Subtype.val h
      simp only [LinearMap.restrict_apply, φ, ι, LinearMap.lsmul_apply] at this
      rw [← this]
      simp [ι, Algebra.smul_def, mul_comm]
    · rintro ⟨_, ⟨a, rfl⟩, h⟩
      refine ⟨⟨ι a, a, rfl⟩, Subtype.ext ?_⟩
      simp only [LinearMap.restrict_apply, φ, ι, LinearMap.lsmul_apply]
      rw [← h]
      simp [ι, Algebra.smul_def, mul_comm]
  have hrφ : LinearMap.range φ = (Ideal.span {algebraMap A B g}).restrictScalars A := by
    ext x
    simp only [LinearMap.mem_range, Submodule.restrictScalars_mem, Ideal.mem_span_singleton',
      φ, LinearMap.lsmul_apply, Algebra.smul_def, mul_comm]
  rw [Ring.ord, ← length_quotient_comap_subtype_range_map hι, ← hr, key, hrφ,
    (Submodule.Quotient.restrictScalarsEquiv A _).length_eq, hB _ (hne hg)]
  rfl


/-- `ℓ(A ⧸ (g)) = ∑_Q ord_Q g` (`TauCeti.ord_eq_sum_ord_of_integralClosure_eq_holomorphyRing`),
with the orders read as the additive valuations `TauCeti.Place.addValuation` in `WithTop ℤ` and
the length cast from `ℕ∞`. -/
theorem map_natCast_ord_eq_sum_addValuation_of_integralClosure_eq_holomorphyRing
    (hinj : Function.Injective (algebraMap A F))
    (hS : (integralClosure A F).toSubring = (holomorphyRing (S : Set (Place k F))).toSubring)
    [Module.Finite A (integralClosure A F)]
    (hres : Function.Surjective (algebraMap k (IsLocalRing.ResidueField A))) {t : A} (ht0 : t ≠ 0)
    (ht : ∀ z ∈ integralClosure A F, algebraMap A F t * z ∈ (algebraMap A F).range)
    {g : A} (hg : g ≠ 0) :
    (Ring.ord A g).map (Nat.cast : ℕ → ℤ) = ∑ Q ∈ S, Q.addValuation (algebraMap A F g) := by
  have hg' : algebraMap A F g ≠ 0 := fun h ↦ hg (hinj (by rw [h, map_zero]))
  rw [ord_eq_sum_ord_of_integralClosure_eq_holomorphyRing hinj hS hres ht0 ht hg,
    ← Nat.cast_sum, ENat.map_natCast]
  simp only [Place.addValuation_of_ne_zero _ hg', Nat.cast_sum, ← WithTop.coe_sum]
  refine congrArg _ (Finset.sum_congr rfl fun Q hQ ↦ Int.toNat_of_nonneg ?_)
  have hz : algebraMap A F g ∈ holomorphyRing (S : Set (Place k F)) := by
    have : algebraMap A F g ∈ (integralClosure A F).toSubring :=
      (integralClosure A F).algebraMap_mem g
    rw [hS] at this
    exact this
  exact ord_nonneg_of_mem_holomorphyRing (Finset.mem_coe.mpr hQ) ⟨_, hz⟩

end LocalRing

end TauCeti

end
