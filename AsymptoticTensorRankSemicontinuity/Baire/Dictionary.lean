/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The ring ↔ point-set dictionary (Kraft AI.4.1–AI.4.3)

This file bridges Kraft's commutative-algebra language (ideals / primes /
integral extensions) and the **point-set** language `X ⊆ (Fin n → ℂ)` used by
`BaireProperty.lean`, working purely against Mathlib's
`MvPolynomial.zeroLocus` / `MvPolynomial.vanishingIdeal` over `ℂ`.

This file works directly with `(Fin n → ℂ)` point-sets and Mathlib's
`MvPolynomial.zeroLocus` / `MvPolynomial.vanishingIdeal` API.

## Source

* **Kraft AI.4.1** (kraft tex:7142–7150): a finite morphism `φ : Z → W`
  (`𝒪(Z)` a finite `𝒪(W)`-module) is *closed*; surjectivity onto the image is
  lying-over for maximal ideals (`[AM] Theorem 5.10`).
* **Kraft AI.4.2** (kraft tex:7151–7165): Noether normalization — an
  irreducible variety `Z` of dimension `n` admits a finite surjective
  `φ : Z → ℂⁿ`; algebraically, a f.g. domain `A/k` is a finite module over a
  polynomial subring `k[a₁,…,aₙ]`.
* **Kraft AI.4.3** (kraft tex:7166–7219): integral / normal extensions; "finite
  ⟺ integral" for dominant morphisms of irreducible varieties.

## Dictionary lemmas (plan D1–D3)

* `D1` — for an irreducible closed point-set `X = zeroLocus ℂ I` with `I` prime,
  `vanishingIdeal X = I` (Nullstellensatz prime ⟹ radical bookkeeping). Hence
  the coordinate ring `MvPolynomial (Fin n) ℂ ⧸ vanishingIdeal X` is a domain.
* `D2` — points of `X` ↔ `ℂ`-points of `zeroLocus`, i.e. evaluation homs; the
  weak Nullstellensatz packages this (`eq_vanishingIdeal_singleton_of_isMaximal`).
* `D3` — an injective integral `ℂ`-algebra map `MvPolynomial (Fin d) ℂ →ₐ S`
  induces a finite **surjective** map of point-sets via lying-over
  (`Ideal.exists_ideal_over_maximal_of_isIntegral`), the geometric form of
  Kraft AI.4.1.
-/

universe u

namespace Semicontinuity.Baire

open MvPolynomial

variable {n : ℕ}

/-! ## D1 — irreducible point-set ↔ prime vanishing ideal -/

/-- **D1** (Kraft AI.4.3, kraft tex:7166–7219; Nullstellensatz bookkeeping).
For a **prime** ideal `I` of `MvPolynomial (Fin n) ℂ`, the vanishing ideal of
its zero locus is `I` itself. This is the geometric ⟹ algebraic half of the
dictionary: the closed point-set `zeroLocus ℂ I` "remembers" the prime `I`.

Direct consequence of `MvPolynomial.IsPrime.vanishingIdeal_zeroLocus`
(Nullstellensatz: `vanishingIdeal (zeroLocus I) = radical I = I` for `I` prime,
over the algebraically closed field `ℂ`). -/
theorem vanishingIdeal_zeroLocus_of_isPrime
    (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime] :
    vanishingIdeal ℂ (zeroLocus ℂ I) = I :=
  MvPolynomial.IsPrime.vanishingIdeal_zeroLocus I

/-- The **coordinate ring** of a point-set `X ⊆ (Fin n → ℂ)`:
`MvPolynomial (Fin n) ℂ ⧸ vanishingIdeal X`. (Kraft `𝒪(X)`, AI.4.1
notation `θ(Z)`.) -/
abbrev coordRing (X : Set (Fin n → ℂ)) : Type :=
  MvPolynomial (Fin n) ℂ ⧸ vanishingIdeal ℂ X

/-- **D1 corollary**: for an irreducible closed point-set `X = zeroLocus ℂ I`
with `I` prime, the coordinate ring `coordRing X` is an integral domain
(`vanishingIdeal X = I` is prime, so the quotient is a domain). -/
theorem isDomain_coordRing_zeroLocus
    (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime] :
    IsDomain (coordRing (zeroLocus ℂ I)) := by
  have h : vanishingIdeal ℂ (zeroLocus ℂ I) = I :=
    vanishingIdeal_zeroLocus_of_isPrime I
  change IsDomain (MvPolynomial (Fin n) ℂ ⧸ vanishingIdeal ℂ (zeroLocus ℂ I))
  rw [h]
  infer_instance

/-! ## D2 — points ↔ evaluation homs / maximal ideals -/

/-- **D2** (weak Nullstellensatz, kraft AI.4.1 `[AM] Theorem 5.10`,
Mathlib `eq_vanishingIdeal_singleton_of_isMaximal`).

Every maximal ideal of `MvPolynomial (Fin n) ℂ` is the vanishing ideal of a
single point `x ∈ (Fin n → ℂ)`. This is the surjectivity of `point ↦ maximal
ideal`: each `ℂ`-point gives a maximal ideal (`vanishingIdeal {x}`), and over
the algebraically closed `ℂ` every maximal ideal arises this way. -/
theorem exists_point_of_isMaximal
    {m : Ideal (MvPolynomial (Fin n) ℂ)} (hm : m.IsMaximal) :
    ∃ x : Fin n → ℂ, m = vanishingIdeal ℂ {x} :=
  eq_vanishingIdeal_singleton_of_isMaximal ℂ hm

/-- `vanishingIdeal ℂ {x}` is maximal: it is the kernel of the (surjective)
evaluation `ℂ`-algebra hom `aeval x`, whose codomain is the field `ℂ`. -/
instance isMaximal_vanishingIdeal_singleton (x : Fin n → ℂ) :
    (vanishingIdeal ℂ ({x} : Set (Fin n → ℂ))).IsMaximal := by
  have hker : vanishingIdeal ℂ ({x} : Set (Fin n → ℂ))
      = RingHom.ker (aeval x : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ).toRingHom := by
    ext p
    rw [mem_vanishingIdeal_iff]
    simp [RingHom.mem_ker, Set.mem_singleton_iff]
  rw [hker]
  have hsurj : Function.Surjective (aeval x : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) :=
    fun c => ⟨MvPolynomial.C c, by simp⟩
  exact RingHom.ker_isMaximal_of_surjective _ hsurj

/-- A point `x ∈ zeroLocus ℂ I` exactly when `I ≤ vanishingIdeal {x}`
(equivalently every `p ∈ I` vanishes at `x`). The membership ↔ ideal-inclusion
half of D2. -/
theorem mem_zeroLocus_iff_le_vanishingIdeal_singleton
    (I : Ideal (MvPolynomial (Fin n) ℂ)) (x : Fin n → ℂ) :
    x ∈ zeroLocus ℂ I ↔ I ≤ vanishingIdeal ℂ {x} := by
  rw [mem_zeroLocus_iff]
  constructor
  · intro h p hp
    rw [mem_vanishingIdeal_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    exact hy ▸ h p hp
  · intro h p hp
    have := h hp
    rw [mem_vanishingIdeal_iff] at this
    exact this x rfl

/-! ## D3 — finite injective algebra map ⟹ finite surjective map of point-sets

This is the geometric form of Kraft AI.4.1 (kraft tex:7147–7150): a finite
(here: integral) inclusion of coordinate rings gives a *closed surjective*
map of point-sets, surjective by lying-over for maximal ideals
(`[AM] Theorem 5.10`).

We only need the **ideal-level** content consumed by the going-down argument, so
D3 is stated as lying-over surjectivity for the comap map on ideals, plus the
concrete continuous polynomial realisation of the map on points. -/

/-- **D3 (lying-over / surjectivity)** (Kraft AI.4.1, kraft tex:7147–7150;
Mathlib `Ideal.exists_ideal_over_maximal_of_isIntegral`).

If `S` is integral and faithful over `R`, then every maximal ideal of `R` is the
contraction `comap (algebraMap R S)` of a maximal ideal of `S`. Geometrically:
the induced map of `ℂ`-point-sets `MaxSpec S → MaxSpec R` is **surjective**. -/
theorem exists_maximal_over_of_isIntegral
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [FaithfulSMul R S]
    (m : Ideal R) [m.IsMaximal] :
    ∃ M : Ideal S, M.IsMaximal ∧ M.comap (algebraMap R S) = m := by
  apply Ideal.exists_ideal_over_maximal_of_isIntegral m
  have hker : RingHom.ker (algebraMap R S) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective R S)
  rw [hker]
  exact bot_le

/-- **D3 (nonzero-ideal contraction)** (plan L1.2 input, Kraft AI.4.2 norm
argument kraft tex:6857; Mathlib `Ideal.comap_ne_bot_of_integral_mem`).

If `S` is an integral extension of a domain `R` (with `R` nontrivial) and
`I ⊆ S` is a nonzero ideal, then its contraction to `R` is nonzero: pick a
nonzero `b ∈ I`; its minimal integral equation has a nonzero constant term lying
in `I ∩ R`. This is the algebraic heart of "a curve in `X` dominates the
base line" used in Kraft AI.4.5's good-base-point step. -/
theorem comap_ne_bot_of_isIntegral
    {R S : Type*} [CommRing R] [CommRing S] [Nontrivial R] [IsDomain S]
    [Algebra R S] [Algebra.IsIntegral R S]
    {I : Ideal S} (hI : I ≠ ⊥) :
    I.comap (algebraMap R S) ≠ ⊥ := by
  obtain ⟨b, hbI, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  exact Ideal.comap_ne_bot_of_integral_mem hb0 hbI (Algebra.IsIntegral.isIntegral b)

end Semicontinuity.Baire
