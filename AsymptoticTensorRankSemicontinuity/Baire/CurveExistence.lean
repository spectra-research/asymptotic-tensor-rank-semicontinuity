/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Baire.Dictionary
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# A curve through a point meeting a dense open (Kraft AI.4.5 Satz)

This file formalises Kraft's curve-existence theorem, **AI.4.5 Satz**
(kraft tex:7229–7231):

> *Satz: Sei `Z` eine irreduzible Varietät, `z ∈ Z` und `U ⊂ Z` eine offene
> dichte Teilmenge. Dann gibt es eine irreduzible Kurve `C ⊂ Z`, welche `z`
> enthält und `U` trifft.*

(In English: for an irreducible variety `Z`, a point `z ∈ Z`, and a dense open
`U ⊆ Z`, there is an irreducible curve `C ⊆ Z` through `z` that meets `U`.)

Kraft's proof (AI.4.5) runs through Noether normalization: take a finite
surjective morphism `φ : Z → ℂⁿ` with `n = dim Z`, pick a generic line `Y'`
through `φ(z)` avoiding `φ(Z∖U)`, and apply the going-down lemma to lift `Y'`
to an irreducible curve `C ⊆ Z` through `z` with `φ(C) = Y'`, so `C ∩ U ≠ ∅`.

The going-down Lemma (kraft tex:7223) is supplied by Mathlib's
`Algebra.HasGoingDown` instance
(`Mathlib/RingTheory/IntegralClosure/GoingDown.lean:48`) for
`[IsDomain S] [FaithfulSMul R S] [Algebra.IsIntegral R S] [IsIntegrallyClosed R]`,
all four hypotheses being supplied by:
* `S = coordRing X` a domain (Dictionary `isDomain_coordRing_zeroLocus`),
* `R = MvPolynomial (Fin d) ℂ` integrally closed (UFD instance),
* integrality + faithfulness from Noether normalization
  (`exists_integral_inj_algHom_of_fg`).

Everything is stated against `(Fin n → ℂ)`
point-sets + Mathlib; the bridge from `BaireProperty.lean`'s abstract-`V`
Zariski API is handled through the coordinate formulation in `BaireProperty.lean`.

## Algebraic ingredients

* `L1.1` Noether normalization ⟹ integral injective `g : ℂ[Fin d] →ₐ coordRing X`.
* `L1.2` a good base point `y ∉ φ(X \ V)` (nonzero-ideal contraction).
* `L1.3` the line `Y'` through `φ(z)` and `y`.
* `L1.4` going-down lifts the line's prime to a curve prime `Q ∋ z`.
* `L1.5` `C = zeroLocus Q` is integral over the line.
-/

universe u

namespace Semicontinuity.Baire

open MvPolynomial

variable {n : ℕ}

/-! ## L1.4 — the abstract going-down lift (Kraft AI.4.5 Lemma, kraft tex:7223)

The geometric going-down Lemma of Kraft AI.4.5 (kraft tex:7223): for `φ : Z → Y`
finite surjective, `Z` irreducible, `Y` normal, an irreducible closed
`Y' ⊆ Y` through `φ(z)` lifts to an irreducible closed `Z' ⊆ Z` through `z` with
`φ(Z') = Y'`.

In ring language this is `Ideal.exists_ideal_le_liesOver_of_le`: given a
going-down extension `R → S`, primes `p ≤ q` in `R`, and a prime `Q` of `S`
lying over `q`, there is a prime `P ≤ Q` of `S` lying over `p`. We package the
exact form used below: `p` = the line's prime, `q` = `m_{φ(z)}`,
`Q` = `vanishingIdeal {z}` lifted to `coordRing X`. -/

/-- **L1.4 (going-down lift, ring form)** (Kraft AI.4.5 Lemma, kraft tex:7223;
Mathlib `Ideal.exists_ideal_le_liesOver_of_le` + the `HasGoingDown` instance
`Mathlib/RingTheory/IntegralClosure/GoingDown.lean:48`).

For `S` a domain, integral and faithful over an integrally closed `R`, given
primes `p ≤ q` of `R` and a prime `Q` of `S` lying over `q`, there is a prime
`P ≤ Q` of `S` lying over `p`. -/
theorem exists_prime_le_liesOver_of_le
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain S] [FaithfulSMul R S] [Algebra.IsIntegral R S] [IsIntegrallyClosed R]
    {p q : Ideal R} [p.IsPrime] [q.IsPrime] (Q : Ideal S) [Q.IsPrime] [Q.LiesOver q]
    (hpq : p ≤ q) :
    ∃ P ≤ Q, P.IsPrime ∧ P.LiesOver p :=
  Ideal.exists_ideal_le_liesOver_of_le (p := p) (q := q) Q hpq

/-! ## Evaluation at a point of `X`, descended through the coordinate ring

For a point `z ∈ X = zeroLocus ℂ I`, evaluation `aeval z : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ`
kills `I = vanishingIdeal X` (since `I ≤ vanishingIdeal {z}`), hence descends to a
`ℂ`-algebra hom `coordRing X →ₐ[ℂ] ℂ`. This is the ring-language form of "a point of `X`",
used to compute `φ(z)` and to read off coordinates of lying-over points. -/

/-- Evaluation at `z ∈ zeroLocus ℂ I` descends to a `ℂ`-algebra hom on the coordinate ring. -/
noncomputable def evalAtPoint
    {I : Ideal (MvPolynomial (Fin n) ℂ)}
    {z : Fin n → ℂ} (hz : z ∈ zeroLocus ℂ I) :
    coordRing (zeroLocus ℂ I) →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ (vanishingIdeal ℂ (zeroLocus ℂ I)) (aeval z) (by
    intro p hp
    rw [mem_vanishingIdeal_iff] at hp
    exact hp z hz)

@[simp] theorem evalAtPoint_mk
    {I : Ideal (MvPolynomial (Fin n) ℂ)}
    {z : Fin n → ℂ} (hz : z ∈ zeroLocus ℂ I) (p : MvPolynomial (Fin n) ℂ) :
    evalAtPoint hz (Ideal.Quotient.mk _ p) = aeval z p := rfl

/-! ## Kraft AI.4.5 Satz (kraft tex:7229–7231) -/

/-- **D2 point-injectivity** (over `ℂ`): distinct points have distinct vanishing
ideals. If `vanishingIdeal ℂ {z} = vanishingIdeal ℂ {w}` then `z = w`: for each
coordinate `i`, the affine-linear `X i - C (w i)` vanishes at `w`, hence at `z`,
giving `z i = w i`. -/
theorem eq_of_vanishingIdeal_singleton_eq
    {z w : Fin n → ℂ}
    (h : vanishingIdeal ℂ ({z} : Set (Fin n → ℂ))
       = vanishingIdeal ℂ ({w} : Set (Fin n → ℂ))) :
    z = w := by
  funext i
  have hmemw : (X i - C (w i) : MvPolynomial (Fin n) ℂ)
      ∈ vanishingIdeal ℂ ({w} : Set (Fin n → ℂ)) := by
    rw [mem_vanishingIdeal_singleton_iff]
    simp
  rw [← h, mem_vanishingIdeal_singleton_iff] at hmemw
  simpa [sub_eq_zero] using hmemw

/-- **L1.1 degenerate (`d = 0`) case → single point.** If the coordinate ring of
`X = zeroLocus ℂ I` (`I` prime) is a **field**, then `I` is maximal and `X` is a
single point: any two points of `X` have equal (maximal) vanishing ideals, hence
coincide. This is the Noether-normalization-in-`0`-variables branch (kraft
tex:7231 `n := dim Z`, the degenerate `dim Z = 0`). -/
theorem eq_of_mem_zeroLocus_of_isField
    {I : Ideal (MvPolynomial (Fin n) ℂ)} [I.IsPrime]
    (hfield : IsField (coordRing (zeroLocus ℂ I)))
    {z w : Fin n → ℂ} (hz : z ∈ zeroLocus ℂ I) (hw : w ∈ zeroLocus ℂ I) :
    z = w := by
  -- `coordRing X = MvPolynomial ⧸ vanishingIdeal X` a field ⟹ `vanishingIdeal X`
  -- maximal; by D1 it equals `I`, so `I` is maximal.
  have hImax : I.IsMaximal := by
    have hmax : (vanishingIdeal ℂ (zeroLocus ℂ I)).IsMaximal :=
      Ideal.Quotient.maximal_of_isField _ hfield
    rwa [vanishingIdeal_zeroLocus_of_isPrime I] at hmax
  -- `I ≤ vanishingIdeal {z}`, both maximal ⟹ equal; same for `w`.
  have hz' : I ≤ vanishingIdeal ℂ {z} :=
    (mem_zeroLocus_iff_le_vanishingIdeal_singleton I z).mp hz
  have hw' : I ≤ vanishingIdeal ℂ {w} :=
    (mem_zeroLocus_iff_le_vanishingIdeal_singleton I w).mp hw
  have hzeq : I = vanishingIdeal ℂ ({z} : Set (Fin n → ℂ)) :=
    hImax.eq_of_le (isMaximal_vanishingIdeal_singleton z).ne_top hz'
  have hweq : I = vanishingIdeal ℂ ({w} : Set (Fin n → ℂ)) :=
    hImax.eq_of_le (isMaximal_vanishingIdeal_singleton w).ne_top hw'
  exact eq_of_vanishingIdeal_singleton_eq (hzeq.symm.trans hweq)

/-- **Base-point existence** (Kraft tex:7231, the choice `y ∈ ℂⁿ − φ(Z−U)`):
a nonzero polynomial `h` over the infinite field `ℂ` in `≥ 1` variables has a
non-vanishing point distinct from any prescribed point `a`. We move along the
first coordinate axis from a non-vanishing point `y₀`: the univariate restriction
is nonzero, has finitely many roots, so cofinitely many parameters give a
non-vanishing point, and at most one of those points equals `a`. -/
theorem exists_aeval_ne_zero_and_ne {m : ℕ}
    {h : MvPolynomial (Fin (m + 1)) ℂ} (hh : h ≠ 0) (a : Fin (m + 1) → ℂ) :
    ∃ y : Fin (m + 1) → ℂ, aeval y h ≠ 0 ∧ y ≠ a := by
  -- A point `y₀` with `h y₀ ≠ 0` (infinite-field funext).
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Fin (m + 1) → ℂ, aeval y₀ h ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    refine hh (MvPolynomial.funext (R := ℂ) fun x => ?_)
    have := hcon x
    rw [← MvPolynomial.aeval_eq_eval]
    simpa using this
  -- Univariate restriction `u(t) = h (Function.update y₀ 0 (y₀ 0 + t))`.
  set ρ : Fin (m + 1) → Polynomial ℂ :=
    fun i => if i = 0 then Polynomial.C (y₀ 0) + Polynomial.X else Polynomial.C (y₀ i) with hρ
  set u : Polynomial ℂ := aeval ρ h with hu
  have hpt : ∀ t : ℂ, Polynomial.eval t u = aeval (Function.update y₀ 0 (y₀ 0 + t)) h := by
    intro t
    have key : (Polynomial.aeval t).comp (aeval ρ : MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] Polynomial ℂ)
        = aeval (Function.update y₀ 0 (y₀ 0 + t)) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, aeval_X, hρ]
      by_cases hi : i = 0
      · subst hi; simp [Function.update_self]
      · simp [hi]
    have := AlgHom.congr_fun key h
    simp only [AlgHom.comp_apply] at this
    rw [hu, ← this, Polynomial.coe_aeval_eq_eval]
  have hu0 : u ≠ 0 := by
    intro hu0
    apply hy₀
    have := hpt 0
    rw [hu0] at this
    simpa using this.symm
  -- Finitely many roots of `u`; the points are distinct for distinct `t`,
  -- so we avoid both the (finite) root set and the at-most-one `t` with the point `= a`.
  have hfin : {t : ℂ | Polynomial.IsRoot u t}.Finite := Polynomial.finite_setOf_isRoot hu0
  have hbad : {t : ℂ | Function.update y₀ 0 (y₀ 0 + t) = a}.Subsingleton := by
    intro s hs t ht
    simp only [Set.mem_setOf_eq] at hs ht
    have hs0 : y₀ 0 + s = a 0 := by have := congrFun hs 0; simpa using this
    have ht0 : y₀ 0 + t = a 0 := by have := congrFun ht 0; simpa using this
    have : y₀ 0 + s = y₀ 0 + t := by rw [hs0, ht0]
    exact add_left_cancel this
  obtain ⟨t, ht⟩ : ∃ t : ℂ, ¬ Polynomial.IsRoot u t ∧
      Function.update y₀ 0 (y₀ 0 + t) ≠ a := by
    by_contra hcon
    push_neg at hcon
    -- Then every `t` is a root of `u` or makes the point `= a`.
    have : (Set.univ : Set ℂ) ⊆
        {t | Polynomial.IsRoot u t} ∪ {t | Function.update y₀ 0 (y₀ 0 + t) = a} := by
      intro t _
      by_cases hr : Polynomial.IsRoot u t
      · exact Or.inl hr
      · exact Or.inr (hcon t hr)
    have huniv : (Set.univ : Set ℂ).Finite :=
      (hfin.union (hbad.finite)).subset this
    exact huniv.not_infinite Set.infinite_univ
  refine ⟨Function.update y₀ 0 (y₀ 0 + t), ?_, ht.2⟩
  rw [← hpt t]
  exact ht.1

/-- **Descent of the line to the curve** (Kraft tex:7223–7231, steps B7–B8).
Abstract over the coordinate rings to avoid `whnf` blow-up from the non-canonical
`Algebra R S` instance: given the integral injective `g : R →ₐ[ℂ] S` (as a plain
algebra map), a prime `P0` of `S` whose contraction along `g` is `pL`, and the
target curve coordinate ring `T` with `T ≃ₐ[ℂ] S ⧸ P0`, the quotient map
`R ⧸ pL → S ⧸ P0` is injective + integral, so it composes (through `R ⧸ pL ≃ ℂ[t]`
and `T ≃ S ⧸ P0`) to an injective integral `ℂ[t] →ₐ[ℂ] T`. -/
private theorem descend_line_to_curve
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra ℂ R] [Algebra ℂ S] [Algebra ℂ T]
    (g : R →ₐ[ℂ] S) (hg_int : (g : R →+* S).IsIntegral)
    (P0 : Ideal S) [P0.IsPrime]
    (eqL : (R ⧸ P0.comap (g : R →+* S)) ≃ₐ[ℂ] MvPolynomial (Fin 1) ℂ)
    (eqCoord : T ≃ₐ[ℂ] S ⧸ P0) :
    ∃ ψ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ] T,
      Function.Injective ψ ∧ ψ.toRingHom.IsIntegral := by
  -- `gdesc : R ⧸ (comap g P0) → S ⧸ P0`, the descent of `g` (Mathlib `quotientMap`).
  let gdesc : (R ⧸ P0.comap (g : R →+* S)) →+* S ⧸ P0 :=
    Ideal.quotientMap P0 (g : R →+* S) le_rfl
  have hgdesc_inj : Function.Injective gdesc :=
    Ideal.quotientMap_injective
  have hmk_int : (Ideal.Quotient.mk P0).IsIntegral :=
    RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective
  have hgdesc_int : gdesc.IsIntegral := by
    rw [show gdesc = Ideal.quotientMap P0 (g : R →+* S) le_rfl from rfl,
      isIntegral_quotientMap_iff]
    exact RingHom.IsIntegral.trans _ _ hg_int hmk_int
  -- Upgrade to a `ℂ`-algebra map; its underlying function is `gdesc`.
  let gdescₐ : (R ⧸ P0.comap (g : R →+* S)) →ₐ[ℂ] S ⧸ P0 :=
    Ideal.quotientMapₐ P0 g le_rfl
  have hgdescₐ_fun : ⇑gdescₐ = ⇑gdesc := rfl
  let ψ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ] T :=
    (eqCoord.symm.toAlgHom.comp gdescₐ).comp eqL.symm.toAlgHom
  refine ⟨ψ, ?_, ?_⟩
  · have h1 : Function.Injective (⇑gdescₐ) := by
      simpa [hgdescₐ_fun] using hgdesc_inj
    intro u v huv
    simp only [ψ, AlgHom.comp_apply] at huv
    exact eqL.symm.injective (h1 (eqCoord.symm.injective huv))
  · -- integral: iso ∘ integral ∘ iso (compositions of `RingHom.IsIntegral`).
    have hi1 : (eqCoord.symm.toAlgHom.toRingHom).IsIntegral :=
      RingHom.isIntegral_of_surjective _ eqCoord.symm.surjective
    have hi2 : (eqL.symm.toAlgHom.toRingHom).IsIntegral :=
      RingHom.isIntegral_of_surjective _ eqL.symm.surjective
    have hgdescₐ_int : gdescₐ.toRingHom.IsIntegral := hgdesc_int
    have step1 : ((eqCoord.symm.toAlgHom.comp gdescₐ).toRingHom).IsIntegral :=
      RingHom.IsIntegral.trans _ _ hgdescₐ_int hi1
    exact RingHom.IsIntegral.trans _ _ hi2 step1

set_option maxHeartbeats 1600000 in
-- The full Kraft tex:7229–7231 construction (line + going-down + transport + descent + meeting
-- open) is one interlocking proof; the `coordRing` quotient defeq makes the elaboration heavy.
/-- The positive-dimensional Kraft curve construction (Kraft AI.4.5 Satz, tex:7229–7231),
given the nonzero contracted base polynomial `h ∈ (span {fbar}).comap g`.

Construction (following Kraft tex:7231 verbatim):
* the base point `a = φ(z)` is `evalAtPoint hz ∘ g` on the coordinates; a base point
  `y` with `aeval y h ≠ 0` and `y ≠ a` exists (`exists_aeval_ne_zero_and_ne`), giving a
  genuine line `Y'` through `a` and `y`;
* the line algebra map `ψL : R →ₐ MvPolynomial (Fin 1) ℂ`, `X i ↦ C (a i) + C (y i - a i)·X 0`,
  is surjective (since `y ≠ a`), so `R ⧸ ker ψL ≃ₐ[ℂ] MvPolynomial (Fin 1) ℂ` (the line `≅ ℂ[t]`);
* `ker ψL ≤ comap g (ker (evalAtPoint hz))` (the line passes through `a = φ(z)`), so going-down
  (Kraft tex:7223, `exists_prime_le_liesOver_of_le`) lifts to a prime `P0` of `S`
  lying over `ker ψL`;
* transport `Q := comap (mkₐ 𝔳) P0`: prime, `I ≤ Q`, `z ∈ zeroLocus Q`,
  `coordRing (zeroLocus Q) ≅ S ⧸ P0`;
* `ψ : MvPolynomial (Fin 1) ℂ ≅ R ⧸ ker ψL ↪ S ⧸ P0 ≅ coordRing (zeroLocus Q)` injective + integral;
* a lying-over point `c` of the curve over `y` satisfies `aeval c f ≠ 0`: if `aeval c f = 0` then
  `g h = fbar·s` forces `aeval y h = 0`, contradicting the choice of `y` (the meeting-open witness).
-/
private theorem exists_curve_from_nonzero_contracted_base
    {I : Ideal (MvPolynomial (Fin n) ℂ)} [I.IsPrime]
    {z : Fin n → ℂ} (hz : z ∈ zeroLocus ℂ I)
    {f : MvPolynomial (Fin n) ℂ}
    (_hf : ∃ w ∈ zeroLocus ℂ I, aeval w f ≠ 0)
    {d : ℕ}
    (g : MvPolynomial (Fin (d + 1)) ℂ →ₐ[ℂ] coordRing (zeroLocus ℂ I))
    (hg_inj : Function.Injective g) (hg_int : g.IsIntegral)
    (hbase :
      ∃ h : MvPolynomial (Fin (d + 1)) ℂ,
        h ≠ 0 ∧
        h ∈ (Ideal.span
          {((Ideal.Quotient.mkₐ ℂ (vanishingIdeal ℂ (zeroLocus ℂ I))) f :
            coordRing (zeroLocus ℂ I))}).comap g.toRingHom) :
    ∃ (Q : Ideal (MvPolynomial (Fin n) ℂ)) (_ : Q.IsPrime),
      I ≤ Q ∧
      z ∈ zeroLocus ℂ Q ∧
      (zeroLocus ℂ Q ∩
        {x : Fin n → ℂ | x ∈ zeroLocus ℂ I ∧ aeval x f ≠ 0}).Nonempty ∧
      (∃ ψ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ] coordRing (zeroLocus ℂ Q),
        Function.Injective ψ ∧ ψ.toRingHom.IsIntegral) := by
  classical
  -- Abbreviations and the going-down algebra context.
  set 𝔳 : Ideal (MvPolynomial (Fin n) ℂ) := vanishingIdeal ℂ (zeroLocus ℂ I) with h𝔳
  have h𝔳I : 𝔳 = I := vanishingIdeal_zeroLocus_of_isPrime I
  let R := MvPolynomial (Fin (d + 1)) ℂ
  let S := coordRing (zeroLocus ℂ I)
  letI : Algebra R S := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral R S := ⟨fun x => hg_int x⟩
  haveI : FaithfulSMul R S :=
    (faithfulSMul_iff_algebraMap_injective R S).mpr hg_inj
  haveI : IsDomain S := isDomain_coordRing_zeroLocus I
  have halg : (algebraMap R S) = g.toRingHom := rfl
  -- B5(iii): the contracted nonzero base polynomial `h`, with `g h ∈ span {fbar}`.
  obtain ⟨h, hh_ne, hh_mem⟩ := hbase
  -- evaluation `evz : S →ₐ ℂ` at `z`, and the base point `a = φ(z)`.
  let evz : S →ₐ[ℂ] ℂ := evalAtPoint hz
  let a : Fin (d + 1) → ℂ := fun i => evz (g (X i))
  -- KEY (Step A): `evz (g p) = aeval a p` for all `p`.
  have hga : ∀ p : R, evz (g p) = aeval a p := by
    have : (evz.comp g) = (aeval a : R →ₐ[ℂ] ℂ) := by
      apply MvPolynomial.algHom_ext; intro i
      rw [AlgHom.comp_apply, aeval_X]
    intro p; exact AlgHom.congr_fun this p
  -- B5(iv): a base point `y` with `aeval y h ≠ 0` and `y ≠ a` (the genuine line).
  obtain ⟨y, hy_ne, hy_a⟩ := exists_aeval_ne_zero_and_ne hh_ne a
  -- B5(v): the line algebra map `ψL : R →ₐ MvPolynomial (Fin 1) ℂ`,
  -- `X i ↦ C (a i) + C (y i - a i) * X 0`.
  let ψL : R →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
    aeval (fun i => C (a i) + C (y i - a i) * X (0 : Fin 1))
  have hψL_X : ∀ i, ψL (X i) = C (a i) + C (y i - a i) * X (0 : Fin 1) := by
    intro i; rw [show ψL (X i) = aeval _ (X i) from rfl, aeval_X]
  -- evaluation of `ψL` at `t ↦ c` recovers the affine point `a + c•(y-a)`.
  have hψL_eval : ∀ (c : ℂ) (p : R),
      aeval (fun _ : Fin 1 => c) (ψL p) = aeval (fun i => a i + c * (y i - a i)) p := by
    intro c
    have : (aeval (fun _ : Fin 1 => c)).comp ψL
        = (aeval (fun i => a i + c * (y i - a i)) : R →ₐ[ℂ] ℂ) := by
      apply MvPolynomial.algHom_ext; intro i
      rw [AlgHom.comp_apply, hψL_X i, aeval_X]
      rw [map_add, map_mul, aeval_C, aeval_C, aeval_X]
      simp only [Algebra.algebraMap_self, RingHom.id_apply]
      ring
    intro p; exact AlgHom.congr_fun this p
  -- `pL := ker ψL` is prime (target a domain).
  let pL : Ideal R := RingHom.ker ψL.toRingHom
  haveI hpL_prime : pL.IsPrime := RingHom.ker_isPrime _
  -- `ψL` is surjective: since `y ≠ a`, some coordinate `j` has `y j ≠ a j`,
  -- and then `X 0` is in the range.
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ a j := by
    by_contra hcon; push_neg at hcon; exact hy_a (funext hcon)
  have hjne : (y j - a j) ≠ 0 := sub_ne_zero.mpr hj
  have hψL_surj : Function.Surjective ψL := by
    -- `X 0` is in the range via the preimage `(y j - a j)⁻¹ • (X j - C (a j))`.
    have hψLC : ∀ c : ℂ, ψL (C c) = C c := by
      intro c
      rw [show ψL (C c) = aeval _ (C c) from rfl, aeval_C]; rfl
    have hX0 : ψL (C ((y j - a j)⁻¹) * (X j - C (a j))) = X (0 : Fin 1) := by
      rw [map_mul, map_sub, hψL_X j, hψLC, hψLC, add_sub_cancel_left,
        ← mul_assoc, ← C_mul, inv_mul_cancel₀ hjne, C_1, one_mul]
    -- range is a subalgebra containing constants and `X 0`, so it is everything.
    have hrange : ψL.range = ⊤ := by
      rw [_root_.eq_top_iff, ← MvPolynomial.adjoin_range_X (σ := Fin 1) (R := ℂ),
        Algebra.adjoin_le_iff]
      rintro _ ⟨k, rfl⟩
      rw [Fin.eq_zero k, ← hX0]
      exact AlgHom.mem_range_self _ _
    intro w
    have : w ∈ ψL.range := by rw [hrange]; exact Algebra.mem_top
    obtain ⟨v, hv⟩ := this
    exact ⟨v, hv⟩
  -- `eqL : R ⧸ pL ≃ₐ[ℂ] MvPolynomial (Fin 1) ℂ`.
  let eqL : (R ⧸ pL) ≃ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
    Ideal.quotientKerAlgEquivOfSurjective hψL_surj
  -- B5(vi): `Mz := ker evz`, maximal; `pz := comap g Mz`; `pL ≤ pz`.
  let Mz : Ideal S := RingHom.ker evz.toRingHom
  have hevz_surj : Function.Surjective evz := fun c => ⟨algebraMap ℂ S c, by simp [evz]⟩
  haveI hMz_max : Mz.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hevz_surj
  haveI hMz_prime : Mz.IsPrime := hMz_max.isPrime
  let pz : Ideal R := Mz.comap g.toRingHom
  haveI hpz_prime : pz.IsPrime := Ideal.IsPrime.comap _
  haveI hMz_lies : Mz.LiesOver pz := ⟨rfl⟩
  have hpL_le_pz : pL ≤ pz := by
    intro p hp
    -- `p ∈ pL` means `ψL p = 0`; evaluate at `t = 0` to get `aeval a p = 0`,
    -- i.e. `evz (g p) = 0`, i.e. `g p ∈ Mz`, i.e. `p ∈ pz`.
    have hp0 : ψL p = 0 := by simpa [pL, RingHom.mem_ker] using hp
    have : aeval a p = 0 := by
      have := hψL_eval 0 p
      simp only [hp0, map_zero] at this
      simpa using this.symm
    have hgz : evz (g p) = 0 := by rw [hga p]; exact this
    change g.toRingHom p ∈ Mz
    simpa [Mz, RingHom.mem_ker] using hgz
  -- B6: going-down lift `P0 ≤ Mz`, prime, lying over `pL`.
  obtain ⟨P0, hP0_le, hP0_prime, hP0_lies⟩ :=
    exists_prime_le_liesOver_of_le (R := R) (S := S) (p := pL) (q := pz) Mz hpL_le_pz
  haveI : P0.IsPrime := hP0_prime
  haveI : P0.LiesOver pL := hP0_lies
  -- B7: transport to `MvPolynomial (Fin n) ℂ` via the canonical quotient map.
  let mkI : MvPolynomial (Fin n) ℂ →ₐ[ℂ] S := Ideal.Quotient.mkₐ ℂ 𝔳
  let Q : Ideal (MvPolynomial (Fin n) ℂ) := P0.comap mkI.toRingHom
  haveI hQ_prime : Q.IsPrime := Ideal.IsPrime.comap _
  have hQ_vanish : vanishingIdeal ℂ (zeroLocus ℂ Q) = Q := vanishingIdeal_zeroLocus_of_isPrime Q
  -- `I ≤ Q`: `I = 𝔳 = ker mkI ≤ comap mkI P0 = Q`.
  have hIQ : I ≤ Q := by
    rw [← h𝔳I]
    intro p hp
    change mkI.toRingHom p ∈ P0
    have : mkI.toRingHom p = 0 := by
      simp only [mkI, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hp
    rw [this]; exact P0.zero_mem
  -- `z ∈ zeroLocus Q`: need `Q ≤ vanishingIdeal {z}`.
  -- `Q = comap mkI P0 ≤ comap mkI Mz = ker (evz ∘ mkI) = ker (aeval z) = vanishingIdeal {z}`.
  have hQz : z ∈ zeroLocus ℂ Q := by
    rw [mem_zeroLocus_iff_le_vanishingIdeal_singleton]
    intro p hp
    have hpP0 : mkI.toRingHom p ∈ P0 := hp
    have hpMz : mkI.toRingHom p ∈ Mz := hP0_le hpP0
    rw [mem_vanishingIdeal_singleton_iff]
    have : evz (mkI p) = 0 := by simpa [Mz, RingHom.mem_ker] using hpMz
    simpa [evz, mkI, evalAtPoint] using this
  -- The composite `mkP0 ∘ mkI : MvPolynomial (Fin n) ℂ →ₐ S ⧸ P0` is surjective with kernel `Q`.
  let mkP0 : S →ₐ[ℂ] S ⧸ P0 := Ideal.Quotient.mkₐ ℂ P0
  let π : MvPolynomial (Fin n) ℂ →ₐ[ℂ] S ⧸ P0 := mkP0.comp mkI
  have hπ_surj : Function.Surjective π :=
    (Ideal.Quotient.mkₐ_surjective ℂ P0).comp (Ideal.Quotient.mkₐ_surjective ℂ 𝔳)
  have hπ_ker : RingHom.ker π.toRingHom = Q := by
    ext p
    simp only [RingHom.mem_ker, π, AlgHom.comp_apply, mkP0, mkI,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    rfl
  -- `coordRing (zeroLocus Q) = MvPolynomial ⧸ vanishingIdeal (zeroLocus Q)`, and the latter is `Q`.
  let eqCoord : coordRing (zeroLocus ℂ Q) ≃ₐ[ℂ] S ⧸ P0 :=
    (Ideal.quotientEquivAlgOfEq ℂ hQ_vanish).trans
      ((hπ_ker ▸ Ideal.quotientKerAlgEquivOfSurjective hπ_surj :
        (MvPolynomial (Fin n) ℂ ⧸ Q) ≃ₐ[ℂ] S ⧸ P0))
  -- `pL = comap g P0` (lying-over), used to feed the abstract descent lemma.
  have hpL_eq : pL = P0.comap (g : R →+* S) := by
    have := hP0_lies.over
    simpa [Ideal.under, halg] using this
  -- `eqL' : (R ⧸ comap g P0) ≃ₐ ℂ[t]`, transporting `eqL` along `pL = comap g P0`.
  let eqL' : (R ⧸ P0.comap (g : R →+* S)) ≃ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
    (Ideal.quotientEquivAlgOfEq ℂ hpL_eq.symm).trans eqL
  -- Assemble `ψ` via the abstract B7–B8 descent (kept separate to avoid `whnf` blow-up).
  refine ⟨Q, hQ_prime, hIQ, hQz, ?_, ?_⟩
  · -- B9: the meeting-open witness (a point of `C` over `y`, lying in `{f ≠ 0}`).
    have hh_not_pL : h ∉ pL := by
      intro hp
      have hψh : ψL h = 0 := by simpa [pL, RingHom.mem_ker] using hp
      have hev := hψL_eval 1 h
      simp only [hψh, map_zero] at hev
      have hpoint : (fun i : Fin (d + 1) => a i + 1 * (y i - a i)) = y := by
        funext i; ring
      exact hy_ne (by simpa [hpoint] using hev.symm)
    have hgh_not_P0 : g h ∉ P0 := by
      intro hgh
      exact hh_not_pL (by
        have : h ∈ P0.comap g.toRingHom := hgh
        simpa [hpL_eq] using this)
    let fbar : S :=
      ((Ideal.Quotient.mkₐ ℂ (vanishingIdeal ℂ (zeroLocus ℂ I))) f :
        coordRing (zeroLocus ℂ I))
    have hfbar_not_P0 : fbar ∉ P0 := by
      intro hfbar
      exact hgh_not_P0 (by
        have hspan_le : Ideal.span ({fbar} : Set S) ≤ P0 := by
          exact Ideal.span_le.mpr (by
            intro x hx
            rw [Set.mem_singleton_iff] at hx
            simpa [hx] using hfbar)
        exact hspan_le (by simpa [fbar, S] using hh_mem))
    have hf_not_Q : f ∉ Q := by
      intro hfQ
      exact hfbar_not_P0 (by
        simpa [Q, mkI, fbar, h𝔳, S] using hfQ)
    have hnot_all : ¬ ∀ x ∈ zeroLocus ℂ Q, aeval x f = 0 := by
      intro hall
      exact hf_not_Q (by
        rw [← hQ_vanish, mem_vanishingIdeal_iff]
        exact hall)
    push_neg at hnot_all
    obtain ⟨x, hxQ, hxf⟩ := hnot_all
    refine ⟨x, ?_⟩
    exact ⟨hxQ, (fun p hp => hxQ p (hIQ hp)), hxf⟩
  · -- B8: `ψ : MvPolynomial (Fin 1) ℂ ≅ R/pL ↪ S/P0 ≅ coordRing(zeroLocus Q)`,
    -- via the abstract descent lemma (avoids `whnf` blow-up over the `coordRing` defeq).
    exact descend_line_to_curve g hg_int P0 eqL' eqCoord

/-- Nondegenerate (`dim X ≥ 1`) Kraft curve construction.

Exact Lean goal for the branch where Noether normalization of
`coordRing X` lands in `MvPolynomial (Fin (d+1)) ℂ` (so `dim X = d+1 ≥ 1`):
from `hz : z ∈ zeroLocus ℂ I`, `hf : ∃ w ∈ zeroLocus ℂ I, aeval w f ≠ 0`,
and the integral injective Noether map
`g : MvPolynomial (Fin (d+1)) ℂ →ₐ[ℂ] coordRing (zeroLocus ℂ I)`,
construct a prime `Q ⊇ I` with `z ∈ zeroLocus ℂ Q`,
`(zeroLocus ℂ Q) ∩ (zeroLocus ℂ I ∩ {f ≠ 0}) ≠ ∅`, and an injective integral
algebra map `MvPolynomial (Fin 1) ℂ →ₐ[ℂ] coordRing (zeroLocus ℂ Q)`.

Kraft tex:7231 builds the line through `φ z` and a base point `y ∉ φ(X∖V)` (via
the nonzero-ideal contraction `comap_ne_bot_of_isIntegral`), tex:7223 lifts it by
going-down (`exists_prime_le_liesOver_of_le`). This theorem reduces to
`exists_curve_from_nonzero_contracted_base` after extracting the nonzero
contracted base polynomial `h` (the B5(i) step), which performs the full
positive-dimensional geometric construction (line prime → going-down lift →
transport to `MvPolynomial (Fin n) ℂ` → line coordinate ring → meeting-open
point). -/
theorem exists_curve_through_point_curve_case
    {I : Ideal (MvPolynomial (Fin n) ℂ)} [I.IsPrime]
    {z : Fin n → ℂ} (hz : z ∈ zeroLocus ℂ I)
    {f : MvPolynomial (Fin n) ℂ}
    (hf : ∃ w ∈ zeroLocus ℂ I, aeval w f ≠ 0)
    {d : ℕ}
    (g : MvPolynomial (Fin (d + 1)) ℂ →ₐ[ℂ] coordRing (zeroLocus ℂ I))
    (hg_inj : Function.Injective g) (hg_int : g.IsIntegral) :
    ∃ (Q : Ideal (MvPolynomial (Fin n) ℂ)) (_ : Q.IsPrime),
      I ≤ Q ∧
      z ∈ zeroLocus ℂ Q ∧
      (zeroLocus ℂ Q ∩
        {x : Fin n → ℂ | x ∈ zeroLocus ℂ I ∧ aeval x f ≠ 0}).Nonempty ∧
      (∃ ψ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ] coordRing (zeroLocus ℂ Q),
        Function.Injective ψ ∧ ψ.toRingHom.IsIntegral) := by
  -- Install the going-down algebra context (R = base line ambient, S = coordRing X):
  -- the four typeclasses feeding `exists_prime_le_liesOver_of_le` (kraft tex:7223).
  let R := MvPolynomial (Fin (d + 1)) ℂ
  let S := coordRing (zeroLocus ℂ I)
  letI : Algebra R S := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral R S := ⟨fun x => hg_int x⟩
  haveI : FaithfulSMul R S :=
    (faithfulSMul_iff_algebraMap_injective R S).mpr hg_inj
  haveI : IsDomain S := isDomain_coordRing_zeroLocus I
  -- B5(i): the class of `f` in the coordinate ring is nonzero, because `hf`
  -- gives a point of `X = zeroLocus I` where `f` evaluates nontrivially.
  let fbar : S :=
    ((Ideal.Quotient.mkₐ ℂ (vanishingIdeal ℂ (zeroLocus ℂ I))) f :
      coordRing (zeroLocus ℂ I))
  have hfbar_ne : fbar ≠ 0 := by
    intro hfbar0
    obtain ⟨w, hwX, hwf⟩ := hf
    have hfmem : f ∈ vanishingIdeal ℂ (zeroLocus ℂ I) := by
      exact Ideal.Quotient.eq_zero_iff_mem.mp
        (by simpa [fbar, Ideal.Quotient.mkₐ_eq_mk] using hfbar0)
    rw [mem_vanishingIdeal_iff] at hfmem
    have hfw : f ∈ vanishingIdeal ℂ ({w} : Set (Fin n → ℂ)) := by
      rw [mem_vanishingIdeal_singleton_iff]
      exact hfmem w hwX
    rw [mem_vanishingIdeal_singleton_iff] at hfw
    exact hwf hfw
  have hspan_ne : (Ideal.span ({fbar} : Set S)) ≠ ⊥ := by
    intro hspan
    have hfbar_mem_bot : fbar ∈ (⊥ : Ideal S) := by
      rw [← hspan]
      exact Ideal.mem_span_singleton_self fbar
    exact hfbar_ne (by simpa using hfbar_mem_bot)
  have hcomap_ne :
      (Ideal.span ({fbar} : Set S)).comap (algebraMap R S) ≠ ⊥ :=
    comap_ne_bot_of_isIntegral (R := R) (S := S) (I := Ideal.span ({fbar} : Set S))
      hspan_ne
  obtain ⟨h, hhmem, hhne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcomap_ne
  have hbase :
      ∃ h : MvPolynomial (Fin (d + 1)) ℂ,
        h ≠ 0 ∧
        h ∈ (Ideal.span
          {((Ideal.Quotient.mkₐ ℂ (vanishingIdeal ℂ (zeroLocus ℂ I))) f :
            coordRing (zeroLocus ℂ I))}).comap g.toRingHom := by
    refine ⟨h, hhne, ?_⟩
    simpa [R, S, fbar, Algebra.algebraMap_self] using hhmem
  exact exists_curve_from_nonzero_contracted_base hz hf g hg_inj hg_int hbase

/-- **Kraft AI.4.5 Satz** (kraft tex:7229–7231), disjunctive (degenerate-aware)
form.

Let `X = zeroLocus ℂ I ⊆ (Fin n → ℂ)` be an irreducible (here: `I` prime)
Zariski-closed point-set, `z ∈ X`, and let `f : MvPolynomial (Fin n) ℂ` be a
polynomial not vanishing identically on `X` (so the dense open
`V := X ∩ {x | aeval x f ≠ 0}` is nonempty). Then **one of**:

* **(left, degenerate)** `z ∈ V` already, i.e. `z ∈ X ∧ aeval z f ≠ 0`; or
	* **(right, the Kraft curve)** there is an irreducible Zariski-closed curve
  `C = zeroLocus ℂ Q ⊆ X` (with `Q` prime, `I ≤ Q`) such that
  * `z ∈ C`;
  * `(C ∩ V).Nonempty` (the curve meets the dense open);
  * `C` is **finite over a line**: there is an injective integral `ℂ`-algebra
	    hom `MvPolynomial (Fin 1) ℂ →ₐ[ℂ] coordRing C`; `C` is integral over the
	    line `Y'` via Noether normalization restricted to `C`.

**Why the disjunction (degenerate-case convention, kraft tex:7229–7231).**
Kraft's `Satz` asserts an irreducible *Kurve* `C` (dimension 1) through `z`
meeting `V`; the construction is `Noether normalize` `X → ℂᵈ` then lift a line.
When `d = 0`, i.e. `coordRing X` is integral over `ℂ` (Noether normalization in
`0` variables), `X` is a single point: `X = {z}` and the dense open `V ⊆ X`
nonempty forces `V = {z} ∋ z`. There is then **no** finite-over-a-line curve —
`MvPolynomial (Fin 1) ℂ = ℂ[t] ↪ coordRing {z} ≅ ℂ` is impossible — so the
right disjunct is literally false, and Kraft's geometric statement only admits
the point as a *degenerate* "curve". The disjunctive form handles this by the
left branch `z ∈ V`; this is also exactly what the closure argument needs
(it only wants `z ∈ ℂ`-closure(V)`, and `z ∈ V ⊆ ℂ`-closure(V)` directly).

Proof (kraft tex:7233–7236): Noether normalization gives a finite surjective
`φ : X → ℂᵈ` (`d = dim X`). If `d = 0`, `X = {z}` and we land in the left
disjunct. Otherwise pick `y ∈ ℂᵈ ∖ φ(X ∖ V)` and let `Y'` be the line through
`φ(z)` and `y`. Going-down (kraft tex:7223, Mathlib `Algebra.HasGoingDown` over
the normal base `ℂᵈ`) lifts `Y'` to an irreducible curve `C ∋ z` with
`φ(C) = Y'`; by construction `C ∩ V ≠ ∅`. -/
theorem exists_curve_through_point
    {I : Ideal (MvPolynomial (Fin n) ℂ)} [I.IsPrime]
    {z : Fin n → ℂ} (hz : z ∈ zeroLocus ℂ I)
    {f : MvPolynomial (Fin n) ℂ}
    (hf : ∃ w ∈ zeroLocus ℂ I, aeval w f ≠ 0) :
    (z ∈ zeroLocus ℂ I ∧ aeval z f ≠ 0) ∨
    ∃ (Q : Ideal (MvPolynomial (Fin n) ℂ)) (_ : Q.IsPrime),
      I ≤ Q ∧
      z ∈ zeroLocus ℂ Q ∧
      (zeroLocus ℂ Q ∩
        {x : Fin n → ℂ | x ∈ zeroLocus ℂ I ∧ aeval x f ≠ 0}).Nonempty ∧
      (∃ ψ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ] coordRing (zeroLocus ℂ Q),
        Function.Injective ψ ∧ ψ.toRingHom.IsIntegral) := by
  -- Noether normalization of the coordinate ring (kraft tex:7231, "Nach 4.2").
  haveI : IsDomain (coordRing (zeroLocus ℂ I)) := isDomain_coordRing_zeroLocus I
  obtain ⟨d, g, hg_inj, hg_int⟩ :=
    exists_integral_inj_algHom_of_fg ℂ (coordRing (zeroLocus ℂ I))
  -- Install the algebra structure from the Noether map and record integrality.
  letI : Algebra (MvPolynomial (Fin d) ℂ) (coordRing (zeroLocus ℂ I)) :=
    g.toRingHom.toAlgebra
  have hAint : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ)
      (coordRing (zeroLocus ℂ I)) := ⟨fun x => hg_int x⟩
  -- Case on the Noether dimension `d`.
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- d = 0: `coordRing X` is integral over the field `MvPolynomial (Fin 0) ℂ`,
    -- hence a field; `X` is a single point, so `hf`'s witness `w` equals `z`
    -- and `aeval z f ≠ 0`: the LEFT disjunct (kraft tex:7231, degenerate dim 0).
    subst hd0
    have hbaseField : IsField (MvPolynomial (Fin 0) ℂ) :=
      MulEquiv.isField (Field.toIsField ℂ)
        (MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0)).toMulEquiv
    have hfield : IsField (coordRing (zeroLocus ℂ I)) :=
      isField_of_isIntegral_of_isField' hbaseField
    obtain ⟨w, hw, hwf⟩ := hf
    have hzw : z = w := eq_of_mem_zeroLocus_of_isField hfield hz hw
    exact Or.inl ⟨hz, hzw ▸ hwf⟩
  · -- d ≥ 1: the genuine Kraft curve construction (RIGHT disjunct).
    obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hdpos)
    exact Or.inr (exists_curve_through_point_curve_case hz hf g hg_inj hg_int)

end Semicontinuity.Baire
