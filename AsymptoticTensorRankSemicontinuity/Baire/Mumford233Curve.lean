/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Baire.Mumford233
import AsymptoticTensorRankSemicontinuity.Baire.Dictionary
import Mathlib.Topology.Sequences
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# Mumford (2.33) — curve-specific affine bridge

This file isolates the curve-specific algebraic/analytic bridges still needed
after the one-variable ingredients proved in `Baire/Mumford233.lean`.

Source:
* Mumford (2.32), projection refinement:
  Mumford, *Algebraic Geometry I*, Proposition (2.32), tex:1812-1834.
* Mumford (2.33), Steps I--III, especially Step I finite root avoidance and
  Step III lifting/compactness/subsequence conclusion:
  Mumford, *Algebraic Geometry I*, Theorem (2.33), proof Steps I--III, tex:1835-1877.

The declarations below separate the affine curve-density argument into named
Mumford (2.32) and (2.33) inputs:

* `mumford232_affine_fibre_isolating_parameter`: the exact affine analogue of
  Mumford (2.32), producing a one-coordinate finite parameter whose fibre over
  the chosen point is a singleton.
* `mumford233_geometric_sequence_from_good_base_sequence`: the Step III
  lying-over + norm-nonvanishing + boundedness + subsequence assembly once the
  Step I good base sequence (avoiding the roots of the one-variable norm `Nf`) is
  fixed, producing the actual convergent sequence of good complex points.
-/

noncomputable section

namespace Semicontinuity.Baire.Mumford233Curve

open Filter Topology MvPolynomial

variable {n : ℕ}

/-- Point evaluation on the coordinate ring of `zeroLocus ℂ Q`.

This is the affine point↔coordinate-ring dictionary used in Mumford (2.33),
Steps III (`tex:1871-1877`), and in the affine (2.32) fibre statement
(Mumford, *Algebraic Geometry I*, Proposition (2.32), tex:1812-1834): a point of the
curve evaluates regular functions on that curve. -/
def pointEval {Q : Ideal (MvPolynomial (Fin n) ℂ)}
    {z : Fin n → ℂ} (hzQ : z ∈ zeroLocus ℂ Q) :
    Semicontinuity.Baire.coordRing (zeroLocus ℂ Q) →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ (vanishingIdeal ℂ (zeroLocus ℂ Q)) (aeval z) (by
    intro p hp
    rw [mem_vanishingIdeal_iff] at hp
    exact hp z hzQ)

@[simp] theorem pointEval_mk {Q : Ideal (MvPolynomial (Fin n) ℂ)}
    {z : Fin n → ℂ} (hzQ : z ∈ zeroLocus ℂ Q) (p : MvPolynomial (Fin n) ℂ) :
    pointEval hzQ (Ideal.Quotient.mk _ p) = aeval z p := rfl

/-- The base value of a point under a one-coordinate parameter
`ψ : ℂ[t] → coordRing C`.

This is Mumford (2.33)'s affine `r = 1` base coordinate read at a complex point
(Mumford, *Algebraic Geometry I*, Theorem (2.33), proof Steps I--III, tex:1835-1877), with the
point-evaluation dictionary above. -/
def baseValue {Q : Ideal (MvPolynomial (Fin n) ℂ)}
    {z : Fin n → ℂ} (hzQ : z ∈ zeroLocus ℂ Q)
    (ψ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ]
      Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)) : ℂ :=
  pointEval hzQ (ψ (X (0 : Fin 1)))

/-- The composite `pointEval c ∘ ψ : ℂ[t] →ₐ[ℂ] ℂ` is evaluation of the single
variable at `baseValue c ψ`.  This is the linchpin connecting the algebra (the
parameter `ψ` and the coordinate ring `A`) to the geometry (the complex point `c`
and its base coordinate value) in Mumford (2.33), Step III
(Mumford, *Algebraic Geometry I*, proof of Theorem (2.33)). -/
theorem pointEval_comp_apply {Q : Ideal (MvPolynomial (Fin n) ℂ)}
    {c : Fin n → ℂ} (hcQ : c ∈ zeroLocus ℂ Q)
    (ψ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ]
      Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
    (r : MvPolynomial (Fin 1) ℂ) :
    pointEval hcQ (ψ r) = aeval (fun _ => baseValue hcQ ψ) r := by
  -- Both sides are `ℂ`-algebra homs `ℂ[t] → ℂ` agreeing on the single generator.
  have h := MvPolynomial.algHom_ext (f := (pointEval hcQ).comp ψ)
    (g := (aeval (fun _ => baseValue hcQ ψ) :
      MvPolynomial (Fin 1) ℂ →ₐ[ℂ] ℂ))
    (fun i => by
      fin_cases i
      simp [baseValue])
  exact congrArg (fun L => L r) h

/-- The single-variable specialization of an integral equation at a point.

If `x : A` satisfies the integral equation `p(x) = 0` over `R = ℂ[t]` (via the
`ψ`-algebra structure), then for any point `c ∈ C` the complex value
`pointEval c x` is a root of the complex polynomial obtained by evaluating the
`ℂ[t]`-coefficients of `p` at the base value `baseValue c ψ`.  This converts the
algebraic integral relation into the analytic monic relation that bounds the
coordinate (Mumford (2.33), Step III, `mumford.tex:1871`). -/
theorem isRoot_specialized_of_aeval_eq_zero
    {Q : Ideal (MvPolynomial (Fin n) ℂ)}
    {c : Fin n → ℂ} (hcQ : c ∈ zeroLocus ℂ Q)
    (ψ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ]
      Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
    (x : Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
    (p : Polynomial (MvPolynomial (Fin 1) ℂ))
    (hp : Polynomial.eval₂ ψ.toRingHom x p = 0) :
    (p.map (aeval (fun _ => baseValue hcQ ψ) :
        MvPolynomial (Fin 1) ℂ →ₐ[ℂ] ℂ).toRingHom).IsRoot (pointEval hcQ x) := by
  -- Apply the ring hom `pointEval c` to the integral relation `eval₂ ψ x p = 0`.
  have hcomp : ((pointEval hcQ).toRingHom.comp ψ.toRingHom)
      = (aeval (fun _ => baseValue hcQ ψ) :
          MvPolynomial (Fin 1) ℂ →ₐ[ℂ] ℂ).toRingHom := by
    refine RingHom.ext (fun r => ?_)
    exact pointEval_comp_apply hcQ ψ r
  have := Polynomial.hom_eval₂ p ψ.toRingHom (pointEval hcQ).toRingHom x
  rw [hp, map_zero, hcomp] at this
  -- `this : 0 = eval₂ (aeval ..) (pointEval c x) p`.
  rw [Polynomial.IsRoot, ← Polynomial.eval₂_eq_eval_map]
  exact this.symm

/-- **Uniform coordinate bound for lifts** (Mumford (2.33), Step III affine
boundedness, `mumford.tex:1871`).

If `x : A` is integral over `R = ℂ[t]` (via the `ψ`-algebra structure), then for
every radius `B` there is a radius `Rb` confining `pointEval c x` to
`closedBall 0 Rb` for every point `c ∈ C` whose base value lies in
`closedBall 0 B`.  The affine compactness input is a compact polydisc: each
integral coordinate of every lift over a bounded base
value is bounded.  The bound comes from `cauchyBound` of the specialized monic
polynomial, whose coefficients are continuous (hence bounded) functions of the
base value on the compact ball. -/
theorem exists_bound_pointEval_of_isIntegral
    {Q : Ideal (MvPolynomial (Fin n) ℂ)}
    (ψ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ]
      Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
    (x : Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
    (hx : RingHom.IsIntegralElem ψ.toRingHom x) (B : ℝ) :
    ∃ Rb : ℝ, ∀ (c : Fin n → ℂ) (hcQ : c ∈ zeroLocus ℂ Q),
      ‖baseValue hcQ ψ‖ ≤ B → ‖pointEval hcQ x‖ ≤ Rb := by
  classical
  -- Integral witness: a monic `p` with `eval₂ ψ x p = 0`.
  obtain ⟨p, hp_monic, hp_root⟩ := hx
  set d := p.natDegree with hd
  -- For each `k`, the coefficient `p.coeff k : ℂ[t]` is a bounded function of the
  -- base value `τ` on `closedBall 0 B`.
  have hcompact : IsCompact (Metric.closedBall (0 : ℂ) B) := isCompact_closedBall 0 B
  -- A uniform bound `M` on every coefficient over the ball.
  have hbound : ∀ k : ℕ, ∃ Ck : ℝ, ∀ τ ∈ Metric.closedBall (0 : ℂ) B,
      ‖aeval (fun _ => τ) (p.coeff k)‖ ≤ Ck := by
    intro k
    have hpi : Continuous (fun τ : ℂ => (fun _ : Fin 1 => τ)) := by
      exact continuous_pi (fun _ => continuous_id)
    have hcont : Continuous (fun τ : ℂ => aeval (fun _ => τ) (p.coeff k)) := by
      have h1 : Continuous (fun τ : ℂ => MvPolynomial.eval (fun _ => τ) (p.coeff k)) :=
        (MvPolynomial.continuous_eval (p.coeff k)).comp hpi
      simpa only [MvPolynomial.aeval_def, MvPolynomial.eval] using h1
    obtain ⟨Ck, hCk⟩ := hcompact.exists_bound_of_continuousOn hcont.continuousOn
    exact ⟨Ck, hCk⟩
  -- Take the (finite) maximum bound over `k < d` as an `ℝ≥0`, then add 1.
  choose C hC using hbound
  set M : NNReal := (Finset.range d).sup (fun k => Real.toNNReal (C k)) with hM
  refine ⟨(M : ℝ) + 1, ?_⟩
  intro c hcQ hcB
  -- The specialized monic complex polynomial.
  set g : Polynomial ℂ :=
    p.map (aeval (fun _ => baseValue hcQ ψ) :
      MvPolynomial (Fin 1) ℂ →ₐ[ℂ] ℂ).toRingHom with hg
  have hg_monic : g.Monic := hp_monic.map _
  have hg_ne : g ≠ 0 := hg_monic.ne_zero
  -- `pointEval c x` is a root of `g`.
  have hroot : g.IsRoot (pointEval hcQ x) :=
    isRoot_specialized_of_aeval_eq_zero hcQ ψ x p hp_root
  -- `cauchyBound g ≤ M + 1`: the sup of lower coefficients is `≤ M`.
  have hτB : baseValue hcQ ψ ∈ Metric.closedBall (0 : ℂ) B := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hcB
  have hcoeff : ∀ k ∈ Finset.range d, ‖g.coeff k‖₊ ≤ M := by
    intro k hk
    have hgk : g.coeff k = aeval (fun _ => baseValue hcQ ψ) (p.coeff k) := by
      rw [hg, Polynomial.coeff_map]; rfl
    have hle : ‖g.coeff k‖ ≤ C k := by
      rw [hgk]; exact hC k _ hτB
    have hkey : ‖g.coeff k‖₊ ≤ Real.toNNReal (C k) := by
      rw [← NNReal.coe_le_coe]
      simp only [coe_nnnorm, Real.coe_toNNReal']
      exact le_max_of_le_left hle
    exact le_trans hkey (Finset.le_sup (f := fun k => Real.toNNReal (C k)) hk)
  have hgdeg : g.natDegree = d := by rw [hg, hp_monic.natDegree_map]
  have hcb : Polynomial.cauchyBound g ≤ M + 1 := by
    rw [Polynomial.cauchyBound, hg_monic.leadingCoeff, nnnorm_one, div_one]
    gcongr
    rw [hgdeg]
    exact Finset.sup_le hcoeff
  -- Combine: `‖pointEval c x‖ < cauchyBound g ≤ M + 1`.
  have hlt : (‖pointEval hcQ x‖₊ : ℝ) < (Polynomial.cauchyBound g : ℝ) := by
    exact_mod_cast Polynomial.IsRoot.norm_lt_cauchyBound hg_ne hroot
  have : ‖pointEval hcQ x‖ < (M : ℝ) + 1 := by
    refine lt_of_lt_of_le ?_ (by exact_mod_cast hcb)
    simpa using hlt
  exact le_of_lt this

/-- The coordinate ring of an affine curve is finite over an integral
one-coordinate parameter.

This records the commutative algebra in Mumford (2.33), Steps I--III
(Mumford, *Algebraic Geometry I*, Theorem (2.33), proof Steps I--III, tex:1835-1877): once
`ψ : ℂ[t] → 𝒪(C)` is integral, the finitely generated `ℂ`-algebra `𝒪(C)` is a
finite `ℂ[t]`-module.  The proof uses Mathlib
`Algebra.FiniteType.of_restrictScalars_finiteType`
(`RingTheory/FiniteType.lean:74`) and `Algebra.IsIntegral.finite`
(`RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean:93`). -/
theorem coordRing_moduleFinite_of_integral
    {Q : Ideal (MvPolynomial (Fin n) ℂ)} [Q.IsPrime]
    (ψ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ]
      Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
    (hψ_int : ψ.toRingHom.IsIntegral) :
    letI : Algebra (MvPolynomial (Fin 1) ℂ)
        (Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)) := ψ.toAlgebra
    Module.Finite (MvPolynomial (Fin 1) ℂ)
      (Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)) := by
  let A := Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)
  let R := MvPolynomial (Fin 1) ℂ
  letI : Algebra R A := ψ.toAlgebra
  haveI hInt : Algebra.IsIntegral R A := by
    rw [Algebra.isIntegral_def]
    intro x
    exact hψ_int x
  haveI hFiniteTypeC : Algebra.FiniteType ℂ A := by
    exact Algebra.FiniteType.of_surjective
      (Ideal.Quotient.mkₐ ℂ (vanishingIdeal ℂ (zeroLocus ℂ Q)))
      (Ideal.Quotient.mkₐ_surjective ℂ (vanishingIdeal ℂ (zeroLocus ℂ Q)))
  haveI hFiniteTypeR : Algebra.FiniteType R A := by
    exact Algebra.FiniteType.of_restrictScalars_finiteType ℂ R A
  exact Algebra.IsIntegral.finite

/-- **Two-coordinate fibre isolation predicate** (Mumford (2.32), the hyperplane
`L₀*` excluding the `b_i`, `mumford.tex:1825-1834`; plus the extra coordinate
`mumford.tex:1837-1847`).

A pair consisting of the Noether base parameter `ψ : ℂ[t] ↪ 𝒪(C)` (the `g`-coordinate)
and a second regular function `s : 𝒪(C)` (the separating linear coordinate)
*isolates* `z` when no other point of the curve shares **both** the base value and
the `s`-value with `z`.  This is the affine analogue of `q⁻¹ q(a) = {a}` in (2.32):
the two-coordinate map `q = (g, s)` separates `z` from the rest of its base fibre. -/
def TwoCoordIso {Q : Ideal (MvPolynomial (Fin n) ℂ)}
    {z : Fin n → ℂ} (hzQ : z ∈ zeroLocus ℂ Q)
    (ψ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ]
      Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
    (s : Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)) : Prop :=
  ∀ c : Fin n → ℂ, ∀ hcQ : c ∈ zeroLocus ℂ Q,
    baseValue hcQ ψ = baseValue hzQ ψ →
    pointEval hcQ s = pointEval hzQ s → c = z

/-- The kernel of `pointEval c` recovers the point `c`: two points of the curve with
the same point-evaluation kernel are equal (each coordinate `c j` is read off as
`pointEval c (X j)`, and a `ℂ`-algebra hom to `ℂ` is determined by its kernel). -/
theorem pointEval_injOn_ker
    {Q : Ideal (MvPolynomial (Fin n) ℂ)}
    {c c' : Fin n → ℂ} (hcQ : c ∈ zeroLocus ℂ Q) (hcQ' : c' ∈ zeroLocus ℂ Q)
    (h : RingHom.ker (pointEval hcQ).toRingHom = RingHom.ker (pointEval hcQ').toRingHom) :
    c = c' := by
  funext j
  set xj : Semicontinuity.Baire.coordRing (zeroLocus ℂ Q) :=
    Ideal.Quotient.mk (vanishingIdeal ℂ (zeroLocus ℂ Q)) (X j) with hxj
  have hcj : pointEval hcQ xj = c j := by rw [hxj, pointEval_mk]; simp
  have hcj' : pointEval hcQ' xj = c' j := by rw [hxj, pointEval_mk]; simp
  have hsub : pointEval hcQ xj - pointEval hcQ' xj = 0 := by
    have hmem' : xj - algebraMap ℂ _ (pointEval hcQ' xj) ∈
        RingHom.ker (pointEval hcQ').toRingHom := by
      rw [RingHom.mem_ker]
      simp
    rw [← h, RingHom.mem_ker] at hmem'
    simpa using hmem'
  rw [hcj, hcj'] at hsub
  exact sub_eq_zero.mp hsub

/-- **Affine Mumford (2.32) fibre isolation.**

Given an affine irreducible curve `C = zeroLocus ℂ Q`, a point `z ∈ C`, and one
finite dominant parameter `ψ : ℂ[t] ↪ 𝒪(C)`, there is a second regular coordinate
`s ∈ 𝒪(C)` so that the pair `(ψ, s)` isolates `z` (`TwoCoordIso`).  This is the
affine version of Mumford's Proposition (2.32), where the projection is factored
through a centre chosen so that `q⁻¹ q(a) = {a}`
(Mumford, *Algebraic Geometry I*, Proposition (2.32), tex:1812-1834).

Construction (faithful to (2.32), tex:1825-1834): the base fibre
`F := {c ∈ C : baseValue c ψ = baseValue z ψ}` is finite (`𝒪(C)` is
module-finite over `ℂ[t]` via `ψ`, so the maximal ideals over `(t − g(z))` are
finite: `Algebra.QuasiFinite.finite_primesOver`).  The points `b ∈ F`, `b ≠ z`
are distinct in `ℂ^n`, so a **generic linear functional** `μ : (ℂ^n)*` has
`μ(b − z) ≠ 0` for all of them (`Module.exists_dual_forall_apply_ne_zero`); take
`s :=` the class of the linear polynomial `∑ μ_j X_j`.  Then `pointEval b s ≠
pointEval z s` for every `b ∈ F ∖ {z}`, which is exactly the hyperplane `L₀*`
through `a` and missing the `b_i`. -/
theorem mumford232_affine_fibre_isolating_parameter
    {Q : Ideal (MvPolynomial (Fin n) ℂ)} [Q.IsPrime]
    {z : Fin n → ℂ} (hzQ : z ∈ zeroLocus ℂ Q)
    (ψ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ]
      Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
    (hψ_inj : Function.Injective ψ) (hψ_int : ψ.toRingHom.IsIntegral) :
    ∃ s : Semicontinuity.Baire.coordRing (zeroLocus ℂ Q),
      TwoCoordIso hzQ ψ s := by
  classical
  have _ := hψ_inj
  let A := Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)
  let R := MvPolynomial (Fin 1) ℂ
  letI : Algebra R A := ψ.toAlgebra
  haveI : Algebra.IsIntegral R A := by
    rw [Algebra.isIntegral_def]; intro y; exact hψ_int y
  haveI : FaithfulSMul R A :=
    (faithfulSMul_iff_algebraMap_injective R A).mpr (by simpa using hψ_inj)
  haveI : Module.Finite R A :=
    coordRing_moduleFinite_of_integral (Q := Q) ψ hψ_int
  -- The fixed maximal ideal of `R = ℂ[t]` lying under the base point `z`.
  let m_z : Ideal R := vanishingIdeal ℂ ({fun _ : Fin 1 => baseValue hzQ ψ} : Set (Fin 1 → ℂ))
  haveI : m_z.IsMaximal := isMaximal_vanishingIdeal_singleton (fun _ : Fin 1 => baseValue hzQ ψ)
  haveI : m_z.IsPrime := inferInstance
  -- Step 1: the base fibre `F` (points of `C` over `m_z`) is finite.
  -- Inject it into `m_z.primesOver A` via `c ↦ ker(pointEval c)`.
  let F : Set (Fin n → ℂ) :=
    {c : Fin n → ℂ | ∃ hcQ : c ∈ zeroLocus ℂ Q, baseValue hcQ ψ = baseValue hzQ ψ}
  -- For `c ∈ F`, the kernel of `pointEval c` is a prime of `A` over `m_z`.
  have hker_mem : ∀ c (hcQ : c ∈ zeroLocus ℂ Q), baseValue hcQ ψ = baseValue hzQ ψ →
      RingHom.ker (pointEval hcQ).toRingHom ∈ m_z.primesOver A := by
    intro c hcQ hbase
    refine ⟨RingHom.ker_isPrime _, ?_⟩
    -- lies over `m_z`: `(ker (pointEval c)).under R = m_z`.
    constructor
    apply le_antisymm
    · intro p hp
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change pointEval hcQ (ψ p) = 0
      rw [pointEval_comp_apply hcQ ψ p, hbase]
      rwa [MvPolynomial.mem_vanishingIdeal_singleton_iff] at hp
    · intro p hp
      rw [Ideal.mem_comap, RingHom.mem_ker] at hp
      change pointEval hcQ (ψ p) = 0 at hp
      rw [pointEval_comp_apply hcQ ψ p, hbase] at hp
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      exact hp
  -- The map `Φ : F → m_z.primesOver A`, `c ↦ ker(pointEval c)`, is injective on `F`.
  let Φ : (Fin n → ℂ) → Ideal A := fun c =>
    if hcQ : c ∈ zeroLocus ℂ Q then RingHom.ker (pointEval hcQ).toRingHom else ⊥
  have hΦ_image : Φ '' F ⊆ m_z.primesOver A := by
    rintro _ ⟨c, ⟨hcQ, hbase⟩, rfl⟩
    have : Φ c = RingHom.ker (pointEval hcQ).toRingHom := by simp only [Φ, dif_pos hcQ]
    rw [this]
    exact hker_mem c hcQ hbase
  have hΦ_injOn : Set.InjOn Φ F := by
    rintro a ⟨haQ, hab⟩ b ⟨hbQ, hbb⟩ hΦeq
    have hΦa : Φ a = RingHom.ker (pointEval haQ).toRingHom := by simp only [Φ, dif_pos haQ]
    have hΦb : Φ b = RingHom.ker (pointEval hbQ).toRingHom := by simp only [Φ, dif_pos hbQ]
    rw [hΦa, hΦb] at hΦeq
    exact pointEval_injOn_ker haQ hbQ hΦeq
  have hF_finite : F.Finite := by
    have hfin : (m_z.primesOver A).Finite := Algebra.QuasiFinite.finite_primesOver m_z
    exact Set.Finite.of_finite_image (hfin.subset hΦ_image) hΦ_injOn
  -- Step 2: generic linear functional separating `z` from `F ∖ {z}`.
  -- The points `b ∈ F`, `b ≠ z` give nonzero vectors `b − z`.
  set Fbad : Set (Fin n → ℂ) := F \ {z} with hFbad
  have hFbad_finite : Fbad.Finite := hF_finite.subset Set.diff_subset
  haveI : Finite Fbad := hFbad_finite.to_subtype
  -- Index the bad points by the finite type `Fbad`; each `b − z ≠ 0`.
  obtain ⟨μ, hμ⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℂ) (M := Fin n → ℂ)
    (ι := Fbad) (v := fun b => (b : Fin n → ℂ) - z) (by
      rintro ⟨b, hbF, hbz⟩
      simp only [ne_eq, sub_eq_zero]
      intro h
      exact hbz (by simpa using h))
  -- The linear polynomial `L := ∑ j, C (μ (e_j)) * X j` realizing `μ`.
  set L : MvPolynomial (Fin n) ℂ :=
    ∑ j : Fin n, C (μ (fun k => if j = k then 1 else 0)) * X j with hL
  set s : A := Ideal.Quotient.mk (vanishingIdeal ℂ (zeroLocus ℂ Q)) L with hs
  -- `pointEval c s = μ c` for every point `c`.
  have hs_eval : ∀ c (hcQ : c ∈ zeroLocus ℂ Q), pointEval hcQ s = μ c := by
    intro c hcQ
    rw [hs, pointEval_mk, hL]
    rw [LinearMap.pi_apply_eq_sum_univ μ c]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, aeval_C, aeval_X, mul_comm, smul_eq_mul, Algebra.algebraMap_self,
      RingHom.id_apply]
  refine ⟨s, ?_⟩
  -- Prove `TwoCoordIso`: if `baseValue c ψ = baseValue z ψ` and `pointEval c s =
  -- pointEval z s`, then `c = z`.
  intro c hcQ _hbase hs_c
  have hcF : c ∈ F := ⟨hcQ, _hbase⟩
  by_contra hcz
  -- Then `c ∈ Fbad`, so `μ (c − z) ≠ 0`, contradicting `pointEval c s = pointEval z s`.
  have hcbad : c ∈ Fbad := ⟨hcF, by simpa [Set.mem_singleton_iff] using hcz⟩
  have hne := hμ ⟨c, hcbad⟩
  apply hne
  have : μ c = μ z := by
    rw [← hs_eval c hcQ, ← hs_eval z hzQ]; exact hs_c
  simp only [map_sub]
  rw [this, sub_self]

/-- If a polynomial is nonzero at some point of `zeroLocus ℂ Q`, then its class in
the coordinate ring of that zero locus is nonzero.

This is the algebraic starting point for Mumford (2.33), Step I
(`mumford.tex:1849`): the function being
nonzero somewhere on the curve is what must feed the nonzero one-variable norm
polynomial on the base. -/
theorem coordRing_mk_ne_zero_of_exists_aeval_ne_zero
    {Q : Ideal (MvPolynomial (Fin n) ℂ)} {f : MvPolynomial (Fin n) ℂ}
    (h : ∃ x ∈ zeroLocus ℂ Q, aeval x f ≠ 0) :
    ((Ideal.Quotient.mkₐ ℂ (vanishingIdeal ℂ (zeroLocus ℂ Q))) f :
      Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)) ≠ 0 := by
  intro hf
  obtain ⟨x, hxQ, hxf⟩ := h
  have hfmem : f ∈ vanishingIdeal ℂ (zeroLocus ℂ Q) := by
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      (by simpa [Ideal.Quotient.mkₐ_eq_mk] using hf)
  rw [mem_vanishingIdeal_iff] at hfmem
  exact hxf (hfmem x hxQ)

/-- Nonzero elements of the coordinate ring have nonzero algebra norm once the
finite `ℂ[t]`-module is free.

This is the norm step in Mumford (2.33), Step I
(`mumford.tex:1849-1855`), in the affine
finite-map formulation.  The final freeness input is the standard finite
torsion-free module over the PID `ℂ[X] ≃ ℂ[t]`; with it, Mathlib
`Algebra.norm_ne_zero_iff` (`RingTheory/Norm/Basic.lean:112`) gives the result
because `coordRing (zeroLocus ℂ Q)` is a domain by
`Semicontinuity.Baire.isDomain_coordRing_zeroLocus`. -/
theorem coordRing_norm_ne_zero_of_ne_zero
    {Q : Ideal (MvPolynomial (Fin n) ℂ)} [Q.IsPrime]
    (ψ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ]
      Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
    (a : Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)) (ha : a ≠ 0) :
    letI : Algebra (MvPolynomial (Fin 1) ℂ)
        (Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)) := ψ.toAlgebra
    Module.Free (MvPolynomial (Fin 1) ℂ)
        (Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)) →
    Module.Finite (MvPolynomial (Fin 1) ℂ)
        (Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)) →
    Algebra.norm (MvPolynomial (Fin 1) ℂ) a ≠ 0 := by
  let A := Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)
  let R := MvPolynomial (Fin 1) ℂ
  letI : Algebra R A := ψ.toAlgebra
  intro hfree hfinite
  haveI : Module.Free R A := hfree
  haveI : Module.Finite R A := hfinite
  haveI : IsDomain A := Semicontinuity.Baire.isDomain_coordRing_zeroLocus Q
  exact (Algebra.norm_ne_zero_iff (R := R) (S := A)).mpr ha

/-- Transport `IsPrincipalIdealRing` across a ring equivalence.

This is the small commutative-algebra bridge used in Mumford (2.33), Steps
I--III (Mumford, *Algebraic Geometry I*, Theorem (2.33), proof Steps I--III, tex:1835-1877), to
replace the base `MvPolynomial (Fin 1) ℂ` by the PID `ℂ[X]`.  The proof is
ideal transport along `Ideal.map`/`Ideal.comap` for a `RingEquiv`
(`Mathlib/RingTheory/Ideal/Maps.lean:468-486`). -/
theorem isPrincipalIdealRing_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    [IsPrincipalIdealRing S] : IsPrincipalIdealRing R where
  principal I := by
    obtain ⟨s, hs⟩ := IsPrincipalIdealRing.principal (I.map e)
    refine ⟨⟨e.symm s, ?_⟩⟩
    ext x
    rw [← Ideal.apply_mem_of_equiv_iff (I := I) (f := e) (x := x), hs]
    change e x ∈ Ideal.span ({s} : Set S) ↔
      x ∈ Ideal.span ({e.symm s} : Set R)
    rw [Ideal.mem_span_singleton', Ideal.mem_span_singleton']
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨e.symm a, ?_⟩
      apply e.injective
      rw [map_mul, e.apply_symm_apply, e.apply_symm_apply]
      exact ha
    · rintro ⟨a, ha⟩
      refine ⟨e a, ?_⟩
      rw [← e.apply_symm_apply s, ← map_mul, ha]

/-- The affine one-coordinate base `ℂ[t] = MvPolynomial (Fin 1) ℂ` is a PID.

This is for Mumford (2.33), affine `r = 1`
(Mumford, *Algebraic Geometry I*, Theorem (2.33), proof Steps I--III, tex:1835-1877): identify
`MvPolynomial (Fin 1) ℂ` with `Polynomial ℂ` using
`MvPolynomial.renameEquiv` and `MvPolynomial.pUnitAlgEquiv`, then transport the
PID instance from `Polynomial ℂ`. -/
theorem mvPolynomial_fin_one_isPrincipalIdealRing :
    IsPrincipalIdealRing (MvPolynomial (Fin 1) ℂ) := by
  let eFin : Fin 1 ≃ PUnit.{1} := Equiv.punitOfNonemptyOfSubsingleton
  let e : MvPolynomial (Fin 1) ℂ ≃ₐ[ℂ] Polynomial ℂ :=
    (MvPolynomial.renameEquiv ℂ eFin).trans (MvPolynomial.pUnitAlgEquiv ℂ)
  exact isPrincipalIdealRing_of_ringEquiv e.toRingEquiv

/-- The standard affine-coordinate equivalence `ℂ[t] ≃ ℂ[X]` for the
one-variable base in Mumford (2.33), Step I
(Mumford, *Algebraic Geometry I*, Theorem (2.33), Step I, `tex:1849`).

This is the same equivalence used in `mvPolynomial_fin_one_isPrincipalIdealRing`;
it lets the nonzero algebra norm over `MvPolynomial (Fin 1) ℂ` be read as an
ordinary complex polynomial with finitely many zeros. -/
def mvPolynomialFinOneAlgEquivPolynomial :
    MvPolynomial (Fin 1) ℂ ≃ₐ[ℂ] Polynomial ℂ :=
  let eFin : Fin 1 ≃ PUnit.{1} := Equiv.punitOfNonemptyOfSubsingleton
  (MvPolynomial.renameEquiv ℂ eFin).trans (MvPolynomial.pUnitAlgEquiv ℂ)

/-- A finite coordinate ring over an injective one-coordinate parameter is free.

This is the finite-module algebra used in Mumford (2.33), affine `r = 1`
(Mumford, *Algebraic Geometry I*, Theorem (2.33), proof Steps I--III, tex:1835-1877): after the PID
transport `MvPolynomial (Fin 1) ℂ ≃ ℂ[X]`, the finite module is torsion-free
because the coordinate ring is a domain and the algebra map is injective
(`NoZeroSMulDivisors.iff_faithfulSMul`, `Mathlib/Algebra/Algebra/Basic.lean:
385-390`).  Mathlib then supplies
`Module.free_of_finite_type_torsion_free'`
(`Mathlib/LinearAlgebra/FreeModule/PID.lean:386`). -/
theorem coordRing_moduleFree_of_finite
    {Q : Ideal (MvPolynomial (Fin n) ℂ)} [Q.IsPrime]
    (ψ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ]
      Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
    (hψ_inj : Function.Injective ψ)
    (hψ_finite :
      letI : Algebra (MvPolynomial (Fin 1) ℂ)
          (Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)) := ψ.toAlgebra
      Module.Finite (MvPolynomial (Fin 1) ℂ)
        (Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))) :
    letI : Algebra (MvPolynomial (Fin 1) ℂ)
        (Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)) := ψ.toAlgebra
    Module.Free (MvPolynomial (Fin 1) ℂ)
        (Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)) := by
  let A := Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)
  let R := MvPolynomial (Fin 1) ℂ
  letI : Algebra R A := ψ.toAlgebra
  haveI : Module.Finite R A := hψ_finite
  haveI : IsDomain R := inferInstance
  haveI : IsPrincipalIdealRing R := mvPolynomial_fin_one_isPrincipalIdealRing
  haveI : IsDomain A := Semicontinuity.Baire.isDomain_coordRing_zeroLocus Q
  haveI : FaithfulSMul R A := by
    rw [faithfulSMul_iff_algebraMap_injective]
    simpa using hψ_inj
  haveI : Module.IsTorsionFree R A :=
    (NoZeroSMulDivisors.iff_faithfulSMul (R := R) (A := A)).mpr inferInstance
  infer_instance

/-- The already-good point case of Mumford (2.33), Step III
(`mumford.tex:1871-1877`): if the target
point itself lies in the nonvanishing locus, the constant sequence proves the
required sequential closure statement. -/
theorem mumford233_constant_approximating_sequence
    {Q : Ideal (MvPolynomial (Fin n) ℂ)}
    {z : Fin n → ℂ} (hzQ : z ∈ zeroLocus ℂ Q)
    {f : MvPolynomial (Fin n) ℂ} (hzf : aeval z f ≠ 0) :
    ∃ u : ℕ → Fin n → ℂ,
      (∀ i, u i ∈ zeroLocus ℂ Q ∩ {x : Fin n → ℂ | aeval x f ≠ 0}) ∧
      Tendsto u atTop (𝓝 z) := by
  refine ⟨fun _ => z, ?_, tendsto_const_nhds⟩
  intro _i
  exact ⟨hzQ, hzf⟩

/-- **Elementary norm-divisibility** for a free finite algebra (no integral
closure needed).  For `x : A` with `A` free and finite over `R`, the element `x`
divides `algebraMap R A (Algebra.norm R x)`.

This is the load-bearing algebraic link in Mumford (2.33), Step II--III
(`mumford.tex:1855-1869`): the norm of `f`
is, up to a unit, the product over the fibre, so `f` divides (the image of) its
norm; hence wherever the norm of `f` is nonzero, `f` itself is nonzero.  The proof
is Cayley--Hamilton via the adjugate: `norm x = det (lmul x)`, and
`adjugate (matrix) * matrix = det • 1`, so `det • 1` lies in the range of
multiplication by `x`, i.e. is an `A`-multiple of `x`. -/
theorem algebra_dvd_algebraMap_norm
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A] (x : A) :
    x ∣ algebraMap R A (Algebra.norm R x) := by
  classical
  let ι := Module.Free.ChooseBasisIndex R A
  let b : Module.Basis ι R A := Module.Free.chooseBasis R A
  -- The matrix of left multiplication by `x`, and its adjugate.
  let Mx : Matrix ι ι R := Algebra.leftMulMatrix b x
  -- Cayley–Hamilton via the adjugate: `Mx * adjugate Mx = det Mx • 1`.
  have hadj : Mx * Mx.adjugate = Mx.det • (1 : Matrix ι ι R) := Matrix.mul_adjugate Mx
  -- `Mx` is the matrix of `mulLeft x`.
  have hMx : Mx = (LinearMap.toMatrix b b) (LinearMap.mulLeft R x) :=
    (Algebra.toMatrix_lmul_eq b x).symm
  -- Translate the matrix identity into linear maps via `Matrix.toLin b b`.
  -- Let `g` be the endomorphism of `A` represented by `adjugate Mx`.
  let g : A →ₗ[R] A := Matrix.toLin b b Mx.adjugate
  -- `mulLeft x ∘ g = Mx.det • id`.
  have hcomp : (LinearMap.mulLeft R x).comp g = Mx.det • LinearMap.id := by
    have h1 : Matrix.toLin b b (Mx * Mx.adjugate)
        = (Matrix.toLin b b Mx).comp (Matrix.toLin b b Mx.adjugate) :=
      Matrix.toLin_mul b b b Mx Mx.adjugate
    have h2 : Matrix.toLin b b Mx = LinearMap.mulLeft R x := by
      rw [hMx, Matrix.toLin_toMatrix]
    have h3 : Matrix.toLin b b (Mx.det • (1 : Matrix ι ι R))
        = Mx.det • LinearMap.id := by
      rw [map_smul, Matrix.toLin_one]
    rw [hadj] at h1
    rw [h3] at h1
    rw [h2] at h1
    exact h1.symm
  -- Evaluate at `1 : A`.
  refine ⟨g 1, ?_⟩
  have hval := congrArg (fun L : A →ₗ[R] A => L 1) hcomp
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq] at hval
  -- `x * g 1 = Mx.det • 1 = algebraMap R A (norm x)`.
  rw [hval]
  have hnorm : Mx.det = Algebra.norm R x := (Algebra.norm_eq_matrix_det b x).symm
  rw [hnorm, Algebra.smul_def, mul_one]

private theorem eval_mvPolynomialFinOneAlgEquivPolynomial
    (p : MvPolynomial (Fin 1) ℂ) (τ : ℂ) :
    (mvPolynomialFinOneAlgEquivPolynomial p).eval τ =
      aeval (fun _ : Fin 1 => τ) p := by
  have h := MvPolynomial.algHom_ext
    (f := (Polynomial.aeval τ).comp mvPolynomialFinOneAlgEquivPolynomial.toAlgHom)
    (g := (aeval (fun _ : Fin 1 => τ) : MvPolynomial (Fin 1) ℂ →ₐ[ℂ] ℂ))
    (fun i => by
      fin_cases i
      simp [mvPolynomialFinOneAlgEquivPolynomial])
  exact congrArg (fun F : MvPolynomial (Fin 1) ℂ →ₐ[ℂ] ℂ => F p) h

private theorem isClosed_zeroLocus_mvPolynomial
    (Q : Ideal (MvPolynomial (Fin n) ℂ)) :
    IsClosed (zeroLocus ℂ Q : Set (Fin n → ℂ)) := by
  rw [zeroLocus]
  simp only [Set.setOf_forall]
  refine isClosed_iInter (fun p => isClosed_iInter fun hp => ?_)
  have hcont : Continuous (fun x : Fin n → ℂ => aeval x p) := by
    simpa only [MvPolynomial.aeval_def, MvPolynomial.eval] using
      (MvPolynomial.continuous_eval p)
  exact isClosed_eq hcont continuous_const

private theorem exists_norm_bound_of_tendsto
    {a : ℂ} {t : ℕ → ℂ} (ht : Tendsto t atTop (𝓝 a)) :
    ∃ B : ℝ, ∀ i, ‖t i‖ ≤ B := by
  have hbdd : Bornology.IsBounded (Set.range t) :=
    Metric.isBounded_range_of_tendsto t ht
  obtain ⟨B, hB⟩ := hbdd.exists_norm_le
  exact ⟨B, fun i => hB (t i) ⟨i, rfl⟩⟩

/-- **Image-curve monic generator** (Mumford (2.33), Step II,
tex:1847-1856).

For the finite integral curve algebra `A` over `R = ℂ[t]` and a second regular
coordinate `s ∈ A`, the image of `C → 𝔸²`, `c ↦ (g(c), s(c))`, is cut out by a
single equation monic in the `s`-coordinate.  Algebraically, the kernel of
`R[Y] → A`, `Y ↦ s`, is generated by a monic polynomial `P_s`; roots of the
specialization `P_s(t_i,Y)` are precisely image characters of the intermediate
algebra, and lying-over to `A` gives curve points above them.  The final conjunct
packages the Step II root choice `Y_i → s(z)` and the Step III lying-over lift
used below: after excluding the norm roots of `f`, the chosen lifts satisfy both
`baseValue = t_i` and `pointEval s = Y_i`, with `f` nonzero.

This is the UFD/height-one-principal plus lying-over image-point fact used in the
two-coordinate Step II--III bridge. -/
theorem image_curve_monic_generator
    {Q : Ideal (MvPolynomial (Fin n) ℂ)} [Q.IsPrime]
    {z : Fin n → ℂ} (hzQ : z ∈ zeroLocus ℂ Q)
    {f : MvPolynomial (Fin n) ℂ}
    (hmeet : (zeroLocus ℂ Q ∩
        {x : Fin n → ℂ | aeval x f ≠ 0}).Nonempty)
    (ψ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ]
      Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
    (hψ_inj : Function.Injective ψ) (hψ_int : ψ.toRingHom.IsIntegral)
    (s : Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
    (Nf : MvPolynomial (Fin 1) ℂ)
    (hNf :
      letI : Algebra (MvPolynomial (Fin 1) ℂ)
          (Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)) := ψ.toAlgebra
      Nf = Algebra.norm (MvPolynomial (Fin 1) ℂ)
        (((Ideal.Quotient.mkₐ ℂ (vanishingIdeal ℂ (zeroLocus ℂ Q))) f :
          Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))))
    (t : ℕ → ℂ)
    (ht_tend : Tendsto t atTop (𝓝 (baseValue hzQ ψ)))
    (ht_good : ∀ i, (mvPolynomialFinOneAlgEquivPolynomial Nf).eval (t i) ≠ 0) :
    ∃ P_s : Polynomial (MvPolynomial (Fin 1) ℂ),
      P_s.Monic ∧
      Polynomial.eval₂ ψ.toRingHom s P_s = 0 ∧
      ∃ Y : ℕ → ℂ, ∃ c : ℕ → Fin n → ℂ,
        ∃ hcQ : ∀ i, c i ∈ zeroLocus ℂ Q,
        (∀ i, baseValue (hcQ i) ψ = t i) ∧
        (∀ i, pointEval (hcQ i) s = Y i) ∧
        (∀ i, aeval (c i) f ≠ 0) ∧
        Tendsto Y atTop (𝓝 (pointEval hzQ s)) := by
  classical
  have _ := hmeet
  -- ===== Algebra setup =====
  let A := Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)
  let R := MvPolynomial (Fin 1) ℂ
  letI : Algebra R A := ψ.toAlgebra
  haveI : Algebra.IsIntegral R A := by
    rw [Algebra.isIntegral_def]
    intro y
    exact hψ_int y
  haveI : FaithfulSMul R A :=
    (faithfulSMul_iff_algebraMap_injective R A).mpr (by simpa using hψ_inj)
  haveI : IsDomain A := Semicontinuity.Baire.isDomain_coordRing_zeroLocus Q
  haveI : IsDomain R := inferInstance
  haveI : IsPrincipalIdealRing R := mvPolynomial_fin_one_isPrincipalIdealRing
  haveI : IsIntegrallyClosed R := inferInstance
  haveI : Module.IsTorsionFree R A :=
    (NoZeroSMulDivisors.iff_faithfulSMul (R := R) (A := A)).mpr inferInstance
  -- `s` is integral over `R` (via the algebra structure from `ψ`).
  have hs_int : IsIntegral R s := Algebra.IsIntegral.isIntegral s
  -- ===== the monic minimal polynomial =====
  set P_s : Polynomial R := minpoly R s with hP_s_def
  have hP_s_monic : P_s.Monic := minpoly.monic hs_int
  have hP_s_aeval : (Polynomial.aeval s) P_s = 0 := minpoly.aeval R s
  -- `eval₂ ψ.toRingHom s P_s = aeval s P_s = 0` (the algebra map is `ψ`).
  have hP_s_eval : Polynomial.eval₂ ψ.toRingHom s P_s = 0 := by
    have halg : (algebraMap R A) = ψ.toRingHom := rfl
    rw [← halg]
    have := hP_s_aeval
    rwa [Polynomial.aeval_def] at this
  refine ⟨P_s, hP_s_monic, hP_s_eval, ?_⟩
  -- ===== root selection `Y_i → s(z)` (Mumford β_i → 0, tex:1857-1869) =====
  -- Abbreviations: evaluation of the `R`-coefficients at a complex base value.
  set a : ℂ := baseValue hzQ ψ with ha_def
  set w : ℂ := pointEval hzQ s with hw_def
  -- The base value `a` is a root of `P_z`, witnessed by `s(z) = w`.
  have hw_root_Pz :
      (P_s.map (aeval (fun _ : Fin 1 => a) :
        R →ₐ[ℂ] ℂ).toRingHom).IsRoot w := by
    have := isRoot_specialized_of_aeval_eq_zero hzQ ψ s P_s hP_s_eval
    simpa [a, w] using this
  -- The degree `d := natDegree P_s` is positive.
  have hd_pos : 0 < P_s.natDegree := minpoly.natDegree_pos hs_int
  -- The continuous function `F τ = (P_s.map (eval at τ)).eval w`.
  set F : ℂ → ℂ := fun τ =>
    Polynomial.eval w (P_s.map (aeval (fun _ : Fin 1 => τ) : R →ₐ[ℂ] ℂ).toRingHom)
    with hF_def
  have hF_cont : Continuous F := by
    -- `F τ = ∑_{k ∈ support} (aeval (fun _ => τ) (P_s.coeff k)) * w ^ k`.
    have hFsum : F = fun τ => ∑ k ∈ P_s.support,
        (aeval (fun _ : Fin 1 => τ) (P_s.coeff k)) * w ^ k := by
      funext τ
      simp only [hF_def, Polynomial.eval_map, Polynomial.eval₂_eq_sum,
        Polynomial.sum]
      rfl
    rw [hFsum]
    refine continuous_finset_sum _ (fun k _ => ?_)
    refine Continuous.mul ?_ continuous_const
    -- `τ ↦ aeval (fun _ => τ) (P_s.coeff k)` is continuous.
    have hcoeff : Continuous (fun τ : ℂ =>
        aeval (fun _ : Fin 1 => τ) (P_s.coeff k)) := by
      have : Continuous (fun τ : ℂ => (fun _ : Fin 1 => τ)) :=
        continuous_pi (fun _ => continuous_id)
      simpa only [MvPolynomial.aeval_def, MvPolynomial.eval] using
        ((MvPolynomial.continuous_eval (P_s.coeff k)).comp this)
    exact hcoeff
  have hFa : F a = 0 := hw_root_Pz
  -- `F (t i) → F a = 0`.
  have hF_tend : Tendsto (fun i => F (t i)) atTop (𝓝 (0 : ℂ)) := by
    have := (hF_cont.tendsto a).comp ht_tend
    rw [hFa] at this
    simpa [Function.comp_def] using this
  -- For each `i`, the specialized monic polynomial `Pi i` and the shifted one.
  set Pi : ℕ → Polynomial ℂ := fun i =>
    P_s.map (aeval (fun _ : Fin 1 => t i) : R →ₐ[ℂ] ℂ).toRingHom with hPi_def
  have hPi_monic : ∀ i, (Pi i).Monic := fun i => hP_s_monic.map _
  have hPi_deg : ∀ i, (Pi i).natDegree = P_s.natDegree := fun i =>
    hP_s_monic.natDegree_map _
  -- The shifted polynomial `Qi i := (Pi i).comp (X + C w)`.
  set Qi : ℕ → Polynomial ℂ := fun i => (Pi i).comp (Polynomial.X + Polynomial.C w)
    with hQi_def
  have hQi_monic : ∀ i, (Qi i).Monic := by
    intro i
    exact (hPi_monic i).comp_X_add_C w
  have hQi_deg : ∀ i, (Qi i).natDegree = P_s.natDegree := by
    intro i
    rw [hQi_def, Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
    exact hPi_deg i
  -- Constant term of `Qi i` is `(Pi i).eval w = F (t i)`.
  have hQi_const : ∀ i, (Qi i).coeff 0 = F (t i) := by
    intro i
    have hcoeff : (Qi i).coeff 0 = (Pi i).eval w := by
      rw [hQi_def]
      have h0 := Polynomial.eval_comp (p := Pi i) (q := Polynomial.X + Polynomial.C w)
        (x := 0)
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
        zero_add] at h0
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact h0
    rw [hcoeff]
  -- Apply the Vieta small-root lemma to each `Qi i`.
  have hβ : ∀ i, ∃ β : ℂ, (Qi i).IsRoot β ∧
      ‖β‖ ^ P_s.natDegree ≤ ‖F (t i)‖ := by
    intro i
    have hQpos : 0 < (Qi i).natDegree := by rw [hQi_deg i]; exact hd_pos
    obtain ⟨β, hβroot, hβbound⟩ :=
      Semicontinuity.Baire.Mumford233.exists_root_pow_le_prod_norm hQpos
    refine ⟨β, hβroot, ?_⟩
    rw [hQi_deg i] at hβbound
    rw [(hQi_monic i).leadingCoeff, div_one, hQi_const i] at hβbound
    exact hβbound
  choose β hβroot hβbound using hβ
  -- `β_i → 0`, hence `Y_i := β_i + w → w`.
  have hβ_tend : Tendsto β atTop (𝓝 (0 : ℂ)) := by
    -- From `‖β i‖^d ≤ ‖F (t i)‖ → 0` and `d > 0`.
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hpow : Tendsto (fun i => ‖β i‖ ^ P_s.natDegree) atTop (𝓝 0) := by
      have hbd : Tendsto (fun i => ‖F (t i)‖) atTop (𝓝 0) := by
        simpa using (hF_tend.norm)
      refine squeeze_zero (fun i => by positivity) hβbound hbd
    -- Take the `1/d`-th power: `(‖β i‖^d)^(1/d) = ‖β i‖ → 0`.
    have hdne : ((P_s.natDegree : ℝ)) ≠ 0 := by
      have : (0 : ℝ) < P_s.natDegree := by exact_mod_cast hd_pos
      exact this.ne'
    have hrpow : Tendsto (fun i => (‖β i‖ ^ P_s.natDegree) ^
        ((P_s.natDegree : ℝ)⁻¹)) atTop (𝓝 ((0 : ℝ) ^ ((P_s.natDegree : ℝ)⁻¹))) := by
      refine (hpow.rpow tendsto_const_nhds (Or.inr ?_))
      positivity
    rw [Real.zero_rpow (by simpa using hdne)] at hrpow
    have hsimp : (fun i => (‖β i‖ ^ P_s.natDegree) ^ ((P_s.natDegree : ℝ)⁻¹))
        = fun i => ‖β i‖ := by
      funext i
      rw [← Real.rpow_natCast (‖β i‖) P_s.natDegree,
        ← Real.rpow_mul (by positivity), mul_inv_cancel₀ hdne, Real.rpow_one]
    rwa [hsimp] at hrpow
  set Y : ℕ → ℂ := fun i => β i + w with hY_def
  have hY_root : ∀ i, (Pi i).IsRoot (Y i) := by
    intro i
    have := hβroot i
    rw [hQi_def, Polynomial.IsRoot, Polynomial.eval_comp] at this
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at this
    rw [Polynomial.IsRoot, hY_def]
    exact this
  have hY_tend : Tendsto Y atTop (𝓝 w) := by
    rw [hY_def]
    have := hβ_tend.add (tendsto_const_nhds (x := w))
    simpa using this
  -- ===== lying-over from the image curve and norm avoidance =====
  have ringHom_eq_of_ker_eq_of_C {B₀ : Type} [CommRing B₀] [Algebra R B₀]
      (φ₁ φ₂ : B₀ →+* ℂ)
      (hker : RingHom.ker φ₁ = RingHom.ker φ₂) :
      (∀ z : ℂ, φ₁ (algebraMap R B₀ (C z)) = z) →
      (∀ z : ℂ, φ₂ (algebraMap R B₀ (C z)) = z) →
      φ₁ = φ₂ := by
    intro hC₁ hC₂
    ext x
    have hx₂ :
        x - algebraMap R B₀ (C (φ₂ x)) ∈ RingHom.ker φ₂ := by
      rw [RingHom.mem_ker]
      simp [map_sub, hC₂]
    have hx₁ :
        x - algebraMap R B₀ (C (φ₂ x)) ∈ RingHom.ker φ₁ := by
      rw [hker]
      exact hx₂
    rw [RingHom.mem_ker] at hx₁
    simpa [map_sub, hC₁, sub_eq_zero] using hx₁
  have h_lift : ∀ i, ∃ c : Fin n → ℂ, ∃ hcQ : c ∈ zeroLocus ℂ Q,
      baseValue hcQ ψ = t i ∧ pointEval hcQ s = Y i ∧ aeval c f ≠ 0 := by
    intro i
    let B : Subalgebra R A := Algebra.adjoin R ({s} : Set A)
    let sB : B := ⟨s, SetLike.mem_coe.1 <| Algebra.subset_adjoin <| Set.mem_singleton s⟩
    let φ : R →ₐ[ℂ] ℂ := aeval (fun _ : Fin 1 => t i)
    have hroot_eval₂ : Polynomial.eval₂ φ.toRingHom (Y i) P_s = 0 := by
      have hroot := hY_root i
      rw [Polynomial.IsRoot] at hroot
      rw [hPi_def, Polynomial.eval_map] at hroot
      simpa [φ] using hroot
    let χ₀ : AdjoinRoot P_s →+* ℂ :=
      AdjoinRoot.lift φ.toRingHom (Y i) hroot_eval₂
    let eR : AdjoinRoot P_s ≃ₐ[R] B := minpoly.equivAdjoin hs_int
    let χ : B →+* ℂ := χ₀.comp eR.symm.toRingHom
    have hχ_C (z : ℂ) : χ (algebraMap R B (C z)) = z := by
      change χ₀ (eR.symm (algebraMap R B (C z))) = z
      have hsymm :
          eR.symm (algebraMap R B (C z)) =
            algebraMap R (AdjoinRoot P_s) (C z) := by
        exact eR.symm.toAlgHom.commutes (C z)
      rw [hsymm]
      have hlift :=
        (AdjoinRoot.lift_of (f := P_s) (i := φ.toRingHom) (a := Y i)
          hroot_eval₂ (x := C z))
      change χ₀ ((AdjoinRoot.of P_s) (C z)) = z
      rw [hlift]
      change φ (C z) = z
      exact φ.commutes z
    have hχ_surj : Function.Surjective χ := by
      intro z
      exact ⟨algebraMap R B (C z), hχ_C z⟩
    let m : Ideal B := RingHom.ker χ
    haveI hm_max : m.IsMaximal := RingHom.ker_isMaximal_of_surjective χ hχ_surj
    letI : Algebra B A :=
      { algebraMap := B.val.toRingHom
        commutes' := fun b x => by exact mul_comm (b : A) x
        smul_def' := fun b x => by
          change (b : A) • x = (b : A) * x
          simp }
    letI : IsScalarTower R B A :=
      IsScalarTower.subalgebra' (R := R) (S := A) (A := A) B
    letI : Algebra.IsIntegral B A := by
      rw [Algebra.isIntegral_def]
      intro x
      exact IsIntegral.tower_top (R := R) (A := B) (B := A)
        (Algebra.IsIntegral.isIntegral (R := R) x)
    letI : FaithfulSMul B A := by
      refine ⟨fun {x y} hxy => ?_⟩
      apply Subtype.ext
      have h1 := hxy (1 : A)
      change (x : A) • (1 : A) = (y : A) • (1 : A) at h1
      simpa using h1
    obtain ⟨M, hM_max, hM_comap⟩ :=
      Semicontinuity.Baire.exists_maximal_over_of_isIntegral (R := B) (S := A) m
    haveI hM_max_inst : M.IsMaximal := hM_max
    let mkI : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A :=
      Ideal.Quotient.mkₐ ℂ (vanishingIdeal ℂ (zeroLocus ℂ Q))
    let mtilde : Ideal (MvPolynomial (Fin n) ℂ) := M.comap mkI.toRingHom
    haveI hmtilde_max : mtilde.IsMaximal :=
      Ideal.comap_isMaximal_of_surjective
        (f := mkI.toRingHom)
        (Ideal.Quotient.mkₐ_surjective ℂ (vanishingIdeal ℂ (zeroLocus ℂ Q)))
    obtain ⟨c, hc_mtilde⟩ :=
      Semicontinuity.Baire.exists_point_of_isMaximal (m := mtilde) hmtilde_max
    have hI_le_mtilde :
        vanishingIdeal ℂ (zeroLocus ℂ Q) ≤ mtilde := by
      intro p hp
      change mkI.toRingHom p ∈ M
      have hp0 : mkI.toRingHom p = 0 := by
        change Ideal.Quotient.mk (vanishingIdeal ℂ (zeroLocus ℂ Q)) p = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hp
      rw [hp0]
      exact M.zero_mem
    have hcQ : c ∈ zeroLocus ℂ Q := by
      rw [mem_zeroLocus_iff_le_vanishingIdeal_singleton]
      have hQvan : vanishingIdeal ℂ (zeroLocus ℂ Q) = Q :=
        vanishingIdeal_zeroLocus_of_isPrime Q
      rw [← hQvan]
      simpa [hc_mtilde] using hI_le_mtilde
    have hker_aeval :
        RingHom.ker (aeval c : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ).toRingHom =
          mtilde := by
      have hsingle :
          vanishingIdeal ℂ ({c} : Set (Fin n → ℂ)) =
            RingHom.ker (aeval c : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ).toRingHom := by
        ext p
        rw [mem_vanishingIdeal_singleton_iff, RingHom.mem_ker]
        rfl
      rw [← hsingle, ← hc_mtilde]
    have hker_point :
        RingHom.ker (pointEval hcQ).toRingHom = M := by
      have hker_lift :
          RingHom.ker (pointEval hcQ).toRingHom =
            (RingHom.ker
              (aeval c : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ).toRingHom).map
                mkI.toRingHom := by
        change RingHom.ker
            (Ideal.Quotient.lift
              (vanishingIdeal ℂ (zeroLocus ℂ Q))
              (aeval c : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ).toRingHom
              _) =
            (RingHom.ker
              (aeval c : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ).toRingHom).map
                mkI.toRingHom
        exact Ideal.ker_quotient_lift
          (I := vanishingIdeal ℂ (zeroLocus ℂ Q))
          (f := (aeval c : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ).toRingHom)
          (H := by
            intro p hp
            rw [RingHom.mem_ker]
            rw [mem_vanishingIdeal_iff] at hp
            exact hp c hcQ)
      have hM_map : mtilde.map mkI.toRingHom = M := by
        simpa [mtilde, mkI] using
          (Ideal.map_comap_of_surjective mkI.toRingHom
            (Ideal.Quotient.mkₐ_surjective ℂ (vanishingIdeal ℂ (zeroLocus ℂ Q))) M)
      rw [hker_lift, hker_aeval, hM_map]
    let inclB_R : B →ₐ[R] A := Subalgebra.val B
    let peB : B →+* ℂ := (pointEval hcQ).toRingHom.comp inclB_R.toRingHom
    have hpeB_C (z : ℂ) : peB (algebraMap R B (C z)) = z := by
      change pointEval hcQ ((algebraMap B A) (algebraMap R B (C z))) = z
      have hval :
          (algebraMap B A) (algebraMap R B (C z)) =
            algebraMap R A (C z) := by
        exact (IsScalarTower.algebraMap_apply R B A (C z)).symm
      rw [hval]
      let ev : R →ₐ[ℂ] ℂ := aeval (fun _ : Fin 1 => baseValue hcQ ψ)
      change pointEval hcQ (ψ (C z)) = z
      rw [pointEval_comp_apply hcQ ψ (C z)]
      change ev (C z) = z
      exact ev.commutes z
    have hker_peB_chi :
        RingHom.ker peB = RingHom.ker χ := by
      have hpe :
          RingHom.ker peB =
            M.comap (algebraMap B A) := by
        ext x
        change pointEval hcQ (algebraMap B A x) = 0 ↔ algebraMap B A x ∈ M
        rw [← hker_point, RingHom.mem_ker]
        rfl
      have hchi : RingHom.ker χ = m := rfl
      rw [hpe, hM_comap, hchi]
    have hpeB_eq_chi : peB = χ :=
      ringHom_eq_of_ker_eq_of_C peB χ hker_peB_chi hpeB_C hχ_C
    have he_root : eR (AdjoinRoot.root P_s) = sB := by
      change (Algebra.adjoin.powerBasis' hs_int).gen = sB
      exact
        (Algebra.adjoin.powerBasis'_gen (R := R) (S := A) (x := s) hs_int)
    have hesymm_s : eR.symm sB = AdjoinRoot.root P_s := by
      apply eR.injective
      rw [AlgEquiv.apply_symm_apply, he_root]
    have hχ_s : χ sB = Y i := by
      rw [show χ sB = χ₀ (eR.symm sB) from rfl, hesymm_s]
      exact AdjoinRoot.lift_root hroot_eval₂
    have hs_val : (sB : A) = s := rfl
    have hpoint_s : pointEval hcQ s = Y i := by
      have := congrArg (fun F : B →+* ℂ => F sB) hpeB_eq_chi
      simpa [peB, inclB_R, hs_val, hχ_s] using this
    have hχ_algebraMap_R (r : R) :
        χ (algebraMap R B r) = φ r := by
      change χ₀ (eR.symm (algebraMap R B r)) = φ r
      have hsymm :
          eR.symm (algebraMap R B r) =
            algebraMap R (AdjoinRoot P_s) r := by
        exact eR.symm.toAlgHom.commutes r
      rw [hsymm]
      change (AdjoinRoot.lift φ.toRingHom (Y i) hroot_eval₂)
          ((AdjoinRoot.of P_s) r) = φ r
      exact AdjoinRoot.lift_of (f := P_s) (i := φ.toRingHom) (a := Y i)
        hroot_eval₂ (x := r)
    have hbase : baseValue hcQ ψ = t i := by
      let xR : R := X (0 : Fin 1)
      let xB : B := algebraMap R B xR
      have hxB_val : (xB : A) = ψ xR := rfl
      have hx_eval : φ xR = t i := by
        change (aeval (fun _ : Fin 1 => t i) : R →ₐ[ℂ] ℂ) (X (0 : Fin 1)) = t i
        exact MvPolynomial.aeval_X (fun _ : Fin 1 => t i) (0 : Fin 1)
      have hF : peB xB = χ xB := congrArg (fun F : B →+* ℂ => F xB) hpeB_eq_chi
      have hpe_xB : peB xB = pointEval hcQ (ψ xR) := by
        change pointEval hcQ (xB : A) = pointEval hcQ (ψ xR)
        rw [hxB_val]
      have hchi_xB : χ xB = t i := by
        simpa [xB, hx_eval] using hχ_algebraMap_R xR
      change pointEval hcQ (ψ xR) = t i
      rw [← hpe_xB]
      exact hF.trans hchi_xB
    have hf_nonzero : aeval c f ≠ 0 := by
      let fbar : A :=
        (Ideal.Quotient.mkₐ ℂ (vanishingIdeal ℂ (zeroLocus ℂ Q))) f
      haveI hFinite : Module.Finite R A :=
        coordRing_moduleFinite_of_integral ψ hψ_int
      haveI hFree : Module.Free R A :=
        coordRing_moduleFree_of_finite ψ hψ_inj hFinite
      have hdiv :
          fbar ∣ algebraMap R A (Algebra.norm R fbar) :=
        algebra_dvd_algebraMap_norm (R := R) (A := A) fbar
      have hnorm : Algebra.norm R fbar = Nf := by
        simpa [A, R, fbar] using hNf.symm
      have hdivN : fbar ∣ algebraMap R A Nf := by
        simpa [hnorm] using hdiv
      have hdiv_eval :
          pointEval hcQ fbar ∣ pointEval hcQ (algebraMap R A Nf) := by
        exact map_dvd (pointEval hcQ).toRingHom hdivN
      have hbase_eval :
          pointEval hcQ (algebraMap R A Nf) =
            aeval (fun _ : Fin 1 => t i) Nf := by
        have hcomp := pointEval_comp_apply hcQ ψ Nf
        simpa [hbase] using hcomp
      have hbase_eval_ne :
          pointEval hcQ (algebraMap R A Nf) ≠ 0 := by
        rw [hbase_eval, ← eval_mvPolynomialFinOneAlgEquivPolynomial]
        exact ht_good i
      have hfbar_ne : pointEval hcQ fbar ≠ 0 := by
        intro hfbar0
        obtain ⟨u, hu⟩ := hdiv_eval
        rw [hfbar0, zero_mul] at hu
        exact hbase_eval_ne hu
      simpa [fbar, pointEval_mk] using hfbar_ne
    exact ⟨c, hcQ, hbase, hpoint_s, hf_nonzero⟩
  choose c hcQ hbase hpoint hf_nonzero using h_lift
  refine ⟨Y, c, hcQ, ?_, ?_, ?_, hY_tend⟩
  · exact hbase
  · exact hpoint
  · exact hf_nonzero

/-- **Mumford (2.33), Step III assembly after the Step I sequence.**

The base sequence has already been produced exactly as in Mumford Step I: a
nonzero one-variable polynomial has "a finite set of zeroes" (`mumford.tex:1849`),
so one can choose a convergent sequence avoiding them.  Here that polynomial is
the one-variable norm polynomial.

Mumford Step III's geometric assembly lifts the good base points,
use compactness to take a convergent subsequence, then use the singleton fibre to
identify the limit (`mumford.tex:1871-1877`).
In affine coordinates this is lying-over for each good base point, norm
nonvanishing on the lift, boundedness in a compact polydisc, subsequence
extraction, and the singleton-fibre hypothesis.

The hypothesis `hNf` records that `Nf` is exactly the one-variable algebra norm of
the class of `f` in `𝒪(C)`.  This link is load-bearing: it is precisely what makes
"the base parameter `t i` avoids the roots of `Nf`" force "the lift of `t i` lies
off the vanishing locus of `f`" (the norm is the product over the fibre, so it is
nonzero at a base point iff `f` is nonzero on the whole fibre over it).  Without it
the statement would be false, as `Nf` would be unrelated to `f`. -/
theorem mumford233_geometric_sequence_from_good_base_sequence
    {Q : Ideal (MvPolynomial (Fin n) ℂ)} [Q.IsPrime]
    {z : Fin n → ℂ} (hzQ : z ∈ zeroLocus ℂ Q)
    {f : MvPolynomial (Fin n) ℂ}
    (hmeet : (zeroLocus ℂ Q ∩
        {x : Fin n → ℂ | aeval x f ≠ 0}).Nonempty)
    (ψ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ]
      Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
    (hψ_inj : Function.Injective ψ) (hψ_int : ψ.toRingHom.IsIntegral)
    (s : Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
    (hIso : TwoCoordIso hzQ ψ s)
    (Nf : MvPolynomial (Fin 1) ℂ)
    (hNf :
      letI : Algebra (MvPolynomial (Fin 1) ℂ)
          (Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)) := ψ.toAlgebra
      Nf = Algebra.norm (MvPolynomial (Fin 1) ℂ)
        (((Ideal.Quotient.mkₐ ℂ (vanishingIdeal ℂ (zeroLocus ℂ Q))) f :
          Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))))
    (t : ℕ → ℂ)
    (ht_tend : Tendsto t atTop (𝓝 (baseValue hzQ ψ)))
    (ht_good : ∀ i, (mvPolynomialFinOneAlgEquivPolynomial Nf).eval (t i) ≠ 0) :
    ∃ u : ℕ → Fin n → ℂ,
      (∀ i, u i ∈ zeroLocus ℂ Q ∩ {x : Fin n → ℂ | aeval x f ≠ 0}) ∧
      Tendsto u atTop (𝓝 z) := by
  classical
  have _ :
      (zeroLocus ℂ Q ∩ {x : Fin n → ℂ | aeval x f ≠ 0}).Nonempty := hmeet
  let A := Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)
  let R := MvPolynomial (Fin 1) ℂ
  letI : Algebra R A := ψ.toAlgebra
  haveI : Algebra.IsIntegral R A := by
    rw [Algebra.isIntegral_def]
    intro y
    exact hψ_int y
  haveI : FaithfulSMul R A :=
    (faithfulSMul_iff_algebraMap_injective R A).mpr (by simpa using hψ_inj)
  haveI : Module.Finite R A :=
    coordRing_moduleFinite_of_integral (Q := Q) ψ hψ_int
  haveI : Module.Free R A :=
    coordRing_moduleFree_of_finite (Q := Q) ψ hψ_inj inferInstance
  let fbar : A :=
    ((Ideal.Quotient.mkₐ ℂ (vanishingIdeal ℂ (zeroLocus ℂ Q))) f :
      Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
  have hNf' : Algebra.norm R fbar = Nf := by
    simpa [R, A, fbar] using hNf.symm
  obtain ⟨P_s, hP_s_monic, hP_s_eval, Y, c, hcQ, hbase, hs_eval, hf_ne, hY_tend⟩ :=
    image_curve_monic_generator hzQ hmeet ψ hψ_inj hψ_int s Nf hNf t ht_tend ht_good
  obtain ⟨Bb, hBb⟩ := exists_norm_bound_of_tendsto ht_tend
  have hcoord_bound : ∀ j : Fin n, ∃ Rj : ℝ, ∀ i, ‖c i j‖ ≤ Rj := by
    intro j
    let xj : A :=
      ((Ideal.Quotient.mkₐ ℂ (vanishingIdeal ℂ (zeroLocus ℂ Q))) (X j) :
        Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
    obtain ⟨Rj, hRj⟩ := exists_bound_pointEval_of_isIntegral ψ xj (hψ_int xj) Bb
    refine ⟨Rj, fun i => ?_⟩
    have hpt := hRj (c i) (hcQ i) (by
      rw [hbase i]
      exact hBb i)
    have hxj_eval : pointEval (hcQ i) xj = c i j := by
      simp [xj, Ideal.Quotient.mkₐ_eq_mk]
    simpa [hxj_eval] using hpt
  choose Rj hRj using hcoord_bound
  let K : Set (Fin n → ℂ) :=
    Set.univ.pi (fun j : Fin n => Metric.closedBall (0 : ℂ) (Rj j))
  have hK_compact : IsCompact K := by
    exact isCompact_univ_pi (fun j => isCompact_closedBall (0 : ℂ) (Rj j))
  have hcK : ∀ i, c i ∈ K := by
    intro i j _hj
    rw [mem_closedBall_zero_iff]
    exact hRj j i
  obtain ⟨cLim, hcLimK, φ, hφ_mono, hφ_tend⟩ :=
    hK_compact.tendsto_subseq hcK
  have hclosedC : IsClosed (zeroLocus ℂ Q : Set (Fin n → ℂ)) :=
    isClosed_zeroLocus_mvPolynomial Q
  have hcLimQ : cLim ∈ zeroLocus ℂ Q :=
    hclosedC.mem_of_tendsto hφ_tend
      (Eventually.of_forall (fun k => hcQ (φ k)))
  obtain ⟨g0, hg0⟩ := Ideal.Quotient.mk_surjective (ψ (X (0 : Fin 1)))
  have hbase_g0 : ∀ x : Fin n → ℂ, ∀ hx : x ∈ zeroLocus ℂ Q,
      baseValue hx ψ = aeval x g0 := by
    intro x hx
    unfold baseValue
    rw [← hg0]
    exact pointEval_mk hx g0
  have hcont_g0 : Continuous (fun x : Fin n → ℂ => aeval x g0) := by
    simpa only [MvPolynomial.aeval_def, MvPolynomial.eval] using
      (MvPolynomial.continuous_eval g0)
  have hlim_eval :
      Tendsto (fun k => aeval (c (φ k)) g0) atTop (𝓝 (aeval cLim g0)) := by
    simpa [Function.comp_def] using hcont_g0.tendsto cLim |>.comp hφ_tend
  have hlim_base :
      Tendsto (fun k => aeval (c (φ k)) g0) atTop (𝓝 (baseValue hzQ ψ)) := by
    have hseq :
        (fun k => aeval (c (φ k)) g0) = fun k => t (φ k) := by
      funext k
      rw [← hbase_g0 (c (φ k)) (hcQ (φ k)), hbase]
    rw [hseq]
    exact ht_tend.comp hφ_mono.tendsto_atTop
  have hbase_limit_eval : aeval cLim g0 = baseValue hzQ ψ :=
    tendsto_nhds_unique hlim_eval hlim_base
  have hbase_limit : baseValue hcLimQ ψ = baseValue hzQ ψ := by
    rw [hbase_g0 cLim hcLimQ]
    exact hbase_limit_eval
  obtain ⟨s0, hs0⟩ := Ideal.Quotient.mk_surjective s
  have hs0_eval : ∀ x : Fin n → ℂ, ∀ hx : x ∈ zeroLocus ℂ Q,
      pointEval hx s = aeval x s0 := by
    intro x hx
    rw [← hs0]
    exact pointEval_mk hx s0
  have hcont_s0 : Continuous (fun x : Fin n → ℂ => aeval x s0) := by
    simpa only [MvPolynomial.aeval_def, MvPolynomial.eval] using
      (MvPolynomial.continuous_eval s0)
  have hlim_s_eval :
      Tendsto (fun k => aeval (c (φ k)) s0) atTop (𝓝 (aeval cLim s0)) := by
    simpa [Function.comp_def] using hcont_s0.tendsto cLim |>.comp hφ_tend
  have hlim_s_target :
      Tendsto (fun k => aeval (c (φ k)) s0) atTop (𝓝 (pointEval hzQ s)) := by
    have hseq :
        (fun k => aeval (c (φ k)) s0) = fun k => Y (φ k) := by
      funext k
      rw [← hs0_eval (c (φ k)) (hcQ (φ k)), hs_eval]
    rw [hseq]
    exact hY_tend.comp hφ_mono.tendsto_atTop
  have hs_limit_eval : aeval cLim s0 = pointEval hzQ s :=
    tendsto_nhds_unique hlim_s_eval hlim_s_target
  have hs_limit : pointEval hcLimQ s = pointEval hzQ s := by
    rw [hs0_eval cLim hcLimQ]
    exact hs_limit_eval
  have hcLim_eq_z : cLim = z := hIso cLim hcLimQ hbase_limit hs_limit
  refine ⟨fun k => c (φ k), ?_, ?_⟩
  · intro k
    exact ⟨hcQ (φ k), hf_ne (φ k)⟩
  · rw [← hcLim_eq_z]
    exact hφ_tend

/-- **Mumford (2.33) geometric assembly after the norm step.**

This is the Step I + lying-over + boundedness + subsequence bridge in
Mumford (2.33), affine `r = 1`
(Mumford, *Algebraic Geometry I*, Theorem (2.33), proof Steps I--III, tex:1835-1877), after the
finite-module/freeness/norm algebra has already produced a nonzero base norm.

Algebraic inputs:
* `coordRing_moduleFinite_of_integral`: finite module over `ℂ[t]`;
* `coordRing_moduleFree_of_finite`: finite torsion-free over the PID
  `MvPolynomial (Fin 1) ℂ ≃ ℂ[X]`;
* `coordRing_norm_ne_zero_of_ne_zero`: nonzero `fbar` has nonzero norm.

Proof idea: view the nonzero norm as a single-variable polynomial, use
`Mumford233.exists_seq_tendsto_avoiding_roots` for Step I (`tex:1849`), lift
each good base point by `exists_maximal_over_of_isIntegral`, use the norm
nonvanishing to keep `fbar` out of the lifted maximal ideal, bound coordinates
via integral equations and `roots_mem_closedBall_of_cauchyBound_le`, extract a
compact subsequence, and identify its limit with `z` using the singleton-fibre
hypothesis (`tex:1871-1877`). -/
theorem mumford233_geometric_sequence_from_nonzero_norm
    {Q : Ideal (MvPolynomial (Fin n) ℂ)} [Q.IsPrime]
    {z : Fin n → ℂ} (hzQ : z ∈ zeroLocus ℂ Q)
    {f : MvPolynomial (Fin n) ℂ}
    (hmeet : (zeroLocus ℂ Q ∩
        {x : Fin n → ℂ | aeval x f ≠ 0}).Nonempty)
    (ψ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ]
      Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
    (hψ_inj : Function.Injective ψ) (hψ_int : ψ.toRingHom.IsIntegral)
    (s : Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
    (hIso : TwoCoordIso hzQ ψ s)
    (hnorm_ne :
      letI : Algebra (MvPolynomial (Fin 1) ℂ)
          (Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)) := ψ.toAlgebra
      Algebra.norm (MvPolynomial (Fin 1) ℂ)
        (((Ideal.Quotient.mkₐ ℂ (vanishingIdeal ℂ (zeroLocus ℂ Q))) f :
          Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))) ≠ 0) :
    ∃ u : ℕ → Fin n → ℂ,
      (∀ i, u i ∈ zeroLocus ℂ Q ∩ {x : Fin n → ℂ | aeval x f ≠ 0}) ∧
      Tendsto u atTop (𝓝 z) := by
  let A := Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)
  let R := MvPolynomial (Fin 1) ℂ
  letI : Algebra R A := ψ.toAlgebra
  let fbar : A :=
    ((Ideal.Quotient.mkₐ ℂ (vanishingIdeal ℂ (zeroLocus ℂ Q))) f :
      Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
  let Nf : R := Algebra.norm R fbar
  let q : Polynomial ℂ := mvPolynomialFinOneAlgEquivPolynomial Nf
  have hq_ne : q ≠ 0 := by
    intro hq
    apply hnorm_ne
    exact mvPolynomialFinOneAlgEquivPolynomial.injective hq
  obtain ⟨t, ht_tend, ht_good⟩ :=
    Semicontinuity.Baire.Mumford233.exists_seq_tendsto_avoiding_roots
      hq_ne (baseValue hzQ ψ)
  exact mumford233_geometric_sequence_from_good_base_sequence
    hzQ hmeet ψ hψ_inj hψ_int s hIso Nf rfl t ht_tend ht_good

/-- Geometric sequence from the finite integral base.

This is the hard branch of Mumford (2.33), Steps I--III after the
finite-module algebra has been proved (`tex:1835-1877`).  From a finite integral
one-coordinate parameter and a nonzero regular function class `fbar`, one uses:
the PID/freeness transport `ℂ[X] ≃ ℂ[t]`, the nonzero norm polynomial from
`coordRing_norm_ne_zero_of_ne_zero`, and then the post-norm geometric statement
`mumford233_geometric_sequence_from_nonzero_norm`. -/
theorem mumford233_geometric_sequence_from_finite_integral
    {Q : Ideal (MvPolynomial (Fin n) ℂ)} [Q.IsPrime]
    {z : Fin n → ℂ} (hzQ : z ∈ zeroLocus ℂ Q)
    {f : MvPolynomial (Fin n) ℂ}
    (hmeet : (zeroLocus ℂ Q ∩
        {x : Fin n → ℂ | aeval x f ≠ 0}).Nonempty)
    (ψ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ]
      Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
    (hψ_inj : Function.Injective ψ) (hψ_int : ψ.toRingHom.IsIntegral)
    (s : Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
    (hIso : TwoCoordIso hzQ ψ s)
    (hfbar_ne :
      ((Ideal.Quotient.mkₐ ℂ (vanishingIdeal ℂ (zeroLocus ℂ Q))) f :
        Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)) ≠ 0)
    (hψ_finite :
      letI : Algebra (MvPolynomial (Fin 1) ℂ)
          (Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)) := ψ.toAlgebra
      Module.Finite (MvPolynomial (Fin 1) ℂ)
        (Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))) :
    ∃ u : ℕ → Fin n → ℂ,
      (∀ i, u i ∈ zeroLocus ℂ Q ∩ {x : Fin n → ℂ | aeval x f ≠ 0}) ∧
      Tendsto u atTop (𝓝 z) := by
  let A := Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)
  let R := MvPolynomial (Fin 1) ℂ
  let fbar : A :=
    ((Ideal.Quotient.mkₐ ℂ (vanishingIdeal ℂ (zeroLocus ℂ Q))) f :
      Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
  have hfree :
      letI : Algebra R A := ψ.toAlgebra
      Module.Free R A :=
    coordRing_moduleFree_of_finite (Q := Q) ψ hψ_inj hψ_finite
  have hnorm_ne :
      letI : Algebra R A := ψ.toAlgebra
      Algebra.norm R fbar ≠ 0 :=
    coordRing_norm_ne_zero_of_ne_zero (Q := Q) ψ fbar hfbar_ne hfree hψ_finite
  exact mumford233_geometric_sequence_from_nonzero_norm
    hzQ hmeet ψ hψ_inj hψ_int s hIso hnorm_ne

/-- **Mumford (2.33) Steps I--III after the Mumford (2.32) projection refinement.**

Assume the chosen affine parameter satisfies the conclusion supplied by Mumford
(2.32).  Then Mumford (2.33), Steps I--III
(Mumford, *Algebraic Geometry I*, Theorem (2.33), proof Steps I--III, tex:1835-1877) produce an
actual
sequence of complex points `uᵢ ∈ C ∩ {f ≠ 0}` converging classically to `z`.

This statement separates the point-producing part from the projection-refinement
problem. Its proof uses Step I finite bad-parameter avoidance (using
`exists_seq_tendsto_avoiding_roots`), lying-over to lift good parameters to
`ℂ`-points (Dictionary `exists_maximal_over_of_isIntegral`), Step III affine
boundedness (`roots_mem_closedBall_of_cauchyBound_le`), subsequence extraction,
and the supplied singleton-fibre hypothesis to identify the limit with `z`. -/
theorem mumford233_isolated_parameter_approximating_sequence
    {Q : Ideal (MvPolynomial (Fin n) ℂ)} [Q.IsPrime]
    {z : Fin n → ℂ} (hzQ : z ∈ zeroLocus ℂ Q)
    {f : MvPolynomial (Fin n) ℂ}
    (hmeet : (zeroLocus ℂ Q ∩
        {x : Fin n → ℂ | aeval x f ≠ 0}).Nonempty)
    (ψ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ]
      Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
    (hψ_inj : Function.Injective ψ) (hψ_int : ψ.toRingHom.IsIntegral)
    (s : Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
    (hIso : TwoCoordIso hzQ ψ s) :
    ∃ u : ℕ → Fin n → ℂ,
      (∀ i, u i ∈ zeroLocus ℂ Q ∩ {x : Fin n → ℂ | aeval x f ≠ 0}) ∧
      Tendsto u atTop (𝓝 z) := by
  by_cases hzf : aeval z f ≠ 0
  · exact mumford233_constant_approximating_sequence hzQ hzf
  have hfbar_ne :
      ((Ideal.Quotient.mkₐ ℂ (vanishingIdeal ℂ (zeroLocus ℂ Q))) f :
        Semicontinuity.Baire.coordRing (zeroLocus ℂ Q)) ≠ 0 := by
    exact coordRing_mk_ne_zero_of_exists_aeval_ne_zero
      (Q := Q) (f := f) ⟨hmeet.choose, hmeet.choose_spec.1, hmeet.choose_spec.2⟩
  have hψ_finite :=
    coordRing_moduleFinite_of_integral (Q := Q) ψ hψ_int
  exact mumford233_geometric_sequence_from_finite_integral
    hzQ hmeet ψ hψ_inj hψ_int s hIso hfbar_ne hψ_finite

/-- **Mumford (2.33), closure conversion from the constructed sequence.**

Once Steps I--III have produced `uᵢ ∈ C ∩ {f ≠ 0}` with `uᵢ → z`, the final
topological conclusion is exactly `mem_closure_of_tendsto`.  This is the last
sentence of Mumford (2.33), Step III
tex:1871-1877, formalized by `mem_closure_of_tendsto`. -/
theorem mumford233_affine_curve_open_dense_from_isolation
    {Q : Ideal (MvPolynomial (Fin n) ℂ)} [Q.IsPrime]
    {z : Fin n → ℂ} (hzQ : z ∈ zeroLocus ℂ Q)
    {f : MvPolynomial (Fin n) ℂ}
    (hmeet : (zeroLocus ℂ Q ∩
        {x : Fin n → ℂ | aeval x f ≠ 0}).Nonempty)
    (ψ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ]
      Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
    (hψ_inj : Function.Injective ψ) (hψ_int : ψ.toRingHom.IsIntegral)
    (s : Semicontinuity.Baire.coordRing (zeroLocus ℂ Q))
    (hIso : TwoCoordIso hzQ ψ s) :
    z ∈ closure (zeroLocus ℂ Q ∩ {x : Fin n → ℂ | aeval x f ≠ 0}) := by
  obtain ⟨u, hu_mem, hu_tend⟩ :=
    mumford233_isolated_parameter_approximating_sequence hzQ hmeet ψ hψ_inj hψ_int s hIso
  exact mem_closure_of_tendsto hu_tend (Eventually.of_forall hu_mem)

end Semicontinuity.Baire.Mumford233Curve
