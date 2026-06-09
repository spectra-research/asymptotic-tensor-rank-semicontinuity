/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Defs
import AsymptoticTensorRankSemicontinuity.Baire.CurveExistence
import AsymptoticTensorRankSemicontinuity.Baire.Mumford233Curve
import Mathlib.Order.BourbakiWitt
import Mathlib.RingTheory.PicardGroup
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# §4.1 Baire property for affine varieties over ℂ

Source: the semicontinuity manuscript,
lines 1108-1137.

* `zariski_baire` — **Lemma 4.2** (tex:1102-1131, `\label{lem:baire-property}`).

Proof outline (tex:1111-1118):
  1. Zariski-open ⇒ Euclidean-open.
  2. Zariski-dense ⇒ Euclidean-dense
     (`\cite[Prop.~5]{serreGeometrieAlgebriqueGeometrie1956}`).
  3. `X` with Euclidean topology is a Baire space.
  4. Apply Baire category theorem.
-/

namespace Semicontinuity

universe v

variable {V : Type v} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]


/-- `U` is **Zariski-open in `X ⊆ V`** (relative Zariski topology, tex:1106, 1314):
    `U ⊆ X` and there exists an ambient Zariski-closed `C` with `X \ U = X ∩ C`.

    Equivalently, `X \ U` is closed in the subspace topology on `X`. When `X` is
    itself ambient Zariski-closed this collapses to "`X \ U` is ambient closed",
    but for general `X` it is strictly weaker (e.g., `V_{<r} = V_{≤r} \ V_{=r}` is
    an Fσ that is open in `V_{≤r}` without being ambient-closed). -/
def IsZariskiOpenIn (U X : Set V) : Prop :=
  U ⊆ X ∧ ∃ C : Set V, IsZariskiClosed (F := ℂ) C ∧ X \ U = X ∩ C

/-- `U` is **Zariski-dense in `X ⊆ V`**: `X ⊆ zariskiClosure U`. -/
def IsZariskiDenseIn (U X : Set V) : Prop :=
  X ⊆ zariskiClosure (F := ℂ) U

/-! ## Euclidean auxiliary predicates

The theorem statement is intentionally phrased only in the algebraic language used by
the surrounding development. For the analytic proof step we model the Euclidean
topology through the coordinate map associated to `Module.finBasis ℂ V`.
-/

/-- Coordinates of a vector in the finite-dimensional complex vector space `V`. -/
noncomputable def euclideanCoord (T : V) : Fin (Module.finrank ℂ V) → ℂ :=
  fun i => (Module.finBasis ℂ V).repr T i

/-- `A` is Euclidean-dense in `X`, expressed through finite-dimensional coordinates. -/
def EuclideanDenseIn (A X : Set V) : Prop :=
  X ⊆ euclideanCoord ⁻¹' closure (euclideanCoord '' A)

/-- `U` is Euclidean-open in `X`, expressed through finite-dimensional coordinates. -/
def EuclideanOpenIn (U X : Set V) : Prop :=
  ∃ O : Set (Fin (Module.finrank ℂ V) → ℂ),
    IsOpen O ∧ U = X ∩ euclideanCoord ⁻¹' O

private lemma isClosed_zariskiCoordZeroSet (A : Set V) :
    IsClosed (⋂ p : { p : MvPolynomial (Fin (Module.finrank ℂ V)) ℂ //
      ∀ T ∈ A, MvPolynomial.eval (euclideanCoord T) p = 0 },
      { x : Fin (Module.finrank ℂ V) → ℂ | MvPolynomial.eval x p.1 = 0 }) := by
  exact isClosed_iInter fun p =>
    isClosed_eq (MvPolynomial.continuous_eval (p := p.1)) continuous_const

private lemma zariskiClosed_eq_coord_preimage {A : Set V}
    (hA : IsZariskiClosed (F := ℂ) A) :
    ∃ Z : Set (Fin (Module.finrank ℂ V) → ℂ),
      IsClosed Z ∧ A = euclideanCoord ⁻¹' Z := by
  let Z : Set (Fin (Module.finrank ℂ V) → ℂ) :=
    ⋂ p : { p : MvPolynomial (Fin (Module.finrank ℂ V)) ℂ //
      ∀ T ∈ A, MvPolynomial.eval (euclideanCoord T) p = 0 },
      { x : Fin (Module.finrank ℂ V) → ℂ | MvPolynomial.eval x p.1 = 0 }
  refine ⟨Z, isClosed_zariskiCoordZeroSet (V := V) A, ?_⟩
  ext T
  constructor
  · intro hT
    change euclideanCoord T ∈ Z
    simp only [Z, Set.mem_iInter, Set.mem_setOf_eq]
    intro p
    exact p.2 T hT
  · intro hT
    change euclideanCoord T ∈ Z at hT
    have hT' : ∀ p : { p : MvPolynomial (Fin (Module.finrank ℂ V)) ℂ //
      ∀ T ∈ A, MvPolynomial.eval (euclideanCoord T) p = 0 },
      MvPolynomial.eval (euclideanCoord T) p.1 = 0 := by
      simpa only [Z, Set.mem_iInter, Set.mem_setOf_eq] using hT
    rw [← hA]
    intro f hf hfA
    rcases hf with ⟨p, hp⟩
    have hpA : ∀ S ∈ A, MvPolynomial.eval (euclideanCoord S) p = 0 := by
      intro S hS
      exact (hp S).symm.trans (hfA S hS)
    have hpT : MvPolynomial.eval (euclideanCoord T) p = 0 := by
      exact hT' ⟨p, hpA⟩
    exact (hp T).trans hpT

private lemma zariskiClosed_image_eq_coordSet {A : Set V}
    (hA : IsZariskiClosed (F := ℂ) A) :
    ∃ Z : Set (Fin (Module.finrank ℂ V) → ℂ),
      IsClosed Z ∧ A = euclideanCoord ⁻¹' Z ∧ euclideanCoord '' A = Z := by
  rcases zariskiClosed_eq_coord_preimage (V := V) hA with ⟨Z, hZ_closed, hAZ⟩
  refine ⟨Z, hZ_closed, hAZ, ?_⟩
  ext x
  constructor
  · rintro ⟨T, hTA, rfl⟩
    rw [hAZ] at hTA
    exact hTA
  · intro hx
    let y : Fin (Module.finrank ℂ V) →₀ ℂ := Finsupp.equivFunOnFinite.symm x
    refine ⟨(Module.finBasis ℂ V).repr.symm y, ?_, ?_⟩
    · rw [hAZ]
      change euclideanCoord ((Module.finBasis ℂ V).repr.symm y) ∈ Z
      convert hx
      funext i
      have h :
          (Module.finBasis ℂ V).repr ((Module.finBasis ℂ V).repr.symm y) = y :=
        LinearEquiv.apply_symm_apply (Module.finBasis ℂ V).repr y
      rw [euclideanCoord, h]
      simp [y]
    · funext i
      have h :
          (Module.finBasis ℂ V).repr ((Module.finBasis ℂ V).repr.symm y) = y :=
        LinearEquiv.apply_symm_apply (Module.finBasis ℂ V).repr y
      rw [euclideanCoord, h]
      simp [y]

/-- Paper tex:1115. Zariski topology is coarser than Euclidean topology. -/
lemma zariskiOpenIn_euclideanOpenIn {U X : Set V}
    (hU : IsZariskiOpenIn U X) :
    EuclideanOpenIn U X := by
  rcases hU with ⟨hUX, C, hC_closed, hXU⟩
  rcases zariskiClosed_eq_coord_preimage (V := V) hC_closed with
    ⟨Z, hZ_closed, hCZ⟩
  refine ⟨Zᶜ, hZ_closed.isOpen_compl, ?_⟩
  ext T
  constructor
  · intro hTU
    refine ⟨hUX hTU, ?_⟩
    rw [Set.mem_preimage, Set.mem_compl_iff]
    intro hTZ
    have hTC : T ∈ C := by
      rw [hCZ]
      exact hTZ
    have hTdiff : T ∈ X \ U := by
      rw [hXU]
      exact ⟨hUX hTU, hTC⟩
    exact hTdiff.2 hTU
  · rintro ⟨hTX, hTZ⟩
    by_contra hTU
    have hTdiff : T ∈ X \ U := ⟨hTX, hTU⟩
    have hTC : T ∈ C := (by
      have := hTdiff
      rw [hXU] at this
      exact this.2)
    have : euclideanCoord T ∈ Z := by
      rw [hCZ] at hTC
      exact hTC
    exact hTZ this


-- On reducible varieties the naive assertion that a polynomial vanishing on a Euclidean-open
-- piece of `X` vanishes on all of `X` is false (e.g. `X` the union of the coordinate axes).
-- The argument below uses Serre 1956 GAGA Prop. 5 together with the Zariski-density
-- hypothesis in `relative_polynomial_identity_theorem_open_meets_compl`.

/-! ## Algebraic infrastructure for the irreducible-component reduction.

These are the basic properties of the `zariskiClosure` closure operator needed to
reduce Serre 1956 Prop. 5 (serre1956.tex:236) from a general complex variety to the
irreducible case. They are elementary consequences of the definition of
`zariskiClosure`; the analytic input is
`irreducible_zariskiOpenDense_euclideanDense`. -/

/-- A set is contained in its Zariski closure. -/
private lemma subset_zariskiClosure_baire (A : Set V) :
    A ⊆ zariskiClosure (F := ℂ) A := by
  intro T hT f hf hfA
  exact hfA T hT

/-- The Zariski closure is monotone. -/
private lemma zariskiClosure_mono_baire {A B : Set V} (h : A ⊆ B) :
    zariskiClosure (F := ℂ) A ⊆ zariskiClosure (F := ℂ) B := by
  intro T hT f hf hfB
  exact hT f hf (fun S hS => hfB S (h hS))

/-- The Zariski closure is itself Zariski-closed. -/
private lemma zariskiClosure_closed_baire (A : Set V) :
    IsZariskiClosed (F := ℂ) (zariskiClosure (F := ℂ) A) := by
  apply Set.eq_of_subset_of_subset
  · intro T hT f hf hfA
    refine hT f hf ?_
    intro S hS
    exact hS f hf hfA
  · exact subset_zariskiClosure_baire (zariskiClosure (F := ℂ) A)

/-- The Zariski closure is the smallest Zariski-closed set containing `A`:
    if `A ⊆ B` and `B` is Zariski-closed, then `zariskiClosure A ⊆ B`. -/
private lemma zariskiClosure_minimal_baire {A B : Set V} (hAB : A ⊆ B)
    (hB : IsZariskiClosed (F := ℂ) B) :
    zariskiClosure (F := ℂ) A ⊆ B := by
  have : zariskiClosure (F := ℂ) A ⊆ zariskiClosure (F := ℂ) B :=
    zariskiClosure_mono_baire hAB
  rw [hB] at this
  exact this

/-- The empty set is Zariski-closed. -/
private lemma zariskiClosed_empty_baire :
    IsZariskiClosed (F := ℂ) (∅ : Set V) := by
  apply Set.eq_of_subset_of_subset
  · intro T hT
    have hOne : (fun _ : V => (1 : ℂ)) T = 0 := by
      refine hT (fun _ : V => (1 : ℂ)) ?_ ?_
      · exact ⟨MvPolynomial.C 1, fun S => by simp⟩
      · intro S hS; simp at hS
    exact (one_ne_zero hOne).elim
  · exact subset_zariskiClosure_baire (∅ : Set V)

/-- A finite union of Zariski-closed sets is Zariski-closed.
    (`zariskiClosure (A ∪ B)` need not equal `A ∪ B` in general for arbitrary
    closure operators, but it does for the Zariski closure: the union of two
    Zariski-closed sets is the zero locus of the pointwise products of the
    defining functions.) -/
private lemma zariskiClosed_union_baire {A B : Set V}
    (hA : IsZariskiClosed (F := ℂ) A) (hB : IsZariskiClosed (F := ℂ) B) :
    IsZariskiClosed (F := ℂ) (A ∪ B) := by
  apply Set.eq_of_subset_of_subset
  · -- `T ∈ zariskiClosure (A ∪ B)` ⇒ `T ∈ A ∪ B`.
    intro T hT
    by_contra hTAB
    rw [Set.mem_union, not_or] at hTAB
    obtain ⟨hTA, hTB⟩ := hTAB
    -- `T ∉ A = zariskiClosure A`: some polynomial `f` vanishes on `A`, `f T ≠ 0`.
    rw [← hA] at hTA
    rw [← hB] at hTB
    simp only [zariskiClosure, Set.mem_setOf_eq, not_forall] at hTA hTB
    obtain ⟨f, hf, hfA, hfT⟩ := hTA
    obtain ⟨g, hg, hgB, hgT⟩ := hTB
    -- `f * g` is polynomial, vanishes on `A ∪ B`, but `(f*g) T = f T * g T ≠ 0`.
    have hfg_poly : IsPolynomialFunction (F := ℂ) (fun x => f x * g x) := by
      obtain ⟨p, hp⟩ := hf
      obtain ⟨q, hq⟩ := hg
      refine ⟨p * q, fun x => ?_⟩
      simp only [map_mul, hp x, hq x]
    have hfg_vanish : ∀ S ∈ A ∪ B, f S * g S = 0 := by
      rintro S (hSA | hSB)
      · rw [hfA S hSA, zero_mul]
      · rw [hgB S hSB, mul_zero]
    have hfgT : f T * g T = 0 := hT (fun x => f x * g x) hfg_poly hfg_vanish
    exact (mul_ne_zero hfT hgT) hfgT
  · exact subset_zariskiClosure_baire (A ∪ B)

/-- A finite (Finset-indexed) union of Zariski-closed sets is Zariski-closed. -/
private lemma zariskiClosed_biUnion_baire {ι : Type*} (s : Finset ι)
    (B : ι → Set V) (hB : ∀ i ∈ s, IsZariskiClosed (F := ℂ) (B i)) :
    IsZariskiClosed (F := ℂ) (⋃ i ∈ s, B i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (zariskiClosed_empty_baire (V := V))
  | insert a s ha ih =>
      have hBa : IsZariskiClosed (F := ℂ) (B a) := hB a (Finset.mem_insert_self a s)
      have hrest : IsZariskiClosed (F := ℂ) (⋃ i ∈ s, B i) :=
        ih (fun i hi => hB i (Finset.mem_insert_of_mem hi))
      have hunion :
          (⋃ i ∈ insert a s, B i) = B a ∪ (⋃ i ∈ s, B i) := by
        ext T
        simp [Finset.mem_insert, Set.mem_iUnion]
      rw [hunion]
      exact zariskiClosed_union_baire hBa hrest

/-- **Local irreducibility predicate** (matches `IsZariskiIrreducible` in
    `EuclideanClosed.lean`, which is downstream of this file; restated here so the
    reduction can be phrased upstream). An affine subset `X ⊆ V` is Zariski-
    irreducible if it is non-empty, Zariski-closed, and cannot be covered by two
    proper Zariski-closed subsets. -/
private def IsZariskiIrred (X : Set V) : Prop :=
  X.Nonempty ∧ IsZariskiClosed (F := ℂ) X ∧
    ∀ Y Z : Set V, IsZariskiClosed (F := ℂ) Y → IsZariskiClosed (F := ℂ) Z →
      X ⊆ Y ∪ Z → X ⊆ Y ∨ X ⊆ Z

/-- On an irreducible variety `X`, a non-empty Zariski-open subset is Zariski-dense.
    (Matches `zariskiOpenIn_dense_of_irreducible` in `EuclideanClosed.lean`, restated
    upstream.) -/
private lemma zariskiOpenIn_dense_of_irred_baire {U X : Set V}
    (hX_irr : IsZariskiIrred X)
    (hU_open : IsZariskiOpenIn U X) (hU_ne : U.Nonempty) :
    IsZariskiDenseIn U X := by
  rcases hX_irr with ⟨_hX_ne, _hX_closed, hX_irred⟩
  rcases hU_open with ⟨hUX, C, hC_closed, hdiff⟩
  have hcover : X ⊆ C ∪ zariskiClosure (F := ℂ) U := by
    intro T hTX
    by_cases hTU : T ∈ U
    · exact Or.inr (subset_zariskiClosure_baire U hTU)
    · left
      have hTdiff : T ∈ X \ U := ⟨hTX, hTU⟩
      have hTC : T ∈ X ∩ C := by simpa [hdiff] using hTdiff
      exact hTC.2
  rcases hX_irred C (zariskiClosure (F := ℂ) U) hC_closed
      (zariskiClosure_closed_baire U) hcover with hXC | hXclosure
  · obtain ⟨T, hTU⟩ := hU_ne
    have hTX : T ∈ X := hUX hTU
    have hTdiff : T ∈ X \ U := by rw [hdiff]; exact ⟨hTX, hXC hTX⟩
    exact (hTdiff.2 hTU).elim
  · exact hXclosure

/-! ### Ambient-space analytic substrate

The genuine analytic content of Serre 1956 Prop. 5 for the **ambient affine
space** `ℂᵏ` is reachable in current Mathlib: it is the multivariable complex
analytic identity theorem `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`
specialised to polynomial evaluations (`AnalyticOnNhd.eval_mvPolynomial`).

`mvPolynomial_eq_zero_of_eventuallyEq_zero` is the principle "a polynomial that
agrees with `0` on a Euclidean neighbourhood of a point is the zero function".
`zeroLocus_interior_eq_empty` derives that the zero set of a nonzero polynomial
has empty Euclidean interior, hence (`compl_dense`) a dense complement.

These are the affine-space shadow of the variety-level fact. The corresponding
irreducible-variety statement requires the relative identity theorem on the variety. -/

/-- The multivariable complex identity theorem for polynomials: a `MvPolynomial`
over `ℂ` in finitely many variables that vanishes on a Euclidean neighbourhood of
*some* point of `ℂᵏ` is the zero polynomial's evaluation, i.e. vanishes everywhere.
Proved via `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`. -/
private lemma mvPolynomial_eventuallyEqZero_imp_eval_zero {k : ℕ}
    (p : MvPolynomial (Fin k) ℂ) {z₀ : Fin k → ℂ}
    (hz₀ : (fun x => MvPolynomial.eval x p) =ᶠ[nhds z₀] 0) :
    ∀ x : Fin k → ℂ, MvPolynomial.eval x p = 0 := by
  have hana : AnalyticOnNhd ℂ (fun x => MvPolynomial.eval x p) Set.univ :=
    AnalyticOnNhd.eval_mvPolynomial p
  have hconn : IsPreconnected (Set.univ : Set (Fin k → ℂ)) :=
    PreconnectedSpace.isPreconnected_univ
  have heq : Set.EqOn (fun x => MvPolynomial.eval x p) 0 Set.univ :=
    hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn (Set.mem_univ z₀) hz₀
  intro x
  have := heq (Set.mem_univ x)
  simpa using this

/-- The Euclidean zero locus of a **nonzero** `MvPolynomial` over `ℂ` has empty
interior in `ℂᵏ`: if it had an interior point, the polynomial would vanish on a
neighbourhood, hence (identity theorem) be identically `0`. -/
private lemma zeroLocus_interior_eq_empty {k : ℕ}
    {p : MvPolynomial (Fin k) ℂ} (hp : p ≠ 0) :
    interior { x : Fin k → ℂ | MvPolynomial.eval x p = 0 } = ∅ := by
  by_contra hne
  rw [← Set.not_nonempty_iff_eq_empty, not_not] at hne
  obtain ⟨z₀, hz₀⟩ := hne
  have hz₀_nhds : { x : Fin k → ℂ | MvPolynomial.eval x p = 0 } ∈ nhds z₀ :=
    mem_interior_iff_mem_nhds.mp hz₀
  have hev : (fun x => MvPolynomial.eval x p) =ᶠ[nhds z₀] 0 := by
    filter_upwards [hz₀_nhds] with x hx using hx
  have hzero : ∀ x : Fin k → ℂ, MvPolynomial.eval x p = 0 :=
    mvPolynomial_eventuallyEqZero_imp_eval_zero p hev
  exact hp (MvPolynomial.funext (fun x => by simpa using hzero x))

/-- The Euclidean complement of the zero locus of a **nonzero** `MvPolynomial`
over `ℂ` is Euclidean-dense in `ℂᵏ` (the ambient-space shadow of Serre Prop. 5):
a nonzero polynomial's zero set is nowhere dense. -/
private lemma dense_compl_zeroLocus {k : ℕ}
    {p : MvPolynomial (Fin k) ℂ} (hp : p ≠ 0) :
    Dense { x : Fin k → ℂ | MvPolynomial.eval x p ≠ 0 } := by
  have hclosed : IsClosed { x : Fin k → ℂ | MvPolynomial.eval x p = 0 } :=
    isClosed_eq (MvPolynomial.continuous_eval p) continuous_const
  have hcompl : { x : Fin k → ℂ | MvPolynomial.eval x p ≠ 0 }
      = { x : Fin k → ℂ | MvPolynomial.eval x p = 0 }ᶜ := by
    ext x; simp [Set.mem_compl_iff]
  rw [hcompl]
  rw [← interior_eq_empty_iff_dense_compl]
  exact zeroLocus_interior_eq_empty hp

/-! ### Curve-reduction substrate

Serre's Remark (`serre1956.tex:236`) notes that Proposition 5 — equivalently the
injectivity of `θ : 𝒪_x → ℋ_x` — is proved by reduction to the case of a curve.
The 1-dimensional density step of that reduction is:

* `dense_compl_finite_complex` — a **cofinite** subset of `ℂ` is Euclidean-dense.
  This is the analytic heart of the curve reduction: on an irreducible algebraic
  curve, the open set `U` is cofinite, and a cofinite subset of the curve's
  (one-dimensional, perfect) Euclidean topology is dense. Pulled back along a
  parametrisation `ℂ → Γ` this is exactly density of a cofinite subset of `ℂ`.
  Proved via `Dense.diff_finite` (a `T1`, no-isolated-points space, which `ℂ` is).

* `cofinite_roots_complex` — the parameter set where a **nonzero** single-variable
  complex polynomial is non-zero is cofinite (`Polynomial.finite_setOf_isRoot`),
  hence dense. This is the concrete source of cofiniteness: restricting a
  polynomial that does not vanish identically on the curve to a parametrisation
  gives a nonzero `q : ℂ[X]` whose non-vanishing locus is `U` pulled back.

* `curveReduction_euclideanDense` — the reduction skeleton: if every point `T ∈ X`
  is `δ t₀` for a **continuous** coordinate-curve `δ : ℂ → (Fin k → ℂ)` whose
  image lies in coordinates of `X` and along which `U` is **cofinite**, then
  `U` is Euclidean-dense in `X`. This packages the curve-density step so the only
  remaining content is the *existence* of such a curve. -/

/-- A **cofinite** subset of `ℂ` is Euclidean-dense (`ℂ` is `T1` with no isolated
points, so `Dense.diff_finite` applies). The 1-D density core of Serre's
curve reduction. -/
private lemma dense_compl_finite_complex {s : Set ℂ} (hs : sᶜ.Finite) :
    Dense s := by
  have h := (dense_univ (X := ℂ)).diff_finite (t := sᶜ) hs
  rwa [show (Set.univ \ sᶜ) = s by ext x; simp] at h

/-- The non-vanishing locus of a **nonzero** single-variable complex polynomial is
cofinite in `ℂ`. The concrete source of cofiniteness in the curve reduction:
restricting a polynomial that does not vanish identically along an irreducible
curve to a parametrisation yields such a `q`. -/
private lemma cofinite_roots_complex {q : Polynomial ℂ} (hq : q ≠ 0) :
    { t : ℂ | q.eval t = 0 }.Finite := by
  simpa [Polynomial.IsRoot] using Polynomial.finite_setOf_isRoot hq

/-- **Curve-reduction skeleton** for Serre 1956 Prop. 5,
`serre1956.tex:236` ("réduction au cas d'une courbe").

If every coordinate point `T ∈ euclideanCoord '' X` of the variety lies on a
**continuous** coordinate-curve `δ : ℂ → (Fin k → ℂ)` (the Euclidean image of an
irreducible algebraic curve `Γ ⊆ X` through the point, via a parametrisation
`ℂ → Γ`), along which the open set `A = euclideanCoord '' U` is **cofinite**
(`Γ ⊄ X \ U`, so `Γ ∩ (X\U)` is a proper closed subset of the curve, hence
finite), then `A` is Euclidean-dense in `X`'s coordinate image: every point of
`X` is a Euclidean limit of points of `U`.

This is the **analytic** one-dimensional part of the reduction. The algebraic
ingredient is the existence of the curve `δ` through a given point of an
irreducible variety, with `U` cofinite on it; see
`irreducible_zariskiOpenDense_euclideanDense`. -/
private lemma curveReduction_euclideanDense {k : ℕ} (A X : Set (Fin k → ℂ))
    (H : ∀ T ∈ X, ∃ (δ : ℂ → (Fin k → ℂ)) (t₀ : ℂ),
        Continuous δ ∧ δ t₀ = T ∧ { t : ℂ | δ t ∉ A }.Finite) :
    X ⊆ closure A := by
  intro T hTX
  obtain ⟨δ, t₀, hδ_cont, hδ0, hfin⟩ := H T hTX
  have hdense : Dense { t : ℂ | δ t ∈ A } := by
    refine dense_compl_finite_complex ?_
    rwa [show { t : ℂ | δ t ∈ A }ᶜ = { t : ℂ | δ t ∉ A } by ext t; simp]
  have ht0 : t₀ ∈ closure { t : ℂ | δ t ∈ A } := hdense t₀
  have hmem : δ t₀ ∈ closure (δ '' { t : ℂ | δ t ∈ A }) :=
    map_mem_closure hδ_cont ht0 (fun t ht => Set.mem_image_of_mem δ ht)
  rw [hδ0] at hmem
  refine closure_mono ?_ hmem
  rintro y ⟨t, ht, rfl⟩
  exact ht

/-! ### Variety identity-theorem reduction

The curve-existence hypothesis of `curveReduction_euclideanDense` is *equivalent*
to the **variety identity theorem**: a polynomial that does not vanish identically
on the irreducible variety `X` has a relative zero locus that is Euclidean-nowhere-
dense in `X` (equivalently, its non-vanishing locus is Euclidean-dense in `X`).
This is the genuine analytic crux of Serre 1956 Prop. 5 and is strictly sharper
(a single polynomial-vanishing statement) than the curve-existence/parametrisation
package. The reduction below shows this identity-theorem hypothesis *suffices* for
`EuclideanDenseIn U X`. The identity-theorem input is the relativisation to `X` of
the ambient statement `dense_compl_zeroLocus`. -/

/-- `euclideanCoord` is injective: it is `Finsupp.coe ∘ (finBasis ℂ V).repr` and
`repr` is a linear equivalence. -/
private lemma euclideanCoord_injective :
    Function.Injective (euclideanCoord : V → Fin (Module.finrank ℂ V) → ℂ) := by
  intro S T hST
  have : (Module.finBasis ℂ V).repr S = (Module.finBasis ℂ V).repr T := by
    ext i; exact congrFun hST i
  exact (Module.finBasis ℂ V).repr.injective this

/-- The coordinate image of the open set `U` is the coordinate image of `X` minus
the coordinate image of the complement `X \ U` (uses injectivity of
`euclideanCoord` so the images do not overlap). -/
private lemma euclideanCoord_image_open_eq {X U : Set V} (hUX : U ⊆ X) :
    euclideanCoord '' U
      = euclideanCoord '' X \ euclideanCoord '' (X \ U) := by
  ext x
  constructor
  · rintro ⟨T, hTU, rfl⟩
    refine ⟨⟨T, hUX hTU, rfl⟩, ?_⟩
    rintro ⟨S, hSdiff, hST⟩
    have : S = T := euclideanCoord_injective hST
    exact hSdiff.2 (this ▸ hTU)
  · rintro ⟨⟨T, hTX, rfl⟩, hxnot⟩
    refine ⟨T, ?_, rfl⟩
    by_contra hTU
    exact hxnot ⟨T, ⟨hTX, hTU⟩, rfl⟩

/-- **Variety identity-theorem reduction**.

If for every polynomial `p` that does not vanish identically on `X` the relative
non-vanishing locus `euclideanCoord '' X ∩ {x | eval x p ≠ 0}` is Euclidean-dense
in `euclideanCoord '' X` (the **variety identity theorem**, `hID`), and if the
complement `X \ U` is contained in the zero locus of some polynomial `f` that does
*not* vanish identically on `X`, then `U` is Euclidean-dense in `X`.

This reduces Serre 1956 Prop. 5 to the single identity-theorem input `hID`, the
relativisation to `X` of the ambient statement `dense_compl_zeroLocus`. -/
private lemma euclideanDense_of_identityTheorem {X U : Set V} (hUX : U ⊆ X)
    {f : MvPolynomial (Fin (Module.finrank ℂ V)) ℂ}
    (hf_compl : ∀ T ∈ X \ U, MvPolynomial.eval (euclideanCoord T) f = 0)
    (_hf_nonzero : ∃ T ∈ X, MvPolynomial.eval (euclideanCoord T) f ≠ 0)
    (hID : euclideanCoord '' X ⊆
      closure (euclideanCoord '' X ∩
        { x : Fin (Module.finrank ℂ V) → ℂ | MvPolynomial.eval x f ≠ 0 })) :
    EuclideanDenseIn U X := by
  -- The relative non-vanishing locus is contained in `euclideanCoord '' U`.
  have hsub : euclideanCoord '' X ∩
      { x : Fin (Module.finrank ℂ V) → ℂ | MvPolynomial.eval x f ≠ 0 }
        ⊆ euclideanCoord '' U := by
    rintro x ⟨⟨T, hTX, rfl⟩, hxf⟩
    rw [euclideanCoord_image_open_eq hUX]
    refine ⟨⟨T, hTX, rfl⟩, ?_⟩
    rintro ⟨S, hSdiff, hST⟩
    apply hxf
    rw [← hST]
    exact hf_compl S hSdiff
  -- Density of the bigger set forces density of `euclideanCoord '' U`.
  intro T hTX
  have hmem : euclideanCoord T ∈
      closure (euclideanCoord '' X ∩
        { x : Fin (Module.finrank ℂ V) → ℂ | MvPolynomial.eval x f ≠ 0 }) :=
    hID (Set.mem_image_of_mem euclideanCoord hTX)
  exact closure_mono hsub hmem

/-! ### Kraft representation bridge

The Kraft curve theorem `Semicontinuity.Baire.exists_curve_through_point` lives in
the `MvPolynomial.zeroLocus`/`aeval` world over `(Fin n → ℂ)`; `BaireProperty`
lives in the abstract Zariski world over `V` via `euclideanCoord`. This block
relates the two languages:

* `evalEqAeval` — `MvPolynomial.eval x p = aeval x p` over `ℂ` (`aeval_eq_eval`,
  `rfl` since the algebra is `ℂ` over itself).
* `vanishingIdeal_baire_eq` — the in-file `vanishingIdeal_baire X` is exactly
  Mathlib's `vanishingIdeal ℂ (euclideanCoord '' X)`.
* `zeroLocus_vanishingIdeal_image` — for an ambient Zariski-**closed** `X`,
  `zeroLocus ℂ (vanishingIdeal ℂ (euclideanCoord '' X)) = euclideanCoord '' X`.
* `isPrime_vanishingIdeal_image_of_irreducible` — `IsZariskiIrred X` ⟹ that ideal
  is **prime** (the algebraic ⟸ geometric Nullstellensatz half, proved from the
  in-file irreducibility def by the standard `pq` cover argument). -/

/-- `MvPolynomial.eval x = aeval x` over `ℂ` (the algebra is `ℂ` over itself). -/
private lemma evalEqAeval {k : ℕ} (x : Fin k → ℂ) (p : MvPolynomial (Fin k) ℂ) :
    MvPolynomial.eval x p = MvPolynomial.aeval x p :=
  (MvPolynomial.aeval_eq_eval x ▸ rfl)

/-- A polynomial `p` lies in `MvPolynomial.vanishingIdeal ℂ (euclideanCoord '' X)`
iff the polynomial function `T ↦ eval (euclideanCoord T) p` vanishes on `X`. -/
private lemma mem_vanishingIdeal_image_iff (X : Set V)
    (p : MvPolynomial (Fin (Module.finrank ℂ V)) ℂ) :
    p ∈ MvPolynomial.vanishingIdeal ℂ (euclideanCoord '' X)
      ↔ ∀ T ∈ X, MvPolynomial.eval (euclideanCoord T) p = 0 := by
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  constructor
  · intro h T hTX
    rw [evalEqAeval]
    exact h (euclideanCoord T) ⟨T, hTX, rfl⟩
  · intro h x hx
    obtain ⟨T, hTX, rfl⟩ := hx
    rw [← evalEqAeval]
    exact h T hTX

/-- A point `T ∈ V` has `euclideanCoord T ∈ zeroLocus ℂ (vanishingIdeal ℂ
(euclideanCoord '' X))` iff `T ∈ zariskiClosure X`. The membership half of the
representation bridge, proved directly from the definition of `zariskiClosure`. -/
private lemma mem_zeroLocus_image_iff_zariskiClosure (X : Set V) (T : V) :
    euclideanCoord T ∈ MvPolynomial.zeroLocus ℂ
        (MvPolynomial.vanishingIdeal ℂ (euclideanCoord '' X))
      ↔ T ∈ zariskiClosure (F := ℂ) X := by
  rw [MvPolynomial.mem_zeroLocus_iff]
  constructor
  · -- zero-locus membership ⟹ Zariski-closure membership.
    intro h f hf hfX
    obtain ⟨p, hp⟩ := hf
    -- `p` vanishes on `euclideanCoord '' X` (since `f` vanishes on `X`).
    have hpmem : p ∈ MvPolynomial.vanishingIdeal ℂ (euclideanCoord '' X) :=
      (mem_vanishingIdeal_image_iff X p).2 (fun S hS => by
        show MvPolynomial.eval (euclideanCoord S) p = 0
        rw [show euclideanCoord S = fun i => (Module.finBasis ℂ V).repr S i from rfl,
          ← hp S]
        exact hfX S hS)
    -- `f T = eval (euclideanCoord T) p = aeval (euclideanCoord T) p = 0`.
    have hfT : f T = MvPolynomial.aeval (euclideanCoord T) p := by
      rw [hp T, ← evalEqAeval]; rfl
    rw [hfT]; exact h p hpmem
  · -- Zariski-closure membership ⟹ zero-locus membership.
    intro h p hp
    rw [← evalEqAeval]
    -- the polynomial function `T ↦ eval (euclideanCoord T) p` vanishes on `X`.
    have hpf : IsPolynomialFunction (F := ℂ)
        (fun S : V => MvPolynomial.eval (euclideanCoord S) p) := ⟨p, fun _ => rfl⟩
    have hpX : ∀ S ∈ X, MvPolynomial.eval (euclideanCoord S) p = 0 :=
      (mem_vanishingIdeal_image_iff X p).1 hp
    exact h _ hpf hpX

/-- For an **ambient Zariski-closed** `X ⊆ V`, the `MvPolynomial` zero locus of the
vanishing ideal of `euclideanCoord '' X` is exactly `euclideanCoord '' X`. -/
private lemma zeroLocus_vanishingIdeal_image {X : Set V}
    (hX_closed : IsZariskiClosed (F := ℂ) X) :
    MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ (euclideanCoord '' X))
      = euclideanCoord '' X := by
  apply le_antisymm
  · -- a point `x` of the zero locus lies in `euclideanCoord '' X`.
    intro x hx
    -- pull `x` back through the coordinate iso: `x = euclideanCoord T₀`.
    set T₀ : V := (Module.finBasis ℂ V).repr.symm
      (Finsupp.equivFunOnFinite.symm x) with hT₀
    have hxT₀ : euclideanCoord T₀ = x := by
      funext i
      simp only [euclideanCoord, hT₀, LinearEquiv.apply_symm_apply]
      rfl
    rw [← hxT₀] at hx ⊢
    have hmemClosure : T₀ ∈ zariskiClosure (F := ℂ) X :=
      (mem_zeroLocus_image_iff_zariskiClosure X T₀).1 hx
    rw [hX_closed] at hmemClosure
    exact ⟨T₀, hmemClosure, rfl⟩
  · -- `euclideanCoord '' X ⊆ zeroLocus (vanishingIdeal (euclideanCoord '' X))`.
    exact MvPolynomial.zeroLocus_vanishingIdeal_le (euclideanCoord '' X)

/-- **Irreducible ⟹ prime** (the algebraic ⟸ geometric Nullstellensatz half).

If `X` is Zariski-irreducible (`IsZariskiIrred`), then the vanishing ideal of its
coordinate image `euclideanCoord '' X` is a **prime** ideal of
`MvPolynomial (Fin (finrank ℂ V)) ℂ`.

Proof (standard): the ideal is proper (`X` nonempty ⟹ `1 ∉ I`); if `p * q ∈ I`
then `euclideanCoord '' X ⊆ zeroLocus(p) ∪ zeroLocus(q)`. Pulling the two zero loci
back along `euclideanCoord` gives two Zariski-closed sets `Yp, Yq` of `V` whose
union covers `X`; irreducibility yields `X ⊆ Yp` or `X ⊆ Yq`, i.e. `p ∈ I` or
`q ∈ I`. -/
private lemma isPrime_vanishingIdeal_image_of_irreducible {X : Set V}
    (hX_irr : IsZariskiIrred X) :
    (MvPolynomial.vanishingIdeal ℂ (euclideanCoord '' X)).IsPrime := by
  obtain ⟨hX_ne, hX_closed, hX_irred⟩ := hX_irr
  set I := MvPolynomial.vanishingIdeal ℂ (euclideanCoord '' X) with hI
  constructor
  · -- `I ≠ ⊤`: otherwise `1 ∈ I` vanishes at the coordinate of a point of `X`.
    intro htop
    obtain ⟨T₀, hT₀⟩ := hX_ne
    have h1 : (1 : MvPolynomial (Fin (Module.finrank ℂ V)) ℂ) ∈ I := htop ▸ Submodule.mem_top
    have := h1 (euclideanCoord T₀) ⟨T₀, hT₀, rfl⟩
    simp at this
  · -- prime: `p * q ∈ I ⟹ p ∈ I ∨ q ∈ I`.
    intro p q hpq
    -- The pullbacks of `zeroLocus p`, `zeroLocus q` to `V`, as Zariski-closed sets.
    set Yp : Set V := { T : V | MvPolynomial.eval (euclideanCoord T) p = 0 } with hYp
    set Yq : Set V := { T : V | MvPolynomial.eval (euclideanCoord T) q = 0 } with hYq
    -- `Yp` is Zariski-closed: it is `zariskiClosure Yp = Yp` because `Yp` is the zero
    -- set of the polynomial function `T ↦ eval (euclideanCoord T) p`.
    have hpf : IsPolynomialFunction (F := ℂ)
        (fun T : V => MvPolynomial.eval (euclideanCoord T) p) :=
      ⟨p, fun T => rfl⟩
    have hqf : IsPolynomialFunction (F := ℂ)
        (fun T : V => MvPolynomial.eval (euclideanCoord T) q) :=
      ⟨q, fun T => rfl⟩
    have hYp_closed : IsZariskiClosed (F := ℂ) Yp := by
      apply le_antisymm _ (subset_zariskiClosure_baire Yp)
      intro T hT
      exact hT _ hpf (fun S hS => hS)
    have hYq_closed : IsZariskiClosed (F := ℂ) Yq := by
      apply le_antisymm _ (subset_zariskiClosure_baire Yq)
      intro T hT
      exact hT _ hqf (fun S hS => hS)
    -- `X ⊆ Yp ∪ Yq`: `pq` vanishes on `euclideanCoord '' X`, so at each `T ∈ X`
    -- either `p` or `q` vanishes.
    have hcover : X ⊆ Yp ∪ Yq := by
      intro T hTX
      have hpqT : MvPolynomial.eval (euclideanCoord T) (p * q) = 0 := by
        rw [evalEqAeval]
        exact hpq (euclideanCoord T) ⟨T, hTX, rfl⟩
      rw [map_mul, mul_eq_zero] at hpqT
      rcases hpqT with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases hX_irred Yp Yq hYp_closed hYq_closed hcover with hXp | hXq
    · left
      intro x hx
      obtain ⟨T, hTX, rfl⟩ := hx
      rw [← evalEqAeval]
      exact hXp hTX
    · right
      intro x hx
      obtain ⟨T, hTX, rfl⟩ := hx
      rw [← evalEqAeval]
      exact hXq hTX

/-! ### Curve Euclidean density

The Kraft curve theorem's RIGHT disjunct supplies an irreducible curve
`C = zeroLocus ℂ Q ⊆ zeroLocus ℂ I` through `z`, meeting the dense open
`{aeval · f ≠ 0}`, and **finite over a line** (an injective integral
`ψ : ℂ[t] ↪ coordRing C`). The 1-D analytic payoff is that `z` is then in the
Euclidean closure of `C ∩ {f ≠ 0}`: on the curve, `f` has only finitely many
zeros (it is nonzero there since `C` meets `{f ≠ 0}`), so its non-vanishing locus
is cofinite, hence Euclidean-dense — this is Serre's own "réduction au cas d'une
courbe" (`serre1956.tex:236`), whose one-dimensional core is
`curveReduction_euclideanDense` / `dense_compl_finite_complex`.

The input `curve_point_in_closure` is purely one-dimensional: it needs the curve
`C` parametrised by a continuous finite-fibred map
`δ : ℂ → C(ℂ-points)` extracted from the integral `ψ : ℂ[t] ↪ coordRing C`
(normalisation of a complex affine curve as a continuous finite map of ℂ-points). -/

open Semicontinuity.Baire in
/-- **Curve Euclidean density** (Serre 1956 `serre1956.tex:236`, "réduction au cas
d'une courbe"; Kraft AI.4.5 curve, kraft tex:7229–7231).

From the RIGHT disjunct of `exists_curve_through_point` — an irreducible curve
`C = zeroLocus ℂ Q ⊆ zeroLocus ℂ I` through `z`, meeting `{aeval · f ≠ 0}`, finite
over a line via injective integral `ψ : ℂ[t] ↪ coordRing C` — the point `z` lies in
the Euclidean closure of `zeroLocus ℂ I ∩ {aeval · f ≠ 0}`.

The geometric content is: a nonempty Zariski-open `{aeval · f ≠ 0} ∩ C`
is Euclidean-dense in the irreducible curve `C` (`z` is not Euclidean-isolated
in `C`). More generally this is the statement that a nonempty Zariski-open subset
of a variety is dense in the classical (Euclidean) topology.

**Source: Mumford, _Algebraic Geometry I: Complex Projective Varieties_,
Theorem (2.33)**:
"Let `X ⊆ ℙⁿ` be an `r`-dimensional variety and `X₀` a Zariski-open set in `X`;
then the classical closure of `X₀` is `X`." Its proof (Steps I-III, tex:1837-1877,
"following G. Stolzenberg") is elementary:
  (2.32) project from a linear centre `M` (tex:1812) with `p_M⁻¹(p_M c) = {c}`
    (isolate `c` on its fibre); `p_M(X)` is a hypersurface `F=0`, monic of degree
    `d` in the last coordinate (projective Noether normalisation);
  Step I: along the line `ε₀ + t·a` pick `tᵢ → 0` with `f(ε₀+tᵢa) ≠ 0` (finite
    roots of a 1-variable polynomial);
  Step II: lift to roots `βᵢ` of `Fᵢ`; product of roots `= a_d(ε₀+tᵢa)/α → 0`
    (Vieta — Mathlib has `Polynomial.prod_roots`/Vieta + root continuity), so
    `bᵢ → c`;
  Step III: lift `bᵢ` to `cᵢ ∈ X`; `ℙⁿ` is classically compact, so a subsequence
    `cᵢ → c_∞`; `p_M(c_∞)=p_M(c)` and `p_M⁻¹(p_M c)={c}` imply `c_∞ = c`;
    `f(cᵢ)≠0` gives `c ∈ classical closure(X₀)`.

For the affine curve case, Mumford Steps I-II are run in an affine chart using the
Kraft-supplied integral `ψ : ℂ[t] ↪ coordRing C`, so `C` is finite over the
`t`-line. Step III's projective compactness is replaced by affine monic-root
boundedness: the lifts lie in a fixed compact polydisc, then
`IsCompact.tendsto_subseq` supplies a convergent subsequence.

Auxiliary ingredients from `Baire/Mumford233.lean`:
* `roots_mem_closedBall_of_cauchyBound_le` (Mumford Step III, tex:1871):
  Cauchy-bound root confinement; one fixed `closedBall` holds every root of a
  uniformly-bounded family.
* `exists_seq_tendsto_avoiding_roots` (Mumford Step I, tex:1849): `∃ tᵢ → t₀`
  avoiding the finite zero set of a nonzero `ℂ[X]`.
* `prod_roots_eq` + `exists_root_pow_le_prod_norm` (Mumford Step II, tex:1869):
  product of roots `= ±coeff0/lead`, so a small constant term forces a
  small-modulus root (the `βᵢ → 0` mechanism).
* `closure_mono` from `C ∩ {f≠0} ⊆ zeroLocus I ∩ {f≠0}`
  (`zeroLocus_anti_mono` + `I ≤ Q`) reduces to the affine `r = 1` curve statement
  `Mumford233Curve.mumford233_affine_curve_open_dense_from_isolation`, fed by the
  affine (2.32) `Mumford233Curve.mumford232_affine_fibre_isolating_parameter`.

Mumford curve inputs from `Baire/Mumford233Curve.lean`:
* `mumford232_affine_fibre_isolating_parameter` (affine Mumford (2.32),
  tex:1812-1834, following G. Stolzenberg) — ∃ a refined finite parameter
  `ψiso : ℂ[t] ↪ 𝒪(C)` (injective + integral) with singleton fibre over `z`
  (`baseValue` separation via `t' = t + λs`, generic `λ`).
* `mumford233_isolated_parameter_approximating_sequence` (Steps I-III,
  tex:1835-1877) — given the singleton fibre, produce `uᵢ ∈ C ∩ {f≠0}` with
  `uᵢ → z`. The easy branch is `aeval z f ≠ 0`, where the constant sequence
  suffices. The hard branch is `aeval z f = 0`, `fbar ≠ 0` in `𝒪(C)`: the Step I
  lying-over construction of a nonzero `ℂ[t]`-norm of `fbar` whose non-roots give
  fibres meeting `{f≠0}`, then lift (lying-over), confine by boundedness, use
  `tendsto_subseq`, identify the limit with `z` by the singleton fibre, and apply
  `mem_closure_of_tendsto` as in
  `mumford233_affine_curve_open_dense_from_isolation`. -/
private lemma mumford233_affine_curve_open_dense {n : ℕ}
    {Q : Ideal (MvPolynomial (Fin n) ℂ)} [Q.IsPrime]
    {z : Fin n → ℂ} (hzQ : z ∈ MvPolynomial.zeroLocus ℂ Q)
    {f : MvPolynomial (Fin n) ℂ}
    (hmeet : (MvPolynomial.zeroLocus ℂ Q ∩
        {x : Fin n → ℂ | MvPolynomial.aeval x f ≠ 0}).Nonempty)
    (ψ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ]
      Semicontinuity.Baire.coordRing (MvPolynomial.zeroLocus ℂ Q))
    (hψ_inj : Function.Injective ψ) (hψ_int : ψ.toRingHom.IsIntegral) :
    z ∈ closure (MvPolynomial.zeroLocus ℂ Q ∩
      {x : Fin n → ℂ | MvPolynomial.aeval x f ≠ 0}) := by
  obtain ⟨s, hIso⟩ :=
    Semicontinuity.Baire.Mumford233Curve.mumford232_affine_fibre_isolating_parameter
      hzQ ψ hψ_inj hψ_int
  exact
    Semicontinuity.Baire.Mumford233Curve.mumford233_affine_curve_open_dense_from_isolation
      hzQ hmeet ψ hψ_inj hψ_int s hIso

/-- **Mumford (2.33), affine curve wire-in.** Given `I ≤ Q`, antitonicity of
`MvPolynomial.zeroLocus` gives `zeroLocus ℂ Q ⊆ zeroLocus ℂ I`. Thus the affine
curve-density statement for `C = zeroLocus ℂ Q` implies the desired ambient
closure statement by `closure_mono`.

The analytic/algebraic input is
`mumford233_affine_curve_open_dense`, the affine `r = 1` form of Mumford,
*Algebraic Geometry I*, Theorem (2.33), proof Steps I--III
(Mumford, *Algebraic Geometry I*, Theorem (2.33), proof Steps I--III), together
with Proposition (2.32)
(Mumford, *Algebraic Geometry I*, Proposition (2.32)). -/
private lemma curve_point_in_closure {n : ℕ}
    {I Q : Ideal (MvPolynomial (Fin n) ℂ)} [I.IsPrime] [Q.IsPrime]
    (hIQ : I ≤ Q) {z : Fin n → ℂ} (hzQ : z ∈ MvPolynomial.zeroLocus ℂ Q)
    {f : MvPolynomial (Fin n) ℂ}
    (hmeet : (MvPolynomial.zeroLocus ℂ Q ∩
        {x : Fin n → ℂ | x ∈ MvPolynomial.zeroLocus ℂ I ∧ MvPolynomial.aeval x f ≠ 0}).Nonempty)
    (ψ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ]
      Semicontinuity.Baire.coordRing (MvPolynomial.zeroLocus ℂ Q))
    (hψ_inj : Function.Injective ψ) (hψ_int : ψ.toRingHom.IsIntegral) :
    z ∈ closure (MvPolynomial.zeroLocus ℂ I ∩
      {x : Fin n → ℂ | MvPolynomial.aeval x f ≠ 0}) := by
  have hmeetQ : (MvPolynomial.zeroLocus ℂ Q ∩
      {x : Fin n → ℂ | MvPolynomial.aeval x f ≠ 0}).Nonempty := by
    rcases hmeet with ⟨x, hxQ, _hxI, hxf⟩
    exact ⟨x, hxQ, hxf⟩
  exact closure_mono
    (by
      intro x hx
      exact ⟨MvPolynomial.zeroLocus_anti_mono hIQ hx.1, hx.2⟩)
    (mumford233_affine_curve_open_dense hzQ hmeetQ ψ hψ_inj hψ_int)

/-- **Irreducible-case Serre 1956 GAGA Prop. 5**.
Serre 1956, Géométrie Algébrique et Géométrie Analytique, Prop. 5
(`serre1956.tex:236`, Remark).

For an **irreducible** complex algebraic variety `X` and a non-empty Zariski-open
Zariski-dense subset `U ⊆ X`, `U` is Euclidean-dense in `X`: every point of `X`
is a Euclidean limit of points of `U`.

This is the irreducible heart of Serre's Proposition 5. The proof is the genuine
complex-analytic content that Mathlib does not yet have:

* The complement `Y = X \ U` is a proper Zariski-closed (hence analytic) subset of
  the irreducible variety `X`. By the identity theorem for analytic functions on the
  connected complex manifold `X^reg` (smooth locus of an irreducible variety is
  connected), a proper analytic subvariety is nowhere dense in the Euclidean
  topology, so its complement `U` is Euclidean-dense.
* Serre phrases this via injectivity of `θ : 𝒪_x → ℋ_x` (algebraic → analytic local
  ring) at each `x ∈ X`; the Remark notes it can be proved by reduction to the
  case of a curve.

The required Mathlib complex-analytic-geometry facts (the genuine gap) are:
(i) the smooth locus of an irreducible complex variety is connected, and
(ii) a proper analytic subvariety of a connected complex manifold is nowhere dense
     (analytic identity theorem).

Two special cases used in this file are:

* The **ambient affine-space** shadow `dense_compl_zeroLocus`: the zero locus of a
  nonzero `MvPolynomial` over `ℂ` is nowhere dense in `ℂᵏ`, via the multivariable
  identity theorem `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`.

* The **1-dimensional analytic core** of Serre's own curve reduction
  (`serre1956.tex:236`, "réduction au cas d'une courbe"):
  `curveReduction_euclideanDense` + `dense_compl_finite_complex` +
  `cofinite_roots_complex`. These give the analytic content of the
  reduction: once a point `T ∈ X` is parametrised by a continuous coordinate-curve
  `δ : ℂ → ℂᵏ` along which `U` is cofinite, `EuclideanDenseIn` follows.

The proof below reduces the algebraic part to a single polynomial-vanishing
statement.

* From the hypotheses (`X` irreducible, `U` Zariski-open and Zariski-dense in `X`)
  the proof extracts an explicit `MvPolynomial` `f` that vanishes on
  the complement `X \ U` but **not** identically on `X` (via `X ⊄ C` from
  irreducibility + non-emptiness of `U`, which is itself forced by Zariski-density).

* The reduction `euclideanDense_of_identityTheorem` then shows that
  `EuclideanDenseIn U X` follows from the identity-theorem input

    hID :  euclideanCoord '' X ⊆ closure (euclideanCoord '' X ∩ {x | eval x f ≠ 0})

Here `hID` is obtained from the Kraft AI.4.5 curve theorem
`Semicontinuity.Baire.exists_curve_through_point`.

* **Representation bridge.** `I := vanishingIdeal ℂ
  (euclideanCoord '' X)` is PRIME (`isPrime_vanishingIdeal_image_of_irreducible`,
  from `IsZariskiIrred`) and `zeroLocus ℂ I = euclideanCoord '' X`
  (`zeroLocus_vanishingIdeal_image`, from `IsZariskiClosed (F := ℂ) X`); `eval = aeval`
  (`evalEqAeval`). A point `euclideanCoord T ∈ euclideanCoord '' X` becomes a point
  `z ∈ zeroLocus ℂ I`, and `exists_curve_through_point` applies.

* **Curve density.** Its LEFT disjunct (`aeval z f ≠ 0`) puts `z` in the
  set directly (`subset_closure`). Its RIGHT disjunct supplies the Kraft curve
  `C = zeroLocus ℂ Q ⊆ zeroLocus ℂ I` through `z`, meeting `{f ≠ 0}`, finite over a
  line via `ψ : ℂ[t] ↪ coordRing C`; `curve_point_in_closure` gives
  `z ∈ closure (zeroLocus ℂ I ∩ {f ≠ 0})`.

`curve_point_in_closure` reduces, via `closure_mono` and `zeroLocus_anti_mono`, to
the affine `r = 1` curve statement. The curve statement uses
`mumford232_affine_fibre_isolating_parameter` and
`mumford233_isolated_parameter_approximating_sequence`; mathematically this is a
continuous finite-fibred parametrisation `δ : ℂ → (Fin n → ℂ)` of the curve `C`
extracted from the integral injective `ψ : ℂ[t] ↪ coordRing C` (complex affine-curve
normalisation as a continuous map of `ℂ`-points; Serre's "réduction au cas d'une
courbe", `serre1956.tex:236`). Given `δ`, `curveReduction_euclideanDense` and
`dense_compl_finite_complex` provide Euclidean density on the curve. -/
private lemma irreducible_zariskiOpenDense_euclideanDense {X U : Set V}
    (hX_irr : IsZariskiIrred X)
    (hU_open : IsZariskiOpenIn U X) (hU_dense : IsZariskiDenseIn U X) :
    EuclideanDenseIn U X := by
  classical
  obtain ⟨hX_ne, hX_closed, _hX_irred⟩ := hX_irr
  obtain ⟨hUX, C, hC_closed, hdiff⟩ := hU_open
  -- `U` is forced nonempty: if `U = ∅` then `zariskiClosure U = ∅` (`zariskiClosed_empty_baire`),
  -- contradicting `X ⊆ zariskiClosure U` with `X` nonempty.
  have hU_ne : U.Nonempty := by
    rcases U.eq_empty_or_nonempty with hUe | hUne
    · exfalso
      obtain ⟨T₀, hT₀⟩ := hX_ne
      have : T₀ ∈ zariskiClosure (F := ℂ) (∅ : Set V) := by
        have := hU_dense hT₀; rwa [hUe] at this
      rw [zariskiClosed_empty_baire (V := V)] at this
      exact this.elim
    · exact hUne
  -- From irreducibility, `X ⊄ C`: otherwise `X \ U = X ∩ C = X` ⟹ `U = ∅`.
  have hXnotC : ¬ X ⊆ C := by
    intro hXC
    obtain ⟨T, hTU⟩ := hU_ne
    have hTdiff : T ∈ X \ U := by
      rw [hdiff]; exact ⟨hUX hTU, hXC (hUX hTU)⟩
    exact hTdiff.2 hTU
  -- Hence a polynomial `f` vanishing on `C` (so on `X \ U`) but not on all of `X`.
  obtain ⟨T₀, hT₀X, hT₀C⟩ : ∃ T ∈ X, T ∉ C := by
    by_contra h
    push_neg at h
    exact hXnotC h
  -- `T₀ ∉ C = zariskiClosure C` gives a polynomial function `g` vanishing on `C`
  -- with `g T₀ ≠ 0`; pull back to an `MvPolynomial`.
  rw [← hC_closed] at hT₀C
  simp only [zariskiClosure, Set.mem_setOf_eq, not_forall] at hT₀C
  obtain ⟨g, hg_poly, hgC, hgT₀⟩ := hT₀C
  obtain ⟨f, hf⟩ := hg_poly
  -- `f` vanishes on `X \ U ⊆ C`, but `f` does not vanish at `T₀ ∈ X`.
  have hf_compl : ∀ T ∈ X \ U, MvPolynomial.eval (euclideanCoord T) f = 0 := by
    intro T hT
    have hTC : T ∈ C := by rw [hdiff] at hT; exact hT.2
    have := hgC T hTC
    rw [hf T] at this
    simpa [euclideanCoord] using this
  have hf_nonzero : ∃ T ∈ X, MvPolynomial.eval (euclideanCoord T) f ≠ 0 := by
    refine ⟨T₀, hT₀X, ?_⟩
    rw [hf T₀] at hgT₀
    simpa [euclideanCoord] using hgT₀
  -- Use the **variety identity theorem** `hID`: the relative
  -- non-vanishing locus of `f` is Euclidean-dense in `euclideanCoord '' X`.
  -- This is the relativisation to `X` of the ambient `dense_compl_zeroLocus`.
  -- **the Kraft representation bridge.** Set `I := vanishingIdeal (euclideanCoord '' X)`;
  -- it is prime (irreducibility) and its zero locus is `euclideanCoord '' X` (closedness).
  have hID : euclideanCoord '' X ⊆
      closure (euclideanCoord '' X ∩
        { x : Fin (Module.finrank ℂ V) → ℂ | MvPolynomial.eval x f ≠ 0 }) := by
    set I : Ideal (MvPolynomial (Fin (Module.finrank ℂ V)) ℂ) :=
      MvPolynomial.vanishingIdeal ℂ (euclideanCoord '' X) with hI
    haveI hIprime : I.IsPrime :=
      isPrime_vanishingIdeal_image_of_irreducible ⟨hX_ne, hX_closed, _hX_irred⟩
    have hZL : MvPolynomial.zeroLocus ℂ I = euclideanCoord '' X :=
      zeroLocus_vanishingIdeal_image hX_closed
    -- Rewrite the target closure in `zeroLocus`/`aeval` language.
    have hset_eq : euclideanCoord '' X ∩
        { x : Fin (Module.finrank ℂ V) → ℂ | MvPolynomial.eval x f ≠ 0 }
          = MvPolynomial.zeroLocus ℂ I ∩
            { x : Fin (Module.finrank ℂ V) → ℂ | MvPolynomial.aeval x f ≠ 0 } := by
      rw [hZL]
      ext x; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, evalEqAeval]
    rw [hset_eq]
    -- `hf` in `aeval` language for the curve theorem.
    have hf_aeval : ∃ w ∈ MvPolynomial.zeroLocus ℂ I, MvPolynomial.aeval w f ≠ 0 := by
      obtain ⟨T, hTX, hT⟩ := hf_nonzero
      refine ⟨euclideanCoord T, ?_, ?_⟩
      · rw [hZL]; exact ⟨T, hTX, rfl⟩
      · rwa [← evalEqAeval]
    -- Take an arbitrary point `euclideanCoord T` of `euclideanCoord '' X = zeroLocus I`.
    rintro x ⟨T, hTX, rfl⟩
    have hz : euclideanCoord T ∈ MvPolynomial.zeroLocus ℂ I := by
      rw [hZL]; exact ⟨T, hTX, rfl⟩
    -- **the curve disjunction.**
    rcases Semicontinuity.Baire.exists_curve_through_point hz hf_aeval with hleft | hright
    · -- LEFT: `euclideanCoord T` already non-vanishing — directly in the set.
      exact subset_closure ⟨hleft.1, hleft.2⟩
    · -- RIGHT: the Kraft curve `C = zeroLocus Q ⊆ zeroLocus I` through `z`.
      obtain ⟨Q, hQprime, hIQ, hzQ, hmeet, ψ, hψ_inj, hψ_int⟩ := hright
      haveI : Q.IsPrime := hQprime
      exact curve_point_in_closure hIQ hzQ hmeet ψ hψ_inj hψ_int
  exact euclideanDense_of_identityTheorem hUX hf_compl hf_nonzero hID

/-! ## Noetherianity infrastructure for the finite irreducible decomposition.

The following block ports, upstream of `EuclideanClosed.lean`, the
vanishing-ideal / Noetherianity machinery used downstream by
`IsZariskiClosed.exists_irreducible_decomposition`
(`ZariskiSublevel.lean` defines `vanishingIdeal`; `EuclideanClosed.lean` defines
`ZariskiClosedSet` and proves `zariskiClosedProperSubset_wf`). Since
`BaireProperty` imports only `Defs`, the pieces are reproduced here from
Mathlib's `MvPolynomial.isNoetherianRing_fin`. No analytic content. -/

/-- The **vanishing ideal** of `A ⊆ V` (ported from `ZariskiSublevel.lean:4349`):
    polynomials whose evaluation at the coordinates `euclideanCoord T` vanishes
    for every `T ∈ A`. -/
private def vanishingIdeal_baire (A : Set V) :
    Ideal (MvPolynomial (Fin (Module.finrank ℂ V)) ℂ) where
  carrier := { p | ∀ T ∈ A, MvPolynomial.eval (euclideanCoord T) p = 0 }
  add_mem' {p q} hp hq := fun T hT => by simp [map_add, hp T hT, hq T hT]
  zero_mem' := fun T _ => by simp
  smul_mem' _ {p} hp := fun T hT => by simp [hp T hT]

/-- `vanishingIdeal_baire` is antitone (ported from `ZariskiSublevel.lean:4367`). -/
private lemma vanishingIdeal_baire_antitone {A B : Set V} (h : A ⊆ B) :
    vanishingIdeal_baire (V := V) B ≤ vanishingIdeal_baire (V := V) A :=
  fun _p hp T hT => hp T (h hT)

/-- A point `T` lies in `zariskiClosure A` iff every polynomial in
    `vanishingIdeal_baire A` evaluates to zero at `T` (ported from
    `ZariskiSublevel.lean:4395`). -/
private lemma mem_zariskiClosure_iff_eval_vanishingIdeal_baire (A : Set V) (T : V) :
    T ∈ zariskiClosure (F := ℂ) A ↔
      ∀ p ∈ vanishingIdeal_baire (V := V) A,
        MvPolynomial.eval (euclideanCoord T) p = 0 := by
  constructor
  · intro hT p hp
    refine hT (fun S => MvPolynomial.eval (euclideanCoord S) p) ⟨p, fun _ => rfl⟩ ?_
    intro S hSA
    exact hp S hSA
  · intro hT f hf hfA
    obtain ⟨p, hp⟩ := hf
    rw [hp T]
    exact hT p (fun S hS => by
      change (MvPolynomial.eval fun i => (Module.finBasis ℂ V).repr S i) p = 0
      rw [← hp S]; exact hfA S hS)

/-- For Zariski-closed `A ⊆ B` with equal vanishing ideals, `A = B`
    (ported from `ZariskiSublevel.lean:4409`). -/
private lemma eq_of_vanishingIdeal_eq_baire {A B : Set V}
    (hA_closed : IsZariskiClosed (F := ℂ) A) (hB_closed : IsZariskiClosed (F := ℂ) B)
    (hAB : A ⊆ B)
    (hI : vanishingIdeal_baire (V := V) A = vanishingIdeal_baire (V := V) B) :
    A = B := by
  apply Set.eq_of_subset_of_subset hAB
  intro T hTB
  rw [← hA_closed, mem_zariskiClosure_iff_eval_vanishingIdeal_baire]
  intro p hpA
  rw [hI] at hpA
  exact (mem_zariskiClosure_iff_eval_vanishingIdeal_baire (V := V) B T).1
    (hB_closed ▸ subset_zariskiClosure_baire B hTB) p hpA

/-- The intersection of two Zariski-closed sets is Zariski-closed
    (ported from `EuclideanClosed.lean:77`). -/
private lemma zariskiClosed_inter_baire {A B : Set V}
    (hA : IsZariskiClosed (F := ℂ) A) (hB : IsZariskiClosed (F := ℂ) B) :
    IsZariskiClosed (F := ℂ) (A ∩ B) := by
  unfold IsZariskiClosed at hA hB ⊢
  apply Set.eq_of_subset_of_subset
  · intro T hT
    refine ⟨?_, ?_⟩
    · rw [← hA]
      intro f hf hfA
      exact hT f hf (fun S hS => hfA S hS.1)
    · rw [← hB]
      intro f hf hfB
      exact hT f hf (fun S hS => hfB S hS.2)
  · exact subset_zariskiClosure_baire (A ∩ B)

/-- The subtype of Zariski-closed sets (ported from `EuclideanClosed.lean:235`). -/
private abbrev ZariskiClosedSet_baire (V : Type v) [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] := { A : Set V // IsZariskiClosed (F := ℂ) A }

/-- Strict inclusion among Zariski-closed sets (ported from
    `EuclideanClosed.lean:239`). -/
private def zariskiClosedProperSubset_baire
    (A B : ZariskiClosedSet_baire V) : Prop := A.1 ⊂ B.1

/-- Strict inclusion among Zariski-closed sets is well-founded, by Noetherianity
    of `MvPolynomial (Fin (finrank ℂ V)) ℂ` through the order-reversing
    `vanishingIdeal_baire` map (ported from `EuclideanClosed.lean:242`). -/
private lemma zariskiClosedProperSubset_baire_wf :
    WellFounded (zariskiClosedProperSubset_baire (V := V)) := by
  classical
  let R := MvPolynomial (Fin (Module.finrank ℂ V)) ℂ
  haveI : IsNoetherianRing R := MvPolynomial.isNoetherianRing_fin
  let I : ZariskiClosedSet_baire V → Ideal R :=
    fun A => vanishingIdeal_baire (V := V) A.1
  refine Subrelation.wf (r := InvImage ((· > ·) : Ideal R → Ideal R → Prop) I) ?_
    (InvImage.wf I (inferInstance : WellFoundedGT (Ideal R)).wf)
  intro A B hAB
  dsimp [zariskiClosedProperSubset_baire] at hAB
  dsimp [InvImage, I]
  have hle : vanishingIdeal_baire (V := V) B.1 ≤
      vanishingIdeal_baire (V := V) A.1 :=
    vanishingIdeal_baire_antitone hAB.1
  refine lt_of_le_of_ne hle ?_
  intro hEq
  apply hAB.2
  have hsets : A.1 = B.1 :=
    eq_of_vanishingIdeal_eq_baire A.2 B.2 hAB.1 hEq.symm
  exact hsets ▸ subset_rfl

/-- **Finite irreducible decomposition** of a non-empty Zariski-closed set
    (Noetherianity of the Zariski topology, `MvPolynomial.isNoetherianRing`,
    paper tex:1169). This is proved downstream as
    `IsZariskiClosed.exists_irreducible_decomposition` in `EuclideanClosed.lean`,
    using the well-foundedness of strict inclusion among Zariski-closed sets via
    the strict descent of vanishing ideals in a Noetherian polynomial ring. Ported
    here (upstream of that file) so that the reducible → irreducible reduction of
    Serre Prop. 5 can be assembled in this file. No analytic content. -/
private lemma exists_irreducible_decomposition_baire
    (X : Set V) (hX_ne : X.Nonempty) (hX_closed : IsZariskiClosed (F := ℂ) X) :
    ∃ (s : Finset (Set V)), s.Nonempty ∧ X = ⋃ Y ∈ s, Y ∧
      ∀ Y ∈ s, IsZariskiClosed (F := ℂ) Y ∧ IsZariskiIrred Y := by
  classical
  let P : ZariskiClosedSet_baire V → Prop := fun X =>
    X.1.Nonempty →
      ∃ (s : Finset (Set V)), s.Nonempty ∧ X.1 = ⋃ Y ∈ s, Y ∧
        ∀ Y ∈ s, IsZariskiClosed (F := ℂ) Y ∧ IsZariskiIrred Y
  have hP : ∀ X : ZariskiClosedSet_baire V,
      (∀ Y : ZariskiClosedSet_baire V,
        zariskiClosedProperSubset_baire Y X → P Y) → P X := by
    intro X ih hX_ne
    by_cases hX_irred : IsZariskiIrred X.1
    · refine ⟨{X.1}, by simp, ?_, ?_⟩
      · ext T
        simp
      · intro Y hY
        simp only [Finset.mem_singleton] at hY
        subst hY
        exact ⟨X.2, hX_irred⟩
    · have hnot :
          ¬ ∀ Y Z : Set V, IsZariskiClosed (F := ℂ) Y → IsZariskiClosed (F := ℂ) Z →
            X.1 ⊆ Y ∪ Z → X.1 ⊆ Y ∨ X.1 ⊆ Z := by
        intro h
        exact hX_irred ⟨hX_ne, X.2, h⟩
      push_neg at hnot
      rcases hnot with ⟨Y, Z, hY_closed, hZ_closed, hcover, hX_not_Y, hX_not_Z⟩
      let XY : ZariskiClosedSet_baire V :=
        ⟨X.1 ∩ Y, zariskiClosed_inter_baire X.2 hY_closed⟩
      let XZ : ZariskiClosedSet_baire V :=
        ⟨X.1 ∩ Z, zariskiClosed_inter_baire X.2 hZ_closed⟩
      have hXY_ssub : zariskiClosedProperSubset_baire XY X := by
        constructor
        · intro T hT
          exact hT.1
        · intro h
          exact hX_not_Y fun T hTX => (h hTX).2
      have hXZ_ssub : zariskiClosedProperSubset_baire XZ X := by
        constructor
        · intro T hT
          exact hT.1
        · intro h
          exact hX_not_Z fun T hTX => (h hTX).2
      have hXY_ne : XY.1.Nonempty := by
        rcases Set.not_subset.mp hX_not_Z with ⟨T, hTX, hTZ⟩
        have hTY : T ∈ Y := by
          rcases hcover hTX with hTY | hTZ'
          · exact hTY
          · exact (hTZ hTZ').elim
        exact ⟨T, hTX, hTY⟩
      have hXZ_ne : XZ.1.Nonempty := by
        rcases Set.not_subset.mp hX_not_Y with ⟨T, hTX, hTY⟩
        have hTZ : T ∈ Z := by
          rcases hcover hTX with hTY' | hTZ
          · exact (hTY hTY').elim
          · exact hTZ
        exact ⟨T, hTX, hTZ⟩
      rcases ih XY hXY_ssub hXY_ne with ⟨sY, hsY_ne, hXY_union, hsY⟩
      rcases ih XZ hXZ_ssub hXZ_ne with ⟨sZ, hsZ_ne, hXZ_union, hsZ⟩
      refine ⟨sY ∪ sZ, Finset.Nonempty.inl hsY_ne, ?_, ?_⟩
      · ext T
        constructor
        · intro hTX
          rcases hcover hTX with hTY | hTZ
          · have hTXY : T ∈ XY.1 := ⟨hTX, hTY⟩
            rw [hXY_union] at hTXY
            rcases Set.mem_iUnion.mp hTXY with ⟨W, hW⟩
            rcases Set.mem_iUnion.mp hW with ⟨hWsY, hTW⟩
            exact Set.mem_iUnion.mpr ⟨W,
              Set.mem_iUnion.mpr ⟨Finset.mem_union.mpr (Or.inl hWsY), hTW⟩⟩
          · have hTXZ : T ∈ XZ.1 := ⟨hTX, hTZ⟩
            rw [hXZ_union] at hTXZ
            rcases Set.mem_iUnion.mp hTXZ with ⟨W, hW⟩
            rcases Set.mem_iUnion.mp hW with ⟨hWsZ, hTW⟩
            exact Set.mem_iUnion.mpr ⟨W,
              Set.mem_iUnion.mpr ⟨Finset.mem_union.mpr (Or.inr hWsZ), hTW⟩⟩
        · intro hT
          rcases Set.mem_iUnion.mp hT with ⟨W, hW⟩
          rcases Set.mem_iUnion.mp hW with ⟨hWs, hTW⟩
          rcases Finset.mem_union.mp hWs with hWsY | hWsZ
          · have hTWXY : T ∈ XY.1 := by
              rw [hXY_union]
              exact Set.mem_iUnion.mpr ⟨W, Set.mem_iUnion.mpr ⟨hWsY, hTW⟩⟩
            exact hTWXY.1
          · have hTWXZ : T ∈ XZ.1 := by
              rw [hXZ_union]
              exact Set.mem_iUnion.mpr ⟨W, Set.mem_iUnion.mpr ⟨hWsZ, hTW⟩⟩
            exact hTWXZ.1
      · intro W hWs
        rcases Finset.mem_union.mp hWs with hWsY | hWsZ
        · exact hsY W hWsY
        · exact hsZ W hWsZ
  exact (zariskiClosedProperSubset_baire_wf (V := V)).induction
    ⟨X, hX_closed⟩ hP hX_ne

/-- Serre 1956, Géométrie Algébrique et Géométrie Analytique, Prop. 5
(Serre, *Géométrie algébrique et géométrie analytique*, Prop. 5):
A Zariski-OPEN and Zariski-DENSE subset `U` of a complex algebraic variety `X`
is Euclidean-dense in `X`. Both hypotheses are needed — Euclidean-open subsets
that are not Zariski-open can be Zariski-dense without being Euclidean-dense.

Proof from `serre_remark_polynomial_vanishes_on_zariskiClosed`:
By contradiction, assume no `S ∈ X \ C` has `euclideanCoord S ∈ O`. Then
`X ∩ euclideanCoord⁻¹' O ⊆ C`. Pick any polynomial `q` vanishing on `C`; then
`q` vanishes on `X ∩ euclideanCoord⁻¹' O`. The Serre Remark sub-helper extends
the vanishing from the Euclidean-open piece to all of `X`. Hence every polynomial
vanishing on `C` vanishes on `X`, i.e., `X ⊆ zariskiClosure C = C`. Combined
with `h_dense : X ⊆ zariskiClosure (X \ C)`, applied to a chosen polynomial that
separates `T` from `∅` we derive a contradiction. -/
private lemma relative_polynomial_identity_theorem_open_meets_compl {X C : Set V}
    (hX_closed : IsZariskiClosed (F := ℂ) X) (hC_closed : IsZariskiClosed (F := ℂ) C)
    (h_dense : IsZariskiDenseIn (X \ C) X) {T : V} (hTX : T ∈ X)
    {O : Set (Fin (Module.finrank ℂ V) → ℂ)}
    (hO_open : IsOpen O) (hTO : euclideanCoord T ∈ O) :
    ∃ S ∈ X \ C, euclideanCoord S ∈ O := by
  classical
  -- REDUCIBLE → IRREDUCIBLE reduction (this part is proved).
  -- Decompose X into finitely many irreducible components.
  have hX_ne : X.Nonempty := ⟨T, hTX⟩
  obtain ⟨s, _hs_ne, hX_union, hs_irred⟩ :=
    exists_irreducible_decomposition_baire (V := V) X hX_ne hX_closed
  -- The "good" components are those NOT contained in `C`.  Because `X \ C` is
  -- Zariski-dense in `X`, the good components already cover `X`: every point of
  -- `X \ C` lies in a good component, so `X \ C ⊆ ⋃_{good} Y`, a Zariski-closed
  -- set, hence `X ⊆ zariskiClosure (X \ C) ⊆ ⋃_{good} Y`.
  let G : Finset (Set V) := s.filter (fun Y => ¬ Y ⊆ C)
  have hXC_subset_G : (X \ C) ⊆ ⋃ Y ∈ G, Y := by
    intro z hz
    have hzX : z ∈ X := hz.1
    rw [hX_union] at hzX
    rcases Set.mem_iUnion₂.mp hzX with ⟨Y, hYs, hzY⟩
    have hY_notC : ¬ Y ⊆ C := by
      intro hYC
      exact hz.2 (hYC hzY)
    exact Set.mem_iUnion₂.mpr ⟨Y, Finset.mem_filter.mpr ⟨hYs, hY_notC⟩, hzY⟩
  have hG_closed : IsZariskiClosed (F := ℂ) (⋃ Y ∈ G, Y) :=
    zariskiClosed_biUnion_baire G (fun Y => Y)
      (fun Y hY => (hs_irred Y (Finset.mem_filter.mp hY).1).1)
  have hX_subset_G : X ⊆ ⋃ Y ∈ G, Y :=
    h_dense.trans (zariskiClosure_minimal_baire hXC_subset_G hG_closed)
  -- `T` lies in some good component `X₀`.
  have hTG : T ∈ ⋃ Y ∈ G, Y := hX_subset_G hTX
  rcases Set.mem_iUnion₂.mp hTG with ⟨X₀, hX₀G, hTX₀⟩
  obtain ⟨hX₀s, hX₀_notC⟩ := Finset.mem_filter.mp hX₀G
  have hX₀_irr : IsZariskiIrred X₀ := (hs_irred X₀ hX₀s).2
  have hX₀_closed : IsZariskiClosed (F := ℂ) X₀ := (hs_irred X₀ hX₀s).1
  have hX₀_sub_X : X₀ ⊆ X := by
    rw [hX_union]; intro w hw; exact Set.mem_iUnion₂.mpr ⟨X₀, hX₀s, hw⟩
  -- `U₀ := X₀ \ C` is a non-empty Zariski-open subset of the irreducible `X₀`,
  -- hence Zariski-dense in `X₀`.
  set U₀ : Set V := X₀ \ C with hU₀_def
  have hU₀_open : IsZariskiOpenIn U₀ X₀ := by
    refine ⟨Set.diff_subset, C, hC_closed, ?_⟩
    ext w
    constructor
    · rintro ⟨hwX₀, hwU₀⟩
      refine ⟨hwX₀, ?_⟩
      by_contra hwC
      exact hwU₀ ⟨hwX₀, hwC⟩
    · rintro ⟨hwX₀, hwC⟩
      exact ⟨hwX₀, fun h => h.2 hwC⟩
  have hU₀_ne : U₀.Nonempty := by
    rcases Set.not_subset.mp hX₀_notC with ⟨w, hwX₀, hwC⟩
    exact ⟨w, hwX₀, hwC⟩
  have hU₀_dense : IsZariskiDenseIn U₀ X₀ :=
    zariskiOpenIn_dense_of_irred_baire hX₀_irr hU₀_open hU₀_ne
  -- IRREDUCIBLE CORE: `U₀` is Euclidean-dense in `X₀`.
  have hU₀_eucl : EuclideanDenseIn U₀ X₀ :=
    irreducible_zariskiOpenDense_euclideanDense hX₀_irr hU₀_open hU₀_dense
  -- Therefore the Euclidean neighbourhood `O` of `T` meets `U₀ ⊆ X \ C`.
  have hT_closure : euclideanCoord T ∈ closure (euclideanCoord '' U₀) :=
    hU₀_eucl hTX₀
  rw [mem_closure_iff] at hT_closure
  obtain ⟨x, hxO, hx_mem⟩ := hT_closure O hO_open hTO
  obtain ⟨S, hSU₀, hSx⟩ := hx_mem
  refine ⟨S, ⟨hX₀_sub_X hSU₀.1, hSU₀.2⟩, ?_⟩
  rw [hSx]; exact hxO

private lemma zariskiDenseIn_compl_zariskiClosed_euclideanDenseIn_aux {X C : Set V}
    (hX_closed : IsZariskiClosed (F := ℂ) X) (hC_closed : IsZariskiClosed (F := ℂ) C)
    (h_dense : IsZariskiDenseIn (X \ C) X) :
    EuclideanDenseIn (X \ C) X := by
  intro T hTX
  change euclideanCoord T ∈ closure (euclideanCoord '' (X \ C))
  rw [mem_closure_iff]
  intro O hO_open hTO
  rcases relative_polynomial_identity_theorem_open_meets_compl
      (V := V) hX_closed hC_closed h_dense hTX hO_open hTO with
    ⟨S, hSXC, hSO⟩
  exact ⟨euclideanCoord S, hSO, ⟨S, hSXC, rfl⟩⟩

private lemma zariskiDenseIn_compl_zariskiClosed_euclideanDenseIn {X C : Set V}
    (hX_closed : IsZariskiClosed (F := ℂ) X) (hC_closed : IsZariskiClosed (F := ℂ) C)
    (h_dense : IsZariskiDenseIn (X \ C) X) :
    EuclideanDenseIn (X \ C) X :=
  zariskiDenseIn_compl_zariskiClosed_euclideanDenseIn_aux
    hX_closed hC_closed h_dense

lemma zariskiDenseIn_euclideanDenseIn {U X : Set V}
    (hX_closed : IsZariskiClosed (F := ℂ) X)
    (hU_open : IsZariskiOpenIn U X) (hU_dense : IsZariskiDenseIn U X) :
    EuclideanDenseIn U X := by
  rcases hU_open with ⟨hUX, C, hC_closed, hXU⟩
  have hU_eq : U = X \ C := by
    ext T
    constructor
    · intro hTU
      refine ⟨hUX hTU, ?_⟩
      intro hTC
      have hTdiff : T ∈ X \ U := by
        rw [hXU]
        exact ⟨hUX hTU, hTC⟩
      exact hTdiff.2 hTU
    · rintro ⟨hTX, hTC⟩
      by_contra hTU
      have hTdiff : T ∈ X \ U := ⟨hTX, hTU⟩
      rw [hXU] at hTdiff
      exact hTC hTdiff.2
  have h_dense_compl : IsZariskiDenseIn (X \ C) X := by
    simpa [← hU_eq] using hU_dense
  have h_euclidean_compl : EuclideanDenseIn (X \ C) X :=
    zariskiDenseIn_compl_zariskiClosed_euclideanDenseIn
      (V := V) hX_closed hC_closed h_dense_compl
  intro T hTX
  refine closure_mono ?_ (h_euclidean_compl hTX)
  rintro x ⟨S, hS, rfl⟩
  refine ⟨S, ?_, rfl⟩
  rw [hU_eq]
  exact hS

/-- Paper tex:1118. A Euclidean-dense subset of a complex affine set is Zariski-dense:
polynomial functions are Euclidean-continuous, so vanishing extends from a dense set. -/
lemma euclideanDenseIn_zariskiDenseIn {A X : Set V}
    (hA : EuclideanDenseIn A X) :
    IsZariskiDenseIn A X := by
  intro T hTX f hf hfA
  rcases hf with ⟨p, hp⟩
  have hT_closure : euclideanCoord T ∈ closure (euclideanCoord '' A) := hA hTX
  have hzero_closed : IsClosed { x : Fin (Module.finrank ℂ V) → ℂ |
      MvPolynomial.eval x p = 0 } :=
    isClosed_eq (MvPolynomial.continuous_eval p) continuous_const
  have hzero_on_image :
      euclideanCoord '' A ⊆ { x : Fin (Module.finrank ℂ V) → ℂ |
        MvPolynomial.eval x p = 0 } := by
    intro x hx
    rcases hx with ⟨S, hSA, rfl⟩
    exact (hp S).symm.trans (hfA S hSA)
  have hzero_on_closure :
      closure (euclideanCoord '' A) ⊆ { x : Fin (Module.finrank ℂ V) → ℂ |
        MvPolynomial.eval x p = 0 } :=
    (IsClosed.closure_subset_iff hzero_closed).2 hzero_on_image
  have hpT : MvPolynomial.eval (euclideanCoord T) p = 0 :=
    hzero_on_closure hT_closure
  simpa [hp T] using hpT

/-- Paper tex:1118. A Zariski-closed complex affine set is a Baire space in the
Euclidean topology, so a countable intersection of Euclidean-open dense subsets is
Euclidean-dense. -/
lemma euclideanDenseIn_iInter_of_zariskiClosed
    (X : Set V) (_hX_ne : X.Nonempty) (hX_closed : IsZariskiClosed (F := ℂ) X)
    (U : ℕ → Set V)
    (hU_open : ∀ i, EuclideanOpenIn (U i) X)
    (hU_dense : ∀ i, EuclideanDenseIn (U i) X) :
    EuclideanDenseIn (⋂ i, U i) X := by
  rcases zariskiClosed_image_eq_coordSet (V := V) hX_closed with
    ⟨Z, hZ_closed, hXZ, hX_image⟩
  choose O hO_open hU_eq using hU_open
  let W : ℕ → Set Z := fun i => { x : Z | (x : Fin (Module.finrank ℂ V) → ℂ) ∈ O i }
  have hW_open : ∀ i, IsOpen (W i) := by
    intro i
    exact hO_open i |>.preimage continuous_subtype_val
  have hcoord_U_subset : ∀ i, euclideanCoord '' U i ⊆ Subtype.val '' W i := by
    intro i x hx
    rcases hx with ⟨T, hTU, rfl⟩
    have hTXO : T ∈ X ∩ euclideanCoord ⁻¹' O i := by
      rw [← hU_eq i]
      exact hTU
    have hxZ : euclideanCoord T ∈ Z := by
      rw [← hX_image]
      exact ⟨T, hTXO.1, rfl⟩
    exact ⟨⟨euclideanCoord T, hxZ⟩, hTXO.2, rfl⟩
  have hW_dense : ∀ i, Dense (W i) := by
    intro i
    rw [Subtype.dense_iff]
    intro x hx
    have hx' : x ∈ euclideanCoord '' X := by
      rw [hX_image]
      exact hx
    rcases hx' with ⟨T, hTX, rfl⟩
    exact closure_mono (hcoord_U_subset i) (hU_dense i hTX)
  haveI : CompleteSpace Z := hZ_closed.completeSpace_coe
  haveI : BaireSpace Z := inferInstance
  have hW_iInter_dense : Dense (⋂ i, W i) :=
    dense_iInter_of_isOpen_nat hW_open hW_dense
  rw [Subtype.dense_iff] at hW_iInter_dense
  intro T hTX
  change euclideanCoord T ∈ closure (euclideanCoord '' ⋂ i, U i)
  have hcoordZ : euclideanCoord T ∈ Z := by
    rw [← hX_image]
    exact ⟨T, hTX, rfl⟩
  refine closure_mono ?_ (hW_iInter_dense hcoordZ)
  intro x hx
  rcases hx with ⟨xZ, hxW, rfl⟩
  have hx_mem_Z : (xZ : Fin (Module.finrank ℂ V) → ℂ) ∈ euclideanCoord '' X := by
    rw [hX_image]
    exact xZ.2
  rcases hx_mem_Z with ⟨S, hSX, hScoord⟩
  refine ⟨S, ?_, hScoord⟩
  rw [Set.mem_iInter]
  intro i
  have hSO : euclideanCoord S ∈ O i := by
    rw [hScoord]
    exact Set.mem_iInter.mp hxW i
  rw [hU_eq i]
  exact ⟨hSX, hSO⟩

/-- **Lemma 4.2** (tex:1102-1131, `\label{lem:baire-property}`).

The intersection of countably many Zariski-open, Zariski-dense subsets of a
non-empty Zariski-closed `X ⊆ V` (complex vector space) is Zariski-dense in `X`. -/
theorem zariski_baire
    (X : Set V) (hX_ne : X.Nonempty) (hX_closed : IsZariskiClosed (F := ℂ) X)
    (U : ℕ → Set V)
    (hU_open : ∀ i, IsZariskiOpenIn (U i) X)
    (hU_dense : ∀ i, IsZariskiDenseIn (U i) X) :
    IsZariskiDenseIn (⋂ i, U i) X := by
  have hU_euclidean_open : ∀ i, EuclideanOpenIn (U i) X := fun i =>
    zariskiOpenIn_euclideanOpenIn (V := V) (hU_open i)
  have hU_euclidean_dense : ∀ i, EuclideanDenseIn (U i) X := fun i =>
    zariskiDenseIn_euclideanDenseIn (V := V) hX_closed (hU_open i) (hU_dense i)
  have hInter_euclidean_dense : EuclideanDenseIn (⋂ i, U i) X :=
    euclideanDenseIn_iInter_of_zariskiClosed (V := V) X hX_ne hX_closed U
      hU_euclidean_open hU_euclidean_dense
  exact euclideanDenseIn_zariskiDenseIn (V := V) hInter_euclidean_dense

end Semicontinuity
