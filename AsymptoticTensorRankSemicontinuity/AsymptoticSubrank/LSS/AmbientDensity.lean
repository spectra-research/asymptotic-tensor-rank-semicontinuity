/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.RCLike.Basic

/-!
# LSS Real ambient density substrate

Source: Gortler–Theran, arXiv:2310.11565,
`the Gortler-Theran GOR proof notes`
lines 238-254 (`lem:dense`), statement:

> "If `U` is a non-empty Zariski-open subset of `GOR⁺_σ`, then `U` is dense in the
>  standard topology on `GOR⁺_σ`."

The proof pulls `U`'s defining polynomial back along `φ` to `ℝ^N`, where its
vanishing set is a proper algebraic subset and hence nowhere dense; the continuous
image of the dense complement then lands in `U`.

This file formalizes the **ambient half** of the proof of `lem:dense`
(gorProof tex:238-254): a proper real algebraic subset of `ℝ^N` is nowhere dense
in the standard topology (equivalently, the non-vanishing locus of a nonzero real
polynomial is Euclidean-dense), together with the continuous-image-of-dense
pushforward used at gorProof tex:252-253.

It is the real-coefficient analogue of the ℂ density machinery in
`BaireProperty.lean` (`dense_compl_zeroLocus` and the vanishing-on-open
lemma it rests on).

The ℂ version of the empty-interior step routes through the complex-analytic
identity theorem; over ℝ that tool is unavailable, but it is also unnecessary:
a nonempty open set on which a real polynomial vanishes already forces the
polynomial to be `0` via `MvPolynomial.funext_set` (which holds over any infinite
integral domain, ℝ included), so we route the empty-interior step through the
real port of `mvPolynomial_eq_zero_of_vanishing_on_open` directly.

The theorem statements below package the ambient-density and pushforward
ingredients used by the GOR proof.
	-/

namespace LSS.AmbientDensity

open MvPolynomial Set

/-- Helper: a non-empty open subset of `ℝ` is infinite.

Proof: from `IsOpen` get a metric ball `Metric.ball x ε` around the chosen point;
the open interval `Set.Ioo (x - ε) (x + ε)` is contained in that ball, and is
infinite because `ℝ` is order-dense (`Set.Ioo.infinite`). This is the real
analogue of the corresponding ℂ statement. -/
lemma isOpen_real_infinite_of_mem
    {B : Set ℝ} (hB : IsOpen B) {x : ℝ} (hx : x ∈ B) : B.Infinite := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hB x hx
  have h_image : Set.Ioo (x - ε) (x + ε) ⊆ B := by
    intro y hy
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor
    · linarith [hy.1]
    · linarith [hy.2]
  have h_inf : (Set.Ioo (x - ε) (x + ε)).Infinite :=
    Set.infinite_coe_iff.mp (Set.Ioo.infinite (by linarith : x - ε < x + ε))
  exact h_inf.mono h_image

/-- **Real port** (gorProof tex:250-251). A multivariate polynomial over `ℝ` that
vanishes on a non-empty Euclidean-open subset of `Fin m → ℝ` is the zero
polynomial.

Real-coefficient analogue of the ℂ vanishing-on-open lemma.

Proof: pick `a ∈ U`. By `isOpen_pi_iff'`, `U` contains a product box
`Set.univ.pi u` with each `u i` open and `a i ∈ u i`. Each `u i` is infinite by
`isOpen_real_infinite_of_mem`. Apply `MvPolynomial.funext_set` with `q = 0`
(valid over the infinite integral domain `ℝ`). -/
theorem mvPolynomial_eq_zero_of_vanishing_on_open_real
    {m : ℕ} {U : Set (Fin m → ℝ)} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    {p : MvPolynomial (Fin m) ℝ} (hvanish : ∀ x ∈ U, eval x p = 0) :
    p = 0 := by
  obtain ⟨a, ha⟩ := hU_ne
  obtain ⟨u, hu, husub⟩ := isOpen_pi_iff'.mp hU_open a ha
  have hu_inf : ∀ i : Fin m, (u i).Infinite := by
    intro i
    exact isOpen_real_infinite_of_mem (hu i).1 (hu i).2
  refine MvPolynomial.funext_set u hu_inf ?_
  intro x hx
  rw [hvanish x (husub hx), map_zero]

/-- The Euclidean zero locus of a **nonzero** `MvPolynomial` over `ℝ` has empty
interior in `ℝᵏ`: if it had an interior point, the polynomial would vanish on an
open neighbourhood, hence (by `mvPolynomial_eq_zero_of_vanishing_on_open_real`)
be the zero polynomial.

Real-coefficient analogue of `zeroLocus_interior_eq_empty` (over ℂ), but routed
through the open-set vanishing lemma rather than the complex identity theorem. -/
theorem zeroLocus_interior_eq_empty_real {k : ℕ}
    {p : MvPolynomial (Fin k) ℝ} (hp : p ≠ 0) :
    interior { x : Fin k → ℝ | eval x p = 0 } = ∅ := by
  by_contra hne
  rw [← Set.not_nonempty_iff_eq_empty, not_not] at hne
  obtain ⟨z₀, hz₀⟩ := hne
  -- The interior of the zero locus is a nonempty open set on which `p` vanishes.
  have hopen : IsOpen (interior { x : Fin k → ℝ | eval x p = 0 }) := isOpen_interior
  have hvanish : ∀ y ∈ interior { x : Fin k → ℝ | eval x p = 0 }, eval y p = 0 := by
    intro y hy
    have : y ∈ { x : Fin k → ℝ | eval x p = 0 } := interior_subset hy
    simpa using this
  exact hp (mvPolynomial_eq_zero_of_vanishing_on_open_real hopen ⟨z₀, hz₀⟩ hvanish)

/-- **Real port — ambient nowhere-density** (gorProof tex:251). The Euclidean
complement of the zero locus of a **nonzero** `MvPolynomial` over `ℝ` is dense in
`ℝᵏ`: as a proper algebraic subset, the zero set is nowhere dense.

Real-coefficient analogue of `dense_compl_zeroLocus` (over ℂ).

Proof: the zero locus is closed (`isClosed_eq` + `MvPolynomial.continuous_eval`),
and has empty interior (`zeroLocus_interior_eq_empty_real`); a closed set with
empty interior has dense complement (`interior_eq_empty_iff_dense_compl`). -/
theorem dense_compl_zeroLocus_real {k : ℕ}
    {p : MvPolynomial (Fin k) ℝ} (hp : p ≠ 0) :
    Dense { x : Fin k → ℝ | eval x p ≠ 0 } := by
  have hcompl : { x : Fin k → ℝ | eval x p ≠ 0 }
      = { x : Fin k → ℝ | eval x p = 0 }ᶜ := by
    ext x; simp [Set.mem_compl_iff]
  rw [hcompl, ← interior_eq_empty_iff_dense_compl]
  exact zeroLocus_interior_eq_empty_real hp

/-! ### Pushforward (gorProof tex:252-253)

The proof of `lem:dense` concludes: `φ(ℝ^N ∖ V)` is dense in the standard topology
on `GOR⁺_σ = closure (range φ)`. The underlying topological fact is that the
continuous image of a dense set is dense in the closure of the range.

Mathlib provides this directly as
`Continuous.range_subset_closure_image_dense :
  Continuous f → Dense s → Set.range f ⊆ closure (f '' s)`,
i.e. the range of `φ` is contained in the closure of `φ '' s` for any dense `s`.
Taking closures, `closure (range φ) ⊆ closure (φ '' s)`, which is exactly the
statement "`φ '' s` is dense in `closure (range φ)`". -/

/-- **Pushforward** (gorProof tex:252-253). If `φ` is continuous and `S` is dense
(e.g. `S = Vᶜ`, the complement of a proper real algebraic set, by
`dense_compl_zeroLocus_real`), then `closure (range φ) ⊆ closure (φ '' S)`. Hence
`φ '' S` is dense in the standard topology on `closure (range φ) = GOR⁺_σ`.

This is the clean ambient form of the final step; it is a thin specialization of
the Mathlib lemma `Continuous.range_subset_closure_image_dense`. -/
theorem closure_range_subset_closure_image_of_dense
    {N M : ℕ} {φ : (Fin N → ℝ) → (Fin M → ℝ)} (hφ : Continuous φ)
    {S : Set (Fin N → ℝ)} (hS : Dense S) :
    closure (Set.range φ) ⊆ closure (φ '' S) := by
  have h := hφ.range_subset_closure_image_dense hS
  calc closure (Set.range φ) ⊆ closure (closure (φ '' S)) := closure_mono h
    _ = closure (φ '' S) := closure_closure

/-- **Pushforward, subspace form** (gorProof tex:252-253). With the hypotheses
above, the image `φ '' S`, viewed inside the subspace `GOR⁺_σ := closure (range φ)`,
is genuinely `Dense` in the subspace topology.

Here `GOR := closure (Set.range φ)` is the standard-topology ambient set (the
GOR⁺_σ of the paper, the closure of the parameterization's image), and the dense
subset is `Subtype.val ⁻¹' (φ '' S)` — the points of `GOR` that lie in `φ '' S`.
This is the faithful "`φ(ℝ^N∖V)` is dense in `GOR⁺_σ`" of the source, obtained
from `closure_range_subset_closure_image_of_dense` via `Subtype.dense_iff`. -/
theorem dense_image_in_closure_range_of_dense
    {N M : ℕ} {φ : (Fin N → ℝ) → (Fin M → ℝ)} (hφ : Continuous φ)
    {S : Set (Fin N → ℝ)} (hS : Dense S) :
    Dense (Subtype.val ⁻¹' (φ '' S) :
      Set ↑(closure (Set.range φ))) := by
  rw [Subtype.dense_iff]
  intro y hy
  -- `Subtype.val '' (Subtype.val ⁻¹' (φ '' S)) = (φ '' S) ∩ closure (range φ)`,
  -- and `φ '' S ⊆ closure (range φ)`, so this image is just `φ '' S`.
  have himg : Subtype.val '' (Subtype.val ⁻¹' (φ '' S) :
      Set ↑(closure (Set.range φ))) = closure (Set.range φ) ∩ φ '' S := by
    rw [Subtype.image_preimage_coe]
  rw [himg]
  have hsub : φ '' S ⊆ closure (Set.range φ) :=
    (Set.image_subset_range φ S).trans subset_closure
  rw [Set.inter_eq_self_of_subset_right hsub]
  exact closure_range_subset_closure_image_of_dense hφ hS hy

end LSS.AmbientDensity
