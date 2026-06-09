/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Sequences
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Mumford (2.33) — affine Steps I / II / III building blocks

This file formalizes analytic ingredients of
**Mumford, _Algebraic Geometry I: Complex Projective Varieties_, Theorem (2.33)**
(`tex:1835-1877`, "following G. Stolzenberg"), in the **affine `r = 1`** form used
by `BaireProperty.curve_point_in_closure`.

The pieces here are the parts of the proof that are pure 1-variable complex
analysis / polynomial bookkeeping before applying the affine analogue of
Mumford (2.32):

* **Monic-root boundedness** (Mumford Step III, the affine replacement for
  `ℙⁿ`-compactness, `tex:1871`). A family of nonzero complex polynomials whose
  `cauchyBound` is uniformly bounded over a set `K` has all its roots, for
  `t ∈ K`, inside one fixed Euclidean ball `closedBall 0 R`. This confines the
  affine lifts `cᵢ ∈ X` (one coordinate at a time) to a fixed compact polydisc,
  so `IsCompact.tendsto_subseq` supplies the convergent subsequence — replacing
  Mumford's "`ℙⁿ` is compact in the classical topology".

* **Cofinite good-parameter sequence** (Mumford Step I, `tex:1849`). For
  a nonzero single-variable complex polynomial, its zero set is finite; hence
  there is a sequence `tᵢ → t₀` avoiding the zeros (any prescribed limit `t₀`).

* **Vieta product-of-roots → small root** (Mumford Step II,
  `tex:1869`). A monic complex polynomial of positive degree with small constant
  term has a root of small modulus: the product of the roots is `± (constant
  term)`, so the minimum-modulus root is `≤ |const|^{1/d}`. This is the exact
  mechanism by which `βᵢ → 0` in Mumford Step II.

The base-point/lying-over argument, the affine (2.32) fibre isolation, and the
Steps II+III assembly are handled in `Baire/Mumford233Curve.lean`.
-/

namespace Semicontinuity.Baire.Mumford233

open Polynomial Filter Topology NNReal

/-! ## Monic-root boundedness (Mumford Step III, `tex:1871`) -/

/-- **Cauchy-bound root confinement.** If every `P t` (for `t ∈ K`) is nonzero and
has Cauchy bound `≤ R`, then all roots of all these polynomials lie in the fixed
ball `Metric.closedBall (0 : ℂ) R`. Mumford (2.33) Step III replacement for
`ℙⁿ`-compactness (`tex:1871`): one fixed compact set holds every root of the
family. -/
theorem roots_mem_closedBall_of_cauchyBound_le
    {ι : Type*} {P : ι → ℂ[X]} {K : Set ι} {R : ℝ}
    (hP : ∀ t ∈ K, P t ≠ 0)
    (hR : ∀ t ∈ K, ((cauchyBound (P t) : ℝ)) ≤ R)
    {t : ι} (ht : t ∈ K) {x : ℂ} (hx : (P t).IsRoot x) :
    x ∈ Metric.closedBall (0 : ℂ) R := by
  have hlt : (‖x‖₊ : ℝ) < ((cauchyBound (P t) : ℝ)) := by
    exact_mod_cast IsRoot.norm_lt_cauchyBound (hP t ht) hx
  have hle : ‖x‖ ≤ R := le_of_lt (lt_of_lt_of_le hlt (hR t ht))
  simpa [Metric.mem_closedBall, dist_eq_norm] using hle

/-- **Single-polynomial root confinement.** Every root of a nonzero complex
polynomial `p` lies in `Metric.closedBall 0 (cauchyBound p)`. Specialisation of
`roots_mem_closedBall_of_cauchyBound_le` to one polynomial. -/
theorem isRoot_mem_closedBall_cauchyBound
    {p : ℂ[X]} (hp : p ≠ 0) {x : ℂ} (hx : p.IsRoot x) :
    x ∈ Metric.closedBall (0 : ℂ) ((cauchyBound p : ℝ)) := by
  have hlt : (‖x‖₊ : ℝ) < ((cauchyBound p : ℝ)) := by
    exact_mod_cast IsRoot.norm_lt_cauchyBound hp hx
  have hle : ‖x‖ ≤ ((cauchyBound p : ℝ)) :=
    le_of_lt (by simpa using hlt)
  simpa [Metric.mem_closedBall, dist_eq_norm] using hle

/-! ## Step I cofinite good-parameter (Mumford Step I, `tex:1849`) -/

/-- **Step I cofiniteness.** The zero set of a nonzero single-variable complex
polynomial is finite (`Polynomial.finite_setOf_isRoot`). Mumford Step I
(`tex:1849`): `f(ε₀ + t·a)` is a nonzero polynomial in `t`, so it has finitely
many zeros and there is a sequence `tᵢ → 0` along which it is nonzero. -/
theorem finite_zeroSet_of_ne_zero {q : ℂ[X]} (hq : q ≠ 0) :
    {t : ℂ | q.eval t = 0}.Finite := by
  simpa [Polynomial.IsRoot] using Polynomial.finite_setOf_isRoot hq

/-- **Step I sequence.** A nonzero complex polynomial `q` admits a sequence
`tᵢ → t₀` (to any prescribed limit `t₀`) avoiding the zeros of `q`. This is the
"choose `tᵢ → 0` with `f(ε₀ + tᵢ a) ≠ 0`" of Mumford Step I (`tex:1849`),
abstracted to an arbitrary limit point. -/
theorem exists_seq_tendsto_avoiding_roots {q : ℂ[X]} (hq : q ≠ 0) (t₀ : ℂ) :
    ∃ u : ℕ → ℂ, Tendsto u atTop (𝓝 t₀) ∧ ∀ i, q.eval (u i) ≠ 0 := by
  have hfin : {t : ℂ | q.eval t = 0}.Finite := finite_zeroSet_of_ne_zero hq
  -- The complement of a finite set is dense in ℂ (no isolated points), so `t₀`
  -- is a limit of points where `q ≠ 0`. Extract a sequence via first-countability.
  have hdense : Dense {t : ℂ | q.eval t ≠ 0} := by
    have h := (dense_univ (X := ℂ)).diff_finite (t := {t : ℂ | q.eval t = 0}) hfin
    have hset : (Set.univ \ {t : ℂ | q.eval t = 0}) = {t : ℂ | q.eval t ≠ 0} := by
      ext t; simp
    rwa [hset] at h
  have hmem : t₀ ∈ closure {t : ℂ | q.eval t ≠ 0} := hdense t₀
  rw [mem_closure_iff_seq_limit] at hmem
  obtain ⟨u, hu_mem, hu_tend⟩ := hmem
  exact ⟨u, hu_tend, hu_mem⟩

/-! ## Vieta product-of-roots → small root (Mumford Step II,
`tex:1869`) -/

/-- **Vieta: product of roots = signed constant term over leading coeff.**
For a complex polynomial `p` that splits (always, over `ℂ`), with
`p.natDegree = d`, the product of its roots (with multiplicity) equals
`(-1)^d · p.coeff 0 / p.leadingCoeff`. The `tex:1869` input "product of the roots
of `Fᵢ` is `a_d(ε₀+tᵢa)/α`". -/
theorem prod_roots_eq {p : ℂ[X]} (hp : p ≠ 0) :
    p.roots.prod = (-1) ^ p.natDegree * (p.coeff 0 / p.leadingCoeff) := by
  have hsplit : p.Splits := IsAlgClosed.splits p
  have hlead : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have hcoeff : p.coeff 0 = (-1) ^ p.natDegree * p.leadingCoeff * p.roots.prod :=
    hsplit.coeff_zero_eq_leadingCoeff_mul_prod_roots
  rw [hcoeff]
  field_simp
  rw [← pow_mul, mul_comm p.natDegree 2, pow_mul, neg_one_sq, one_pow, mul_one]

/-- **Step II small root** (Mumford `tex:1869`). A complex polynomial `p` of
positive degree has a root `β` whose modulus is bounded by
`(‖coeff 0‖ / ‖leadingCoeff‖)^(1/natDegree)` — concretely, the *minimum* modulus
over the roots is `≤` the geometric mean, and the product of moduli is
`‖coeff 0 / leadingCoeff‖`. Hence if `coeff 0 → 0` (with leading coeff bounded
away from `0`), some root `β → 0`. This is the mechanism `βᵢ → 0` of Step II:
"the product of the roots of `Fᵢ` is `a_d/α`, and since `a_d(ε₀) = 0` these tend
to `0`, so there is a sequence `βᵢ` of roots tending to `0`."

Stated as the existence of a root whose `natDegree`-th power modulus is `≤`
`‖coeff 0 / leadingCoeff‖` (i.e. `‖β‖^d ≤ ∏‖rootⱼ‖`). -/
theorem exists_root_pow_le_prod_norm {p : ℂ[X]} (hp : 0 < p.natDegree) :
    ∃ β : ℂ, p.IsRoot β ∧
      ‖β‖ ^ p.natDegree ≤ ‖p.coeff 0 / p.leadingCoeff‖ := by
  have hp0 : p ≠ 0 := fun h => by simp [h] at hp
  have hcard : p.roots.card = p.natDegree :=
    splits_iff_card_roots.1 (IsAlgClosed.splits p)
  have hne : p.roots ≠ 0 := by
    intro h; rw [h] at hcard; simp only [Multiset.card_zero] at hcard; omega
  -- The product of the root-moduli (as `ℝ≥0`) equals ‖coeff 0 / leadingCoeff‖₊.
  have hprodnorm : (p.roots.map (‖·‖₊)).prod = ‖p.coeff 0 / p.leadingCoeff‖₊ := by
    have hpr : ‖p.roots.prod‖₊ = ‖p.coeff 0 / p.leadingCoeff‖₊ := by
      rw [prod_roots_eq hp0, nnnorm_mul, nnnorm_pow, nnnorm_neg, nnnorm_one,
        one_pow, one_mul]
    rw [← hpr]
    induction p.roots using Multiset.induction with
    | empty => simp
    | cons a s ih => simp [Multiset.map_cons, Multiset.prod_cons, nnnorm_mul, ih]
  -- Pick the minimum-modulus root `β`; then `‖β‖₊ ≤ ‖rootⱼ‖₊` for every root.
  obtain ⟨β, hβmem, hβmin⟩ := Multiset.exists_min_image (‖·‖₊) hne
  refine ⟨β, Polynomial.isRoot_of_mem_roots hβmem, ?_⟩
  -- `‖β‖₊^card ≤ ∏‖rootⱼ‖₊ = ‖coeff 0 / leadingCoeff‖₊`, in the ordered monoid `ℝ≥0`.
  have hpow : ‖β‖₊ ^ (p.roots.map (‖·‖₊)).card ≤ (p.roots.map (‖·‖₊)).prod := by
    refine Multiset.pow_card_le_prod ?_
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
    exact hβmin z hz
  rw [Multiset.card_map, hcard, hprodnorm] at hpow
  -- Transfer the `ℝ≥0` inequality back to `ℝ`.
  have := (NNReal.coe_le_coe.mpr hpow)
  push_cast at this
  simpa using this

end Semicontinuity.Baire.Mumford233
