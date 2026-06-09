/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Ring.Basic
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Abstract quadratic-form decomposition for a general-position orthogonal representation

This file formalizes the quadratic-form decomposition at the heart of the Vrana–Christandl
degeneration (Corollary 3.5), over an **abstract** orthogonal representation `c` of the line
graph `L(H)` of a hypergraph `H = ([k], E, I)`.

## Source

Vrana–Christandl, arXiv:1603.03964 (`genmamu.tex`), lines 136-158.

Given a system of linear equalities `∑_e c_e i_e = g` with `c : E → ℤ^D`, `g ∈ ℤ^D`, subtracting
`g` and taking the inner product with itself gives (genmamu:147-148)

  `⟨∑_e c_e i_e − g, ∑_e c_e i_e − g⟩`
    `= ⟨g,g⟩ + ∑_e (⟨c_e,c_e⟩ i_e² − 2⟨c_e,g⟩ i_e) + ∑_{e,f} ⟨c_e,c_f⟩ i_e i_f.`

genmamu:150 ("We need to distribute the terms among the vertices in such a way that an index
`i_e` can only appear at vertices incident with `e`. This is always possible for the first term
and the following sum, while the condition for the double sum is that `⟨c_e,c_f⟩ = 0` whenever
there is no vertex incident to both `e` and `f`."). That orthogonality condition is exactly
"`c : E → ℤ^d` is an orthogonal representation of the line graph `L(H)`".

The vanishing of the non-incident cross terms is what lets the degeneration use **local**
`ε`-operators (genmamu:150-157).

## Main definitions

* `absQuadForm c g i` — the squared norm `∑_r (∑_e c e r * i e − g r)²`.
* `absLocalWeight` — the per-vertex contribution; each `i_e²` / `i_e` term is assigned to the
  owning vertex `edgeOwner e`, and each (ordered) cross term `i_e i_f` to a common incident
  vertex `pairOwner e f`. The `⟨g,g⟩` term is assigned to the distinguished vertex `gVertex`.

## Main results

* `absQuadForm_eq_canon` — the algebraic expansion of `absQuadForm` (uses orthogonality to drop
  non-incident cross terms).
* `absLocalWeight_sum_eq_canon` — `∑_v absLocalWeight v` equals the same canonical expansion
  (pure partition / fiberwise reindexing).
* `absQuadForm_eq_sum_localWeights` — **the headline**: `absQuadForm c g i = ∑ v, absLocalWeight v`.
* `absQuadForm_nonneg`, `absQuadForm_eq_zero_iff` — `Q ≥ 0`, and `Q = 0 ↔ ∑_e c_e i_e = g`.

## Method

The quadratic form is developed over an abstract `c`
(`quadForm`, `localWeight`, `quadForm_eq_sum_localWeights`, `quadForm_nonneg`,
`quadForm_eq_zero_iff`), generalizing the cycle-specific representation. Here the cycle's
`cycleEdgeVec`/`prevFin'`/`next_sum_eq_prev_sum` bookkeeping is replaced by abstract
`edgeOwner` / `pairOwner` distribution functions, so the headline becomes a `sum_fiberwise`
reindexing instead of a cycle bijection.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset BigOperators

namespace VC.Degeneration

variable {E : Type*} [Fintype E] [DecidableEq E] {k D : ℕ}

/-! ### Integer dot product -/

/-- Integer dot product of two vectors in `ℤ^D`. -/
def idot (u v : Fin D → ℤ) : ℤ := ∑ r : Fin D, u r * v r

lemma idot_comm (u v : Fin D → ℤ) : idot u v = idot v u := by
  unfold idot; apply Finset.sum_congr rfl; intro r _; ring

/-! ### The quadratic form `Q` -/

/-- The linear combination `∑_e c_e i_e ∈ ℤ^D`. -/
def linComb (c : E → Fin D → ℤ) (i : E → ℤ) : Fin D → ℤ :=
  fun r => ∑ e : E, c e r * i e

/-- **The quadratic form** `Q(i) = ‖∑_e c_e i_e − g‖² = ∑_r (∑_e c_e r · i_e − g_r)²`
    (genmamu:146-148). Squared norm of the integer vector `∑_e c_e i_e − g`. -/
def absQuadForm (c : E → Fin D → ℤ) (g : Fin D → ℤ) (i : E → ℤ) : ℤ :=
  ∑ r : Fin D, (linComb c i r - g r) ^ 2

/-! ### Nonnegativity and the zero-set (sum of squares) -/

/-- `Q ≥ 0`: it is a sum of squares. -/
theorem absQuadForm_nonneg (c : E → Fin D → ℤ) (g : Fin D → ℤ) (i : E → ℤ) :
    0 ≤ absQuadForm c g i :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `Q = 0 ↔ ∑_e c_e i_e = g`. -/
theorem absQuadForm_eq_zero_iff (c : E → Fin D → ℤ) (g : Fin D → ℤ) (i : E → ℤ) :
    absQuadForm c g i = 0 ↔ ∀ r : Fin D, linComb c i r = g r := by
  simp only [absQuadForm]
  constructor
  · intro h r
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun r _ => sq_nonneg (linComb c i r - g r))).mp h r (Finset.mem_univ r)
    rwa [sq_eq_zero_iff, sub_eq_zero] at this
  · intro h
    apply Finset.sum_eq_zero
    intro r _; rw [h r, sub_self, sq, mul_zero]

/-- `Q ≥ 1` for non-solutions: if `∑_e c_e i_e ≠ g` then `Q ≥ 1` (squared norm of a nonzero
    integer vector). -/
theorem absQuadForm_pos_of_ne_sol (c : E → Fin D → ℤ) (g : Fin D → ℤ) (i : E → ℤ)
    (hne : ¬ ∀ r : Fin D, linComb c i r = g r) :
    1 ≤ absQuadForm c g i := by
  push_neg at hne
  obtain ⟨r, hr⟩ := hne
  have h1 : 1 ≤ (linComb c i r - g r) ^ 2 := by
    have : linComb c i r - g r ≠ 0 := sub_ne_zero.mpr hr
    nlinarith [sq_abs (linComb c i r - g r), abs_pos.mpr this]
  have h2 : (linComb c i r - g r) ^ 2 ≤ absQuadForm c g i :=
    Finset.single_le_sum (f := fun r => (linComb c i r - g r) ^ 2)
      (fun r _ => sq_nonneg _) (Finset.mem_univ r)
  linarith

/-! ### Algebraic expansion of `Q` into a canonical form

We expand `Q = ⟨g,g⟩ + ∑_e (⟨c_e,c_e⟩ i_e² − 2⟨c_e,g⟩ i_e) + ∑_{e,f} ⟨c_e,c_f⟩ i_e i_f`
(genmamu:148). The double sum here is over **all** ordered pairs `(e,f)`; the diagonal `e = f`
gives the `⟨c_e,c_e⟩ i_e²` summands of the middle term, and the off-diagonal contributes the
cross terms. -/

/-- `⟨∑_e c_e i_e, ∑_f c_f i_f⟩` expands to the double sum `∑_e ∑_f ⟨c_e,c_f⟩ i_e i_f`. -/
lemma idot_linComb_self (c : E → Fin D → ℤ) (i : E → ℤ) :
    idot (linComb c i) (linComb c i) =
      ∑ e : E, ∑ f : E, idot (c e) (c f) * i e * i f := by
  simp only [idot, linComb]
  trans (∑ r : Fin D, ∑ e : E, ∑ f : E, c e r * i e * (c f r * i f))
  · apply Finset.sum_congr rfl; intro r _; rw [Finset.sum_mul_sum]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro e _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro f _
    conv_lhs => arg 2; ext r; rw [show c e r * i e * (c f r * i f)
      = c e r * c f r * (i e * i f) from by ring]
    rw [← Finset.sum_mul]; ring

/-- `⟨∑_e c_e i_e, g⟩` distributes as `∑_e ⟨c_e,g⟩ i_e`. -/
lemma idot_linComb_gVec (c : E → Fin D → ℤ) (g : Fin D → ℤ) (i : E → ℤ) :
    idot (linComb c i) g = ∑ e : E, idot (c e) g * i e := by
  simp only [idot, linComb]
  trans (∑ r : Fin D, ∑ e : E, c e r * i e * g r)
  · apply Finset.sum_congr rfl; intro r _; rw [Finset.sum_mul]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro e _
    conv_lhs => arg 2; ext r; rw [show c e r * i e * g r = c e r * g r * i e from by ring]
    rw [← Finset.sum_mul]

/-- `Q = ⟨linComb, linComb⟩ − 2⟨linComb, g⟩ + ⟨g,g⟩`. -/
lemma absQuadForm_as_idot (c : E → Fin D → ℤ) (g : Fin D → ℤ) (i : E → ℤ) :
    absQuadForm c g i =
      idot (linComb c i) (linComb c i) - 2 * idot (linComb c i) g + idot g g := by
  unfold absQuadForm idot
  have hsq : ∀ r : Fin D, (linComb c i r - g r) ^ 2 =
      linComb c i r * linComb c i r - 2 * (linComb c i r * g r) + g r * g r := by
    intro r; ring
  simp_rw [hsq]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  congr 1; congr 1
  rw [← Finset.mul_sum]

/-! ### Distribution data: assigning terms to vertices

genmamu:150 distributes terms among vertices so an index `i_e` only appears at vertices
incident with `e`. We package the distribution choice as explicit "owner" functions:

* `edgeOwner e` — a vertex incident with `e` (carries the `i_e²` and `i_e` terms of `e`);
* `pairOwner e f` — a vertex incident with **both** `e` and `f`, for every off-diagonal pair
  whose inner product `⟨c_e,c_f⟩` is nonzero (orthogonality guarantees such a vertex exists);
* `gVertex` — a distinguished vertex carrying the constant `⟨g,g⟩` term.

For `L(K_k)`, an edge is a 2-subset `{a,b}`; `edgeOwner {a,b} = min a b`, and a surviving cross
pair `{a,b},{a,c}` (which must share a vertex `a`) gets `pairOwner = a`. -/

variable (inc : Fin k → E → Prop) [∀ v e, Decidable (inc v e)]

/-- Two edges are **incident** if they share a common incident vertex. The orthogonality
    hypothesis says non-incident edges have `⟨c_e,c_f⟩ = 0` (genmamu:150). -/
def edgesIncident (e f : E) : Prop := ∃ v : Fin k, inc v e ∧ inc v f

/-- The canonical expansion of `Q` (genmamu:148), written with the distribution functions so
    that the off-diagonal double sum is over **all** ordered pairs. -/
def canonForm (c : E → Fin D → ℤ) (g : Fin D → ℤ) (i : E → ℤ) : ℤ :=
  idot g g
  + ∑ e : E, (idot (c e) (c e) * i e ^ 2 - 2 * idot (c e) g * i e)
  + ∑ e : E, ∑ f ∈ Finset.univ.erase e, idot (c e) (c f) * i e * i f

/-- **Algebraic expansion of `Q`.** `Q = canonForm`. This is the step genmamu:147-148 performs:
    expand the squared norm, split the diagonal `e = f` out of the double sum to form the
    `⟨c_e,c_e⟩ i_e²` terms, and leave the off-diagonal cross terms. No orthogonality is used
    here; orthogonality enters only in the per-vertex distribution below. -/
theorem absQuadForm_eq_canon (c : E → Fin D → ℤ) (g : Fin D → ℤ) (i : E → ℤ) :
    absQuadForm c g i = canonForm c g i := by
  rw [absQuadForm_as_idot, idot_linComb_self, idot_linComb_gVec]
  simp only [canonForm]
  -- Split the diagonal e=f from the double sum.
  have hsplit : ∑ e : E, ∑ f : E, idot (c e) (c f) * i e * i f =
      ∑ e : E, idot (c e) (c e) * i e * i e
      + ∑ e : E, ∑ f ∈ Finset.univ.erase e, idot (c e) (c f) * i e * i f := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro e _
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e)]
  rw [hsplit]
  -- Now rearrange: (diag + off) − 2*∑ lin + gg = gg + ∑(self·i² − 2 lin) + off.
  have hdiag : ∑ e : E, idot (c e) (c e) * i e * i e
      = ∑ e : E, idot (c e) (c e) * i e ^ 2 := by
    apply Finset.sum_congr rfl; intro e _; ring
  rw [hdiag]
  rw [Finset.sum_sub_distrib]
  have h2 : ∑ e : E, 2 * idot (c e) g * i e = 2 * ∑ e : E, idot (c e) g * i e := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro e _; ring
  rw [h2]; ring

/-! ### The per-vertex local weight and the headline decomposition

We now require the distribution data and the orthogonality hypothesis, and read off the headline
by `Finset.sum_fiberwise`. -/

-- Distribution data (genmamu:150), passed explicitly to `absLocalWeight` and its lemmas:
-- * `edgeOwner : E → Fin k` — a vertex incident with `e`, carrying the `i_e²`/`i_e` terms;
-- * `pairOwner : E → E → Fin k` — a common incident vertex of `e,f` when `⟨c_e,c_f⟩ ≠ 0`
--   (orthogonality guarantees existence); irrelevant otherwise since the cross term vanishes;
-- * `gVertex : Fin k` — the distinguished vertex carrying the constant `⟨g,g⟩` term.

/-- **The per-vertex local weight** `w_v`.

    Collects: the `⟨g,g⟩` term (at `gVertex`), the diagonal+linear terms
    `⟨c_e,c_e⟩ i_e² − 2⟨c_e,g⟩ i_e` of edges owned by `v`, and the off-diagonal cross terms
    `⟨c_e,c_f⟩ i_e i_f` of ordered distinct pairs owned by `v`.

    By construction `∑_v w_v` reassembles `canonForm`, and an index `i_e` only appears at
    vertices `v` for which `edgeOwner e = v` (resp. `pairOwner e f = v`) — vertices incident
    with `e` once the owner functions are chosen incident (genmamu:150). -/
def absLocalWeight (edgeOwner : E → Fin k) (pairOwner : E → E → Fin k) (gVertex : Fin k)
    (c : E → Fin D → ℤ) (g : Fin D → ℤ) (i : E → ℤ) (v : Fin k) : ℤ :=
  (if v = gVertex then idot g g else 0)
  + ∑ e ∈ Finset.univ.filter (fun e => edgeOwner e = v),
      (idot (c e) (c e) * i e ^ 2 - 2 * idot (c e) g * i e)
  + ∑ e ∈ Finset.univ.filter (fun e => True),
      ∑ f ∈ (Finset.univ.erase e).filter (fun f => pairOwner e f = v),
        idot (c e) (c f) * i e * i f

/-- `∑_v w_v = canonForm` — pure partition/fiberwise reindexing of `canonForm`.

    The `⟨g,g⟩` term lands once (at `gVertex`); the edge terms are partitioned by `edgeOwner`;
    the off-diagonal pair terms are partitioned by `pairOwner`. No orthogonality is needed for
    this identity — it is bookkeeping. -/
theorem absLocalWeight_sum_eq_canon (edgeOwner : E → Fin k) (pairOwner : E → E → Fin k)
    (gVertex : Fin k) (c : E → Fin D → ℤ) (g : Fin D → ℤ) (i : E → ℤ) :
    ∑ v : Fin k, absLocalWeight edgeOwner pairOwner gVertex c g i v
      = canonForm c g i := by
  simp only [absLocalWeight, canonForm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  · congr 1
    · -- ∑_v (if v = gVertex then ⟨g,g⟩ else 0) = ⟨g,g⟩
      rw [Finset.sum_ite_eq' Finset.univ gVertex (fun _ => idot g g)]
      simp
    · -- ∑_v ∑_{edgeOwner e = v} (…) = ∑_e (…)  : fiberwise over edgeOwner
      rw [← Finset.sum_fiberwise Finset.univ edgeOwner
            (fun e => idot (c e) (c e) * i e ^ 2 - 2 * idot (c e) g * i e)]
  · -- ∑_v ∑_e ∑_{pairOwner e f = v} (…) = ∑_e ∑_{f ≠ e} (…)  : fiberwise over pairOwner
    simp only [Finset.filter_true]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro e _
    rw [← Finset.sum_fiberwise (Finset.univ.erase e) (fun f => pairOwner e f)
          (fun f => idot (c e) (c f) * i e * i f)]

/-- **Headline decomposition** (genmamu:146-158).

    `Q(i) = ∑_v w_v` — the quadratic form distributes as a sum of vertex-local weights, where
    each weight `w_v` only sees indices `i_e` for edges `e` owned by `v` (and the cross terms of
    pairs owned by `v`). Combined with the orthogonality hypothesis (genmamu:150), choosing the
    owner functions **incident** (`edgeOwner e` incident with `e`, `pairOwner e f` incident with
    both `e,f` whenever `⟨c_e,c_f⟩ ≠ 0`) makes every term that `w_v` carries depend only on
    edges incident with `v` — exactly the locality genmamu:150-157 needs for local
    `ε`-operators.

    The identity itself is `absQuadForm_eq_canon` (algebra) composed with
    `absLocalWeight_sum_eq_canon` (partition); the orthogonality enters when the owner functions
    are instantiated (see `absLocalWeight_locality`). -/
theorem absQuadForm_eq_sum_localWeights (edgeOwner : E → Fin k) (pairOwner : E → E → Fin k)
    (gVertex : Fin k) (c : E → Fin D → ℤ) (g : Fin D → ℤ) (i : E → ℤ) :
    absQuadForm c g i
      = ∑ v : Fin k, absLocalWeight edgeOwner pairOwner gVertex c g i v := by
  rw [absQuadForm_eq_canon,
    absLocalWeight_sum_eq_canon edgeOwner pairOwner gVertex c g i]

/-! ### Locality from orthogonality (genmamu:150)

The orthogonality hypothesis kills the cross terms of non-incident pairs. We record the two
consequences that make the distribution **well-defined and local**:

1. a non-incident pair contributes nothing (`cross_term_vanishes`); hence
2. every cross term that `w_v` actually carries comes from a pair sharing a vertex, and — once
   `edgeOwner`/`pairOwner` are chosen incident — `w_v` depends only on edges incident with `v`
   (`absLocalWeight_locality`). -/

/-- **Cross terms vanish for non-incident edges** (genmamu:150, the mathematical core).
    If `e,f` have no common incident vertex then `⟨c_e,c_f⟩ i_e i_f = 0`. -/
theorem cross_term_vanishes (c : E → Fin D → ℤ) (i : E → ℤ)
    (horth : ∀ e f : E, ¬ edgesIncident inc e f → idot (c e) (c f) = 0)
    (e f : E) (hnadj : ¬ edgesIncident inc e f) :
    idot (c e) (c f) * i e * i f = 0 := by
  rw [horth e f hnadj, zero_mul, zero_mul]

/-- **Locality of the per-vertex weight** (genmamu:150).

    Assume the owner functions are chosen incident:
    * `hEdgeInc : edgeOwner e` is incident with `e`;
    * `hPairInc : pairOwner e f` is incident with both `e` and `f` whenever `⟨c_e,c_f⟩ ≠ 0`.

    Then the local weight `w_v(c, g, i)` only depends on the indices `i_e` of edges `e`
    **incident with `v`**: replacing `i` by any `i'` agreeing with `i` on all edges incident
    with `v` leaves `w_v` unchanged. (The orthogonality hypothesis is what makes `pairOwner`'s
    incidence requirement non-vacuous — non-incident pairs already contribute `0`.) -/
theorem absLocalWeight_locality (edgeOwner : E → Fin k) (pairOwner : E → E → Fin k)
    (gVertex : Fin k) (c : E → Fin D → ℤ) (g : Fin D → ℤ)
    (horth : ∀ e f : E, ¬ edgesIncident inc e f → idot (c e) (c f) = 0)
    (hEdgeInc : ∀ e, inc (edgeOwner e) e)
    (hPairInc : ∀ e f, e ≠ f → idot (c e) (c f) ≠ 0 → inc (pairOwner e f) e ∧ inc (pairOwner e f) f)
    (v : Fin k) (i i' : E → ℤ)
    (hagree : ∀ e, inc v e → i e = i' e) :
    absLocalWeight edgeOwner pairOwner gVertex c g i v
      = absLocalWeight edgeOwner pairOwner gVertex c g i' v := by
  simp only [absLocalWeight]
  congr 1
  · congr 1
    -- edge terms: each surviving edge e has edgeOwner e = v, hence inc v e, so i e = i' e.
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.mem_filter] at he
    have hve : inc v e := he.2 ▸ hEdgeInc e
    rw [hagree e hve]
  · -- cross terms: each surviving (e,f) has pairOwner e f = v. If ⟨c_e,c_f⟩ = 0 the summand is
    -- 0 on both sides; otherwise inc v e ∧ inc v f, so i e = i' e and i f = i' f.
    simp only [Finset.filter_true]
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro f hf
    rw [Finset.mem_filter, Finset.mem_erase] at hf
    obtain ⟨⟨hfe, _⟩, hpo⟩ := hf
    by_cases hz : idot (c e) (c f) = 0
    · rw [hz]; ring
    · obtain ⟨hve, hvf⟩ := hPairInc e f (Ne.symm hfe) hz
      rw [hpo] at hve hvf
      rw [hagree e hve, hagree f hvf]

end VC.Degeneration
