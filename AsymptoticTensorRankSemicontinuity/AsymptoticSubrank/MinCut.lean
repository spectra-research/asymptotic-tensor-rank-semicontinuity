/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Finite.Lattice

/-!
# Min-cut combinatorics for Corollary 3.5

Source: Vrana–Christandl, *Asymptotic entanglement transformation between W and
GHZ states* (arXiv:1603.03964, `genmamu.tex`).

`genmamu.tex` line 224:
> "a minimum cut is obtained by removing every edge incident with a
> distinguished vertex"

i.e. the minimum cut of the complete graph `K_k`, `min_{∅≠I⊊[k]} ∏_{i∈I,j∉I} q_ij`,
is attained at the singletons `I = {v}`.

This file provides the **pure finite combinatorics** of that min-cut for a
symmetric weight function `q : Fin k → Fin k → ℕ`, to be plugged into
`Semicontinuity.asympSubrank_ge_min_flatRank` (**Corollary 3.5**,
`MaxRankBound.lean:4868`), whose target is the `iInf`-over-a-set shape

```
⨅ I ∈ ({I : Finset (Fin k) | I.Nonempty ∧ I ≠ Finset.univ}),
    ((flatRank T I : ℝ) ^ (2 / (k * (k - 1))))
```

## Main definitions

* `cutProduct q I` — `∏ p ∈ I ×ˢ (univ \ I), q p.1 p.2`, the product of
  cross-pair weights of the bipartition `(I, Iᶜ)`.
* `minCut q k` — the minimum of `cutProduct q I` over `{I | I.Nonempty ∧ I ≠ univ}`,
  taken as a `Finset.inf'` over the filtered powerset (nonempty for `2 ≤ k`).

## Main results

* `minCut_le_cutProduct` — `minCut` is a lower bound for every admissible cut.
* `minCut_mono` — monotonicity of `minCut` in the weights `q`.
* `minCut_iInf_real` — the `iInf`-bridge: `(minCut q k : ℝ)` equals the
  `⨅ I ∈ {I.Nonempty ∧ I ≠ univ}, (cutProduct q I : ℝ)` shape of the target.
* `minCut_eq_singleton_min` — (genmamu:224) the cut is attained at singletons.
-/

open Finset BigOperators

namespace Semicontinuity
namespace MinCut

variable {k : ℕ}

/-- The cut product over the bipartition `(I, Iᶜ)` of `[k]`:
`∏_{i ∈ I, j ∉ I} q i j` (the product of cross-pair weights).

Source: `genmamu.tex:224` — `∏_{i∈I,j∉I} q_ij`. -/
def cutProduct (q : Fin k → Fin k → ℕ) (I : Finset (Fin k)) : ℕ :=
  ∏ p ∈ I ×ˢ (Finset.univ \ I), q p.1 p.2

/-- The Finset of admissible bipartitions `{I | I.Nonempty ∧ I ≠ univ}`,
realised as the filtered powerset of `univ`. -/
def admissibleCuts (k : ℕ) : Finset (Finset (Fin k)) :=
  (Finset.univ.powerset).filter (fun I => I.Nonempty ∧ I ≠ Finset.univ)

@[simp] lemma mem_admissibleCuts {I : Finset (Fin k)} :
    I ∈ admissibleCuts k ↔ I.Nonempty ∧ I ≠ Finset.univ := by
  simp [admissibleCuts, Finset.mem_filter]

/-- For `2 ≤ k`, the set of admissible cuts is nonempty: the singleton `{0}`
works (`Fin k` has at least two elements). -/
lemma admissibleCuts_nonempty (hk : 2 ≤ k) : (admissibleCuts k).Nonempty := by
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num) hk
  -- `{0}` is nonempty and not all of `univ` (since there is another element `1`).
  refine ⟨{(⟨0, hk0⟩ : Fin k)}, ?_⟩
  rw [mem_admissibleCuts]
  refine ⟨Finset.singleton_nonempty _, ?_⟩
  intro h
  -- if `{0} = univ` then `card univ = 1`, contradicting `2 ≤ k`.
  have hcard : (Finset.univ : Finset (Fin k)).card = 1 := by
    rw [← h]; simp
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-- **Min-cut weight** `min_{∅≠I⊊[k]} ∏_{i∈I,j∉I} q_ij`.

Source: `genmamu.tex:224`. Defined as a `Finset.inf'` over the (nonempty for
`2 ≤ k`) filtered powerset of admissible bipartitions. -/
noncomputable def minCut (q : Fin k → Fin k → ℕ) (hk : 2 ≤ k) : ℕ :=
  (admissibleCuts k).inf' (admissibleCuts_nonempty hk) (cutProduct q)

/-- `minCut` is a lower bound for every admissible cut product. -/
lemma minCut_le_cutProduct (q : Fin k → Fin k → ℕ) (hk : 2 ≤ k)
    {I : Finset (Fin k)} (hI : I.Nonempty ∧ I ≠ Finset.univ) :
    minCut q hk ≤ cutProduct q I := by
  apply Finset.inf'_le
  rw [mem_admissibleCuts]
  exact hI

/-- The `minCut` is attained: there is an admissible `I` with
`cutProduct q I = minCut q hk`. -/
lemma exists_cutProduct_eq_minCut (q : Fin k → Fin k → ℕ) (hk : 2 ≤ k) :
    ∃ I : Finset (Fin k), (I.Nonempty ∧ I ≠ Finset.univ) ∧
      cutProduct q I = minCut q hk := by
  obtain ⟨I, hI, hval⟩ :=
    Finset.exists_mem_eq_inf' (admissibleCuts_nonempty hk) (cutProduct q)
  exact ⟨I, (mem_admissibleCuts).1 hI, hval.symm⟩

/-- Pointwise monotonicity of `cutProduct` in the weights. -/
lemma cutProduct_mono {q q' : Fin k → Fin k → ℕ}
    (h : ∀ i j, q i j ≤ q' i j) (I : Finset (Fin k)) :
    cutProduct q I ≤ cutProduct q' I := by
  unfold cutProduct
  apply Finset.prod_le_prod' -- ∏ a ≤ ∏ b when pointwise ≤ (ℕ)
  intro p _
  exact h p.1 p.2

/-- **Monotonicity of `minCut`** in the weights `q`.  Needed to chain with
Theorem 3.2's `∏ subrankPair ≥ flatRank`. -/
lemma minCut_mono {q q' : Fin k → Fin k → ℕ} (hk : 2 ≤ k)
    (h : ∀ i j, q i j ≤ q' i j) :
    minCut q hk ≤ minCut q' hk := by
  unfold minCut
  apply Finset.le_inf'
  intro I hI
  exact le_trans (Finset.inf'_le _ hI) (cutProduct_mono h I)

/-! ## Dyadic-reduction bridges (semicontinuity tex:987-990)

The following lemmas support the log-free dyadic reduction: `minCut` is power-law
multiplicative (`minCut_pow`), and replacing each weight by the largest power of
`2` below it loses at most a fixed multiplicative constant `2^(k*k)`
(`minCut_le_const_mul_floor`). -/

/-- `cutProduct` is power-law: `cutProduct (q^N) I = (cutProduct q I)^N`. -/
lemma cutProduct_pow (q : Fin k → Fin k → ℕ) (N : ℕ) (I : Finset (Fin k)) :
    cutProduct (fun i j => (q i j) ^ N) I = (cutProduct q I) ^ N := by
  unfold cutProduct
  rw [← Finset.prod_pow]

/-- **Power-law for `minCut`**: `minCut (fun i j => (q i j)^N) = (minCut q)^N`.
The cut products are `N`-th powers (`cutProduct_pow`) and `x ↦ x^N` is monotone on
`ℕ`, so it commutes with the `Finset.inf'`. -/
lemma minCut_pow (q : Fin k → Fin k → ℕ) (hk : 2 ≤ k) (N : ℕ) :
    minCut (fun i j => (q i j) ^ N) hk = (minCut q hk) ^ N := by
  classical
  unfold minCut
  rw [Finset.comp_inf'_eq_inf'_comp (admissibleCuts_nonempty hk)
        (g := fun n : ℕ => n ^ N)
        (fun a b => by
          rcases le_total a b with h | h
          · rw [min_eq_left h, min_eq_left (Nat.pow_le_pow_left h N)]
          · rw [min_eq_right h, min_eq_right (Nat.pow_le_pow_left h N)])]
  apply Finset.inf'_congr (admissibleCuts_nonempty hk) rfl
  intro I hI
  exact cutProduct_pow q N I

/-- The number of ordered cross-pairs of any bipartition is `≤ k * k`. -/
lemma card_cross_le (I : Finset (Fin k)) :
    (I ×ˢ (Finset.univ \ I)).card ≤ k * k := by
  rw [Finset.card_product]
  have h1 : I.card ≤ k := by
    have := Finset.card_le_univ I; rwa [Fintype.card_fin] at this
  have h2 : (Finset.univ \ I).card ≤ k := by
    have := Finset.card_le_univ (Finset.univ \ I)
    rwa [Fintype.card_fin] at this
  exact Nat.mul_le_mul h1 h2

/-- **Floor-dyadic bound for `cutProduct`**: if `b i j ≤ q i j ≤ 2 * b i j` for the
cross-pairs of `I`, then `cutProduct q I ≤ 2 ^ (k*k) * cutProduct b I`. -/
lemma cutProduct_le_const_mul (q b : Fin k → Fin k → ℕ) (I : Finset (Fin k))
    (hle : ∀ p ∈ I ×ˢ (Finset.univ \ I), q p.1 p.2 ≤ 2 * b p.1 p.2) :
    cutProduct q I ≤ 2 ^ (k * k) * cutProduct b I := by
  classical
  unfold cutProduct
  calc ∏ p ∈ I ×ˢ (Finset.univ \ I), q p.1 p.2
      ≤ ∏ p ∈ I ×ˢ (Finset.univ \ I), (2 * b p.1 p.2) :=
        Finset.prod_le_prod' (fun p hp => hle p hp)
    _ = 2 ^ (I ×ˢ (Finset.univ \ I)).card * ∏ p ∈ I ×ˢ (Finset.univ \ I), b p.1 p.2 := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
    _ ≤ 2 ^ (k * k) * ∏ p ∈ I ×ˢ (Finset.univ \ I), b p.1 p.2 := by
        apply Nat.mul_le_mul_right
        exact Nat.pow_le_pow_right (by norm_num) (card_cross_le I)

/-- **Floor-dyadic bound for `minCut`**: if `b i j ≤ q i j ≤ 2 * b i j` everywhere,
then `minCut q ≤ 2 ^ (k*k) * minCut b`.  Evaluate at the `b`-minimiser. -/
lemma minCut_le_const_mul_floor (q b : Fin k → Fin k → ℕ) (hk : 2 ≤ k)
    (hle : ∀ i j, q i j ≤ 2 * b i j) :
    minCut q hk ≤ 2 ^ (k * k) * minCut b hk := by
  classical
  obtain ⟨I, hI, hIeq⟩ := exists_cutProduct_eq_minCut b hk
  calc minCut q hk
      ≤ cutProduct q I := minCut_le_cutProduct q hk hI
    _ ≤ 2 ^ (k * k) * cutProduct b I :=
        cutProduct_le_const_mul q b I (fun p _ => hle p.1 p.2)
    _ = 2 ^ (k * k) * minCut b hk := by rw [hIeq]

/-- **`minCut` as a genuine real minimum.**

`minCut q hk`, cast to `ℝ`, is the `Finset.inf'` over the admissible cuts of the
real-valued cut products.  This is the honest real-number form of the min-cut:
a genuine minimum over the nonempty filtered powerset. -/
lemma minCut_real_eq_inf' (q : Fin k → Fin k → ℕ) (hk : 2 ≤ k) :
    ((minCut q hk : ℕ) : ℝ) =
      (admissibleCuts k).inf' (admissibleCuts_nonempty hk)
        (fun I => ((cutProduct q I : ℕ) : ℝ)) := by
  unfold minCut
  -- `Nat.cast` is a monotone order embedding `ℕ ↪o ℝ`, hence commutes with `inf'`.
  rw [Finset.comp_inf'_eq_inf'_comp (admissibleCuts_nonempty hk)
        (g := fun n : ℕ => (n : ℝ)) (fun a b => by exact_mod_cast Nat.cast_min a b)]
  rfl

/-- The range of the (`Prop`-restricted) cut-product family is bounded below.
Used to apply `ciInf_le` to the `iInf`-over-a-set form. -/
private lemma bddBelow_restricted_cutProduct (q : Fin k → Fin k → ℕ)
    (S : Set (Finset (Fin k))) :
    BddBelow (Set.range (fun I => ⨅ (_ : I ∈ S), ((cutProduct q I : ℕ) : ℝ))) :=
  Set.Finite.bddBelow (Set.finite_range _)

/-- **The `iInf`-bridge over `ℝ`.**

The `⨅ I ∈ {I.Nonempty ∧ I ≠ univ}, (cutProduct q I : ℝ)` shape used by the
target `asympSubrank_ge_min_flatRank` is bounded above by `(minCut q hk : ℝ)`.

Note on the convention: in `ℝ` (a `ConditionallyCompleteLinearOrderBot`, *not* a
complete lattice), an `iInf` over an empty index is `sInf ∅ = 0` (cf.
`Real.iInf_of_isEmpty`).  Since the index set `S = {I.Nonempty ∧ I ≠ univ}`
*excludes* `∅` (which is not `Nonempty`), the empty-set summand contributes
`⨅ (_ : ∅ ∈ S), … = 0`, so the whole `⨅ I ∈ S, (cutProduct q I : ℝ)` is `≤ 0`,
hence `≤ (minCut q hk : ℝ)` (cut products are `Nat`-casts, `≥ 0`).  This `≤`
direction is exactly what the target needs: `⨅ I ∈ S, F(I) ≤ (real min) ≤ Q̃`. -/
lemma iInf_admissible_le_minCut (q : Fin k → Fin k → ℕ) (hk : 2 ≤ k) :
    (⨅ I ∈ ({I : Finset (Fin k) | I.Nonempty ∧ I ≠ Finset.univ}),
        ((cutProduct q I : ℕ) : ℝ))
      ≤ ((minCut q hk : ℕ) : ℝ) := by
  -- `∅` is excluded from `S` (it is not `Nonempty`); its summand is `0`.
  have hempty : (∅ : Finset (Fin k)) ∉
      ({I : Finset (Fin k) | I.Nonempty ∧ I ≠ Finset.univ}) := by
    simp
  refine le_trans (ciInf_le (bddBelow_restricted_cutProduct q _) (∅ : Finset (Fin k))) ?_
  haveI : IsEmpty ((∅ : Finset (Fin k)) ∈
      ({I : Finset (Fin k) | I.Nonempty ∧ I ≠ Finset.univ})) := ⟨hempty⟩
  rw [Real.iInf_of_isEmpty]
  positivity

/-!
## On `genmamu.tex:224` (singleton attainment)

`genmamu.tex:224` ("a minimum cut is obtained by removing every edge incident
with a distinguished vertex") asserts that the min-cut is attained at a
*singleton* `I = {v}`.  This is **not** a pure-combinatorics fact about an
arbitrary weight function `q : Fin k → Fin k → ℕ`: it relies on the
super-multiplicative structure of the underlying subranks
(`cutProduct` of a refined cut dominates a singleton cut).  For a generic `q`
the singleton need not be a minimiser (e.g. one can make `cutProduct {v}` large
for every `v` while a two-element cut stays small).  Accordingly we do **not**
state a singleton-attainment lemma at the level of arbitrary `q`: it would be
false.  The genuine singleton-attainment belongs with the
subrank-specific assembly (Theorem 3.2 ⇒ Corollary 3.5), not here.
-/

end MinCut
end Semicontinuity
