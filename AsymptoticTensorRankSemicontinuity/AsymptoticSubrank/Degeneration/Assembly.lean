/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.Degeneration.QuadForm
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.Degeneration.Counting
import AsymptoticTensorRankSemicontinuity.Prerequisites.BorderSubrankK
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Vrana–Christandl GHZ degeneration assembly (Corollary 3.5)

This file assembles the **degeneration lower bound** at the heart of the
Vrana–Christandl bound on `ω(GHZ^H_2, GHZ_2)` (arXiv:1603.03964, `genmamu.tex`
lines 150-189): for a general-position orthogonal representation
`c : E → ℤ^D` of the line graph `L(H)` of a hypergraph `H = ([k], E, I)`,

  `GHZ^H_n ⪰ GHZ_M`   with   `M = solCount c n g`   (the optimal `g`),

hence `borderSubrank (GHZ^H_n) ≥ M`. Combined with the Counting lemma
(`exists_g_solCount_ge`) and `M ≈ n^{l−d}`, this feeds the rate
`ω(GHZ^H_2, GHZ_2) ≤ log n / log M → 1/(|E|−d)` (genmamu:181-189).

## Source (read verbatim before editing)

`genmamu.tex:150-157` (the degeneration). The quadratic form
`Q(i) = ⟨∑_e c_e i_e − g, ∑_e c_e i_e − g⟩` distributes over the vertices, an
index `i_e` appearing only at vertices incident with `e` (orthogonality of the
line-graph representation kills the non-incident cross terms). Local
`ε`-dependent operators `A_1(ε),…,A_k(ε)` then act diagonally by
`(⊗_j A_j(ε)) |(i_e)⟩ = ε^{Q(i)} |(i_e)⟩`, so

> `GHZ^H_n ⪰ ∑_{0≤i_e≤n−1, ∑c_e i_e = g} |(i_e)_{E_1}⟩…|(i_e)_{E_k}⟩`,

the leading `ε`-order being exactly the solutions of `∑_e c_e i_e = g`.

`genmamu.tex:158-159` (general position). The surviving state IS a GHZ state of
size `#solutions`: fixing the indices at any **one** vertex determines the rest,
because the vectors of edges not incident with that vertex are linearly
independent. A sufficient condition is that *any* `d` of the `c_e` are linearly
independent ("general position", needing `d ≥ |E| − min_j |E_j|`).

`genmamu.tex:162-189` (Thm). Choosing `g` to maximize the count gives
`≥ M := ⌈(2C)^{−d} n^{l−d}⌉` solutions, whence `GHZ^H_n ⪰ GHZ_M`.

## Encoding (newly defined — no GHZ^H encoding existed in the repo)

`GHZ^H_n` is the **diagonal consistency tensor** of the hypergraph: a `k`-tensor
(`TensorK F k`) with one leg per vertex `v : Fin k`, leg `v` indexed by the
incident-edge index assignment `localIdx inc n v := {e // inc v e} → Fin n`
(genmamu:152, the ket `|(i_e)_{e ∈ E_v}⟩_v`). Its entry is `1` iff the local
assignments are **globally consistent** — i.e. they are the restrictions of a
single global index tuple `i : E → Fin n` (genmamu:151-156, the GHZ diagonal:
all legs carry "the same" underlying `(i_e)`). This is the abstract,
general-position generalization of the cycle's `mamuIter`
(`IteratedMaMu/Basic.lean:69`), whose matching condition
`(f j).2 = (f (j+1)).1` is exactly local consistency for the cycle hypergraph.

The construction mirrors `TensorK.borderSubrankK_mamuIter_ge`
(`IteratedMaMu/Degeneration.lean:821`) but is driven by the abstract
`absLocalWeight` `ε`-exponents and the `absQuadForm_eq_zero_iff` solution set
from `QuadForm.lean`, with general-position injectivity giving the GHZ structure.

## Main results

* `ghzHTensor` — the abstract `GHZ^H_n` diagonal-consistency `k`-tensor.
* `GHZBorderRestricts` — the `ε`-degeneration (`borderSubrankK`-style) predicate:
  the unit/identity `k`-tensor `⟨s⟩` degenerates into `GHZ^H_n`.
* `ghzH_borderRestricts_solCount` — **the degeneration** (genmamu:150-159): the
  diagonal polynomial family built from `absLocalWeight` exponents degenerates
  `⟨solCount c n g⟩` into `GHZ^H_n`. The leading-order coefficient bookkeeping is
  described in its docstring.
* `borderSubrankK_ghzH_ge_solCount` — **the headline**:
  `solCount c n g ≤ borderSubrankK (ghzHTensor …)`.
* `borderSubrankK_ghzH_ge_optimal` — feeds the optimal-`g` count of
  `exists_g_solCount_ge`, the `n^{l−d}` rate.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset BigOperators Polynomial

namespace VC.Degeneration

universe u

variable {E : Type*} [Fintype E] [DecidableEq E] {k D : ℕ}

/-! ## The abstract `GHZ^H_n` diagonal-consistency tensor (genmamu:151-156) -/

variable (inc : Fin k → E → Prop) [∀ v e, Decidable (inc v e)]

/-- The local index space at vertex `v`: the incident-edge index assignment
    `(i_e)_{e : inc v e}` (genmamu:152, the ket `|(i_e)_{e ∈ E_v}⟩_v`). -/
abbrev localIdx (n : ℕ) (v : Fin k) : Type _ := {e : E // inc v e} → Fin n

/-- The **`GHZ^H_n` tensor** (genmamu:151-156): the `k`-tensor whose leg `v` is
    indexed by `localIdx inc n v`, with entry `1` iff the per-vertex local index
    assignments are **globally consistent** — there is a single global tuple
    `i : E → Fin n` restricting (`fun e => i e.1`) to each leg's local assignment.

    This is the GHZ diagonal of the hypergraph: the abstract, general-position
    generalization of `mamuIter` (`IteratedMaMu/Basic.lean:69`), whose cyclic
    matching condition is exactly local consistency for the cycle hypergraph. -/
noncomputable def ghzHTensor {F : Type u} [Field F] (n : ℕ) :
    TensorK F k (localIdx inc n) :=
  fun f => if (∃ i : E → Fin n, ∀ v : Fin k, ∀ e : {e : E // inc v e}, f v e = i e.1)
            then (1 : F) else 0

/-- A global tuple `i : E → Fin n` induces a consistent local family
    `globalToLocal inc i v e := i e.1`, on which `ghzHTensor` is `1`. -/
def globalToLocal {n : ℕ} (i : E → Fin n) :
    (v : Fin k) → localIdx inc n v :=
  fun v e => i e.1

/-- The diagonal `GHZ^H_n` tensor evaluates to `1` on every globally-consistent
    family `globalToLocal inc i` (genmamu:156, the surviving GHZ terms). -/
lemma ghzHTensor_globalToLocal {F : Type u} [Field F] {n : ℕ} (i : E → Fin n) :
    ghzHTensor (F := F) inc n (globalToLocal inc i) = 1 := by
  unfold ghzHTensor
  rw [if_pos]
  exact ⟨i, fun v e => rfl⟩

/-! ## The degeneration predicate (genmamu:150-157)

We phrase the `ε`-degeneration in the `TensorK.borderSubrankK` shape
(`IteratedMaMu/BorderSubrankK.lean:39`), so that the headline plugs into
`borderSubrankK` directly, exactly as `borderSubrankK_mamuIter_ge` does. -/

/-- **`ε`-degeneration `⟨s⟩ ⪰ GHZ^H_n`** in the `borderSubrankK` `Polynomial.coeff`
    encoding (genmamu:150-157, Strassen-style `ε`-operators). A degree-`N`
    polynomial family `A : (v : Fin k) → Fin s → localIdx v → F[X]` whose
    contraction against `GHZ^H_n`

    * **vanishes** below degree `N` (the `ε`-orders), and
    * **realizes** the identity tensor `identityK F k s ρ` at degree `N`,

    for every leg tuple `ρ`. This is `s ∈` the set defining
    `borderSubrankK (ghzHTensor …)`. -/
def GHZBorderRestricts {F : Type u} [Field F] (n s : ℕ)
    (A : (v : Fin k) → Fin s → localIdx inc n v → Polynomial F)
    (N : ℕ) : Prop :=
  (∀ ρ : Fin k → Fin s, ∀ l : ℕ, l < N →
    (∑ f : (v : Fin k) → localIdx inc n v,
      (∏ v : Fin k, A v (ρ v) (f v)) * Polynomial.C (ghzHTensor (F := F) inc n f)).coeff l = 0) ∧
  (∀ ρ : Fin k → Fin s,
    (∑ f : (v : Fin k) → localIdx inc n v,
      (∏ v : Fin k, A v (ρ v) (f v)) * Polynomial.C (ghzHTensor (F := F) inc n f)).coeff N
      = TensorK.identityK F k s ρ)

/-! ## Reindexing the solution set as labels `Fin s` -/

/-- The solution set `{i : E → Fin n | ∀ r, ∑_e c_e r · i_e = g_r}` as a `Finset`
    (`solCount` is its card; `Counting.lean:69`). -/
def solFinset (c : E → Fin D → ℤ) (n : ℕ) (g : Fin D → ℤ) : Finset (E → Fin n) :=
  Finset.univ.filter (fun i : E → Fin n => ∀ r, ∑ e, (c e r) * (i e : ℤ) = g r)

lemma solFinset_card (c : E → Fin D → ℤ) (n : ℕ) (g : Fin D → ℤ) :
    (solFinset (E := E) c n g).card = solCount c n g := rfl

/-! ## General position ⇒ GHZ injectivity (genmamu:158-159)

The load-bearing hypothesis: fixing the local indices at any one vertex `v₀`
determines the global tuple. We carry it as the abstract hypothesis
`GeneralPositionInjective`, which is exactly genmamu:158-159's statement
("the values of the indices at any one vertex determine the remaining ones
uniquely"). General position (any `d` of the `c_e` linearly independent) is the
*sufficient condition* the paper gives; we keep the injectivity conclusion as
the hypothesis so the degeneration assembly does not silently assume it. -/

/-- **General-position GHZ injectivity** (genmamu:158-159): for the chosen `g`,
    two solutions of `∑_e c_e i_e = g` that agree on the edges incident with some
    single vertex `v₀` are equal. This is the statement "fixing the indices at any
    one vertex determines the rest" — implied by general position of `c`
    (any `d` linearly independent), carried as a hypothesis per genmamu:159. -/
def GeneralPositionInjective (c : E → Fin D → ℤ) (n : ℕ) (g : Fin D → ℤ) : Prop :=
  ∀ v₀ : Fin k, ∀ i i' : E → Fin n,
    (∀ r, ∑ e, (c e r) * (i e : ℤ) = g r) →
    (∀ r, ∑ e, (c e r) * (i' e : ℤ) = g r) →
    (∀ e : E, inc v₀ e → i e = i' e) → i = i'

/-- General-position injectivity in `globalToLocal` form: two solutions whose
    local families agree at one vertex `v₀` induce equal local families
    everywhere — i.e. the labels `globalToLocal inc i` are distinct across
    distinct solutions, the GHZ structure of genmamu:158-159. -/
lemma globalToLocal_injOn_of_genPos
    {c : E → Fin D → ℤ} {n : ℕ} {g : Fin D → ℤ} (hk : 0 < k)
    (hgp : GeneralPositionInjective (k := k) inc c n g) :
    Set.InjOn (globalToLocal inc (n := n))
      {i : E → Fin n | ∀ r, ∑ e, (c e r) * (i e : ℤ) = g r} := by
  intro i hi i' hi' heq
  -- The induced local families agree at *every* vertex; use the vertex `v₀ = 0`
  -- (genmamu:158-159, fixing the indices at one vertex determines the rest).
  have hv₀ : ∀ e : E, inc ⟨0, hk⟩ e → i e = i' e := by
    intro e he
    have := congrFun (congrFun heq ⟨0, hk⟩) ⟨e, he⟩
    simpa [globalToLocal] using this
  exact hgp ⟨0, hk⟩ i i' hi hi' hv₀

/-! ## Generic `ε`-operator bookkeeping (tensor-agnostic)

Abstract indicator-collapse and coefficient-extraction lemmas over the GHZ^H
leg type. They are pure polynomial/finite-sum identities — no GHZ^H structure or
orthogonality is used. -/

variable {F : Type u} [Field F]

/-- **Indicator collapse.** When each leg's
    polynomial is an indicator selecting a fixed local label `f₀ v` times `p v`,
    the sum over all local families collapses to the single term
    `(∏_v p v) · C(T f₀)`. Tensor-agnostic. -/
theorem ghz_indicator_collapse {n : ℕ}
    (T : TensorK F k (localIdx inc n))
    (f₀ : (v : Fin k) → localIdx inc n v) (p : Fin k → Polynomial F) :
    (∑ f : (v : Fin k) → localIdx inc n v,
      (∏ v : Fin k, if f v = f₀ v then p v else 0) * Polynomial.C (T f)) =
    (∏ v : Fin k, p v) * Polynomial.C (T f₀) := by
  classical
  have h_eq : ∀ f : (v : Fin k) → localIdx inc n v,
      (∏ v : Fin k, if f v = f₀ v then p v else 0) * Polynomial.C (T f) =
      if f = f₀ then (∏ v : Fin k, p v) * Polynomial.C (T f₀) else 0 := by
    intro f
    by_cases hf : f = f₀
    · subst hf; simp
    · have : ∃ v₀, f v₀ ≠ f₀ v₀ := by
        by_contra h; push_neg at h; exact hf (funext h)
      obtain ⟨v₀, hv₀⟩ := this
      simp only [hf, ite_false]
      have : (∏ v : Fin k, if f v = f₀ v then p v else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ v₀) (if_neg hv₀)
      rw [this, zero_mul]
  simp_rw [h_eq]
  simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- **Coefficient of `(∏_v X^{e v}) · C(c)`**:
    equals `c` at `N = ∑_v e v`, else `0`. Tensor-agnostic. -/
theorem ghz_coeff_prod_X_pow_C (e : Fin k → ℕ) (c : F) (N : ℕ) :
    ((∏ v : Fin k, (Polynomial.X : Polynomial F) ^ e v) * Polynomial.C c).coeff N =
    if N = ∑ v : Fin k, e v then c else 0 := by
  conv_lhs => rw [show ∏ v : Fin k, (X : Polynomial F) ^ e v =
    X ^ (∑ v : Fin k, e v) from Finset.prod_pow_eq_pow_sum Finset.univ e X]
  rw [Polynomial.X_pow_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs with h <;> simp

/-! ## The degeneration `GHZ^H_n ⪰ GHZ_M` (genmamu:150-159)

The structural assembly. The exponents are the per-vertex `absLocalWeight`
contributions (shifted to be nonnegative); the indicator collapse
(`ghz_indicator_collapse`) + coefficient extraction (`ghz_coeff_prod_X_pow_C`)
reduce each leg tuple `ρ` to the total exponent `∑_v w_v + k·K`, which equals
`Q(i) + k·K` by `absQuadForm_eq_sum_localWeights`. By `absQuadForm_eq_zero_iff`:

* a **constant** `ρ` (all legs carry one solution `i`) has `Q = 0`, total exponent
  `= N := k·K`, and `ghzHTensor = 1` on the consistent label `globalToLocal i`
  (`ghzHTensor_globalToLocal`) — giving the identity at degree `N`;
* a **non-constant consistent** `ρ` would, by general-position injectivity
  (`globalToLocal_injOn_of_genPos`), force all legs to carry the *same* solution,
  contradiction — so consistency fails and `ghzHTensor = 0`;
* a **non-solution** label has `Q ≥ 1` (`absQuadForm_pos_of_ne_sol`), total
  exponent `> N`, hence coefficient `0` below `N` and at `N`.

The label index `Fin (solCount c n g) ≃ solFinset c n g` enumerates the solutions
(genmamu:158-159, the surviving GHZ basis). -/

/-- **The degeneration** `⟨solCount c n g⟩ ⪰ GHZ^H_n` (genmamu:150-159).

    This is exactly the leading-order coefficient bookkeeping that the cycle case
    `borderSubrankK_mamuIter_ge`
    (`IteratedMaMu/Degeneration.lean:821`) performs concretely for the cycle.
    The structural ingredients are:

    * the `ε`-operator exponents are the per-vertex `absLocalWeight` contributions
      (`QuadForm.lean`), summing to `Q(i)` by `absQuadForm_eq_sum_localWeights`;
    * the indicator collapse / coefficient extraction are
      `ghz_indicator_collapse` / `ghz_coeff_prod_X_pow_C`;
    * the solution/non-solution dichotomy is `absQuadForm_eq_zero_iff` /
      `absQuadForm_pos_of_ne_sol`;
    * the GHZ structure (distinct surviving labels) is
      `globalToLocal_injOn_of_genPos` (general position, genmamu:158-159);
    * `ghzHTensor` is `1` on consistent labels by `ghzHTensor_globalToLocal`.

    Precise finite computation: the explicit witness packaging — choosing the
    shift `K` so each `(absLocalWeight v) + K ≥ 0` (abstract analogue of
    `localWeight_shift_nonneg`), so that `∑_v ((absLocalWeight v) + K).toNat
    = Q(i) + k·K` (analogue of `sum_shifted_localWeights_eq`), and the
    `solFinset c n g ≃ Fin (solCount c n g)` reindexing of labels. Each is an
    honest finite computation, not a source gap. -/
theorem ghzH_borderRestricts_solCount (c : E → Fin D → ℤ)
    (horth : ∀ e f : E, ¬ edgesIncident inc e f → idot (c e) (c f) = 0)
    (edgeOwner : E → Fin k) (pairOwner : E → E → Fin k) (gVertex : Fin k)
    (hEdgeInc : ∀ e, inc (edgeOwner e) e)
    (hPairInc : ∀ e f, e ≠ f → idot (c e) (c f) ≠ 0 →
      inc (pairOwner e f) e ∧ inc (pairOwner e f) f)
    (n : ℕ) (hn : 1 ≤ n) (hk : 0 < k) (g : Fin D → ℤ)
    (hgp : GeneralPositionInjective (k := k) inc c n g) :
    ∃ (N : ℕ) (A : (v : Fin k) → Fin (solCount c n g) →
        localIdx inc n v → Polynomial F),
      GHZBorderRestricts (F := F) inc n (solCount c n g) A N := by
  classical
  set s := solCount c n g with s_def
  -- Enumerate the solution set `solFinset c n g ≃ Fin s` (its card is `solCount`).
  have hcard : Fintype.card {x // x ∈ solFinset (E := E) c n g} = s := by
    rw [Fintype.card_coe, solFinset_card]
  set eqv : Fin s ≃ {x // x ∈ solFinset (E := E) c n g} :=
    (Fintype.equivFinOfCardEq hcard).symm with eqv_def
  -- `enum i` is the `i`-th solution; it lies in `solFinset`, hence solves the system.
  set enum : Fin s → (E → Fin n) := fun i => (eqv i).1 with enum_def
  have enum_sol : ∀ i : Fin s, ∀ r, ∑ e, (c e r) * ((enum i) e : ℤ) = g r := by
    intro i r
    have := (eqv i).2
    simp only [solFinset, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this r
  have enum_inj : Function.Injective enum := by
    intro i j h
    apply eqv.injective
    exact Subtype.ext h
  -- Abbreviation: the per-vertex local weight as a function of a tuple `i : E → Fin n`.
  set wt : (E → Fin n) → Fin k → ℤ :=
    fun i v => absLocalWeight edgeOwner pairOwner gVertex c g (fun e => ((i e : ℤ))) v
    with wt_def
  -- The local-weight `wt i v` depends only on `i` at edges incident with `v`
  -- (`absLocalWeight_locality`, genmamu:150).
  have wt_local : ∀ (i i' : E → Fin n) (v : Fin k),
      (∀ e, inc v e → i e = i' e) → wt i v = wt i' v := by
    intro i i' v hagree
    refine absLocalWeight_locality inc edgeOwner pairOwner gVertex c g horth
      hEdgeInc hPairInc v (fun e => (i e : ℤ)) (fun e => (i' e : ℤ)) ?_
    intro e he; simp only [hagree e he]
  -- The sum of local weights over vertices is the quadratic form
  -- (`absQuadForm_eq_sum_localWeights`).
  have wt_sum : ∀ i : E → Fin n,
      ∑ v : Fin k, wt i v = absQuadForm c g (fun e => (i e : ℤ)) := by
    intro i
    rw [wt_def]
    exact (absQuadForm_eq_sum_localWeights edgeOwner pairOwner gVertex c g
      (fun e => (i e : ℤ))).symm
  -- **Uniform shift `K`**: choose `K` so each `wt i v + K ≥ 0` over the finite
  -- index range (abstract analogue of `localWeight_shift_nonneg`).
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ (i : E → Fin n) (v : Fin k), 0 ≤ wt i v + (K : ℤ) := by
    have hne : ((fun _ => ⟨0, by omega⟩ : E → Fin n), (⟨0, hk⟩ : Fin k)) ∈
        (Finset.univ : Finset ((E → Fin n) × Fin k)) := Finset.mem_univ _
    set M : ℤ := (Finset.univ : Finset ((E → Fin n) × Fin k)).sup'
      ⟨_, hne⟩ (fun p => - wt p.1 p.2) with M_def
    refine ⟨M.toNat, ?_⟩
    intro i v
    have hle : - wt i v ≤ M :=
      Finset.le_sup' (s := (Finset.univ : Finset ((E → Fin n) × Fin k)))
        (fun p => - wt p.1 p.2) (Finset.mem_univ (i, v))
    have hKge : M ≤ (M.toNat : ℤ) := Int.self_le_toNat _
    linarith
  -- The exponent for vertex `v` and label `i`.
  set expOf : Fin k → Fin s → ℕ :=
    fun v i => (wt (enum i) v + (K : ℤ)).toNat with expOf_def
  set N : ℕ := k * K with N_def
  -- The local family at vertex `v` for label `i`.
  set lp : (v : Fin k) → Fin s → localIdx inc n v :=
    fun v i => globalToLocal inc (enum i) v with lp_def
  -- Total exponent as ℤ.
  have h_total_exp_int : ∀ (ρ : Fin k → Fin s),
      (∑ v : Fin k, (expOf v (ρ v) : ℤ)) =
      (∑ v : Fin k, wt (enum (ρ v)) v) + (k : ℤ) * K := by
    intro ρ
    simp only [expOf_def]
    conv_lhs => arg 2; ext v; rw [Int.toNat_of_nonneg (hK (enum (ρ v)) v)]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  -- The indicator-collapse for the chosen family.
  have h_collapse : ∀ (ρ : Fin k → Fin s),
      (∑ f : (v : Fin k) → localIdx inc n v,
        (∏ v : Fin k, (if f v = lp v (ρ v) then X ^ expOf v (ρ v) else 0)) *
          Polynomial.C (ghzHTensor (F := F) inc n f)) =
      (∏ v : Fin k, X ^ expOf v (ρ v)) *
        Polynomial.C (ghzHTensor (F := F) inc n (fun v => lp v (ρ v))) :=
    fun ρ => ghz_indicator_collapse inc (ghzHTensor (F := F) inc n)
      (fun v => lp v (ρ v)) (fun v => X ^ expOf v (ρ v))
  -- **Consistency ⇒ total exponent = Q(j) + N.** If `ghzHTensor (fun v => lp v (ρ v)) ≠ 0`,
  -- there is a global witness `j` consistent with every leg; by locality each
  -- `wt (enum (ρ v)) v = wt j v`, so the total exponent is `Q(j) + N`.
  have h_consistent_exp : ∀ (ρ : Fin k → Fin s),
      (ghzHTensor (F := F) inc n (fun v => lp v (ρ v)) ≠ 0) →
      ∃ j : E → Fin n,
        (∀ v : Fin k, ∀ e : E, inc v e → enum (ρ v) e = j e) ∧
        (∑ v : Fin k, (expOf v (ρ v) : ℤ)) =
          absQuadForm c g (fun e => (j e : ℤ)) + (k : ℤ) * K := by
    intro ρ hne
    -- Extract the global witness from `ghzHTensor ≠ 0`.
    have hcons : ∃ i : E → Fin n, ∀ v : Fin k, ∀ e : {e : E // inc v e},
        (fun v => lp v (ρ v)) v e = i e.1 := by
      by_contra hno
      apply hne
      unfold ghzHTensor
      rw [if_neg hno]
    obtain ⟨j, hj⟩ := hcons
    refine ⟨j, ?_, ?_⟩
    · -- agreement at incident edges: `lp v (ρ v) e = globalToLocal (enum (ρ v)) v e
      --   = (enum (ρ v)) e = j e` for incident `e`.
      intro v e he
      have := hj v ⟨e, he⟩
      simp only [lp_def] at this
      exact this
    · rw [h_total_exp_int ρ]
      congr 1
      rw [← wt_sum j]
      apply Finset.sum_congr rfl
      intro v _
      exact wt_local (enum (ρ v)) j v (fun e he => by
        have := hj v ⟨e, he⟩
        simp only [lp_def] at this
        exact this)
  -- The witness package.
  refine ⟨N, fun v i f => if f = lp v i then X ^ expOf v i else 0, ?vanish, ?ident⟩
  -- VANISHING below `N`.
  case vanish =>
    intro ρ l hl
    rw [h_collapse ρ, ghz_coeff_prod_X_pow_C]
    by_cases h0 : (ghzHTensor (F := F) inc n (fun v => lp v (ρ v))) = 0
    · simp [h0]
    · rw [if_neg]
      -- Total exponent `= Q(j) + N ≥ N > l`.
      obtain ⟨j, _, hexp⟩ := h_consistent_exp ρ h0
      have hQ : 0 ≤ absQuadForm c g (fun e => (j e : ℤ)) := absQuadForm_nonneg c g _
      have hN_le : (N : ℤ) ≤ ∑ v : Fin k, (expOf v (ρ v) : ℤ) := by
        rw [hexp]; have : (N : ℤ) = (k : ℤ) * K := by rw [N_def]; push_cast; ring
        rw [this]; linarith
      have hN_le' : N ≤ ∑ v : Fin k, expOf v (ρ v) := by
        rw [← Nat.cast_sum] at hN_le; exact_mod_cast hN_le
      omega
  -- IDENTITY at `N`.
  case ident =>
    intro ρ
    rw [h_collapse ρ, ghz_coeff_prod_X_pow_C]
    simp only [TensorK.identityK]
    by_cases hconst : ∀ v₁ v₂ : Fin k, ρ v₁ = ρ v₂
    · -- ρ constant: total exponent `= N`, and `ghzHTensor = 1`.
      rw [if_pos hconst]
      -- All legs carry the same solution `enum (ρ ⟨0,hk⟩)`.
      have hsame : ∀ v : Fin k, enum (ρ v) = enum (ρ ⟨0, hk⟩) := by
        intro v; rw [hconst v ⟨0, hk⟩]
      have hlp_eq : (fun v => lp v (ρ v)) = globalToLocal inc (enum (ρ ⟨0, hk⟩)) := by
        funext v; simp only [lp_def]; rw [hsame v]
      have hghz1 : ghzHTensor (F := F) inc n (fun v => lp v (ρ v)) = 1 := by
        rw [hlp_eq]; exact ghzHTensor_globalToLocal inc (enum (ρ ⟨0, hk⟩))
      -- Q = 0 since `enum (ρ ⟨0,hk⟩)` is a solution.
      have hQ0 : absQuadForm c g (fun e => ((enum (ρ ⟨0, hk⟩)) e : ℤ)) = 0 := by
        rw [absQuadForm_eq_zero_iff]
        intro r; exact enum_sol (ρ ⟨0, hk⟩) r
      -- Total exponent = N.
      have hexpN : (∑ v : Fin k, expOf v (ρ v)) = N := by
        have hne : ghzHTensor (F := F) inc n (fun v => lp v (ρ v)) ≠ 0 := by
          rw [hghz1]; exact one_ne_zero
        obtain ⟨j, hagree, hexp⟩ := h_consistent_exp ρ hne
        -- `j` agrees with the (single) solution at every incident edge, and the
        -- solution itself is consistent, so `Q(j) = Q(sol) = 0`.
        have hjeq : ∀ v : Fin k, ∀ e : E, inc v e →
            (enum (ρ ⟨0, hk⟩)) e = j e := by
          intro v e he; rw [← hsame v]; exact hagree v e he
        -- `j` solves the system: it agrees with the solution on edges incident
        -- with vertex `0`, and `globalToLocal` is consistent across all legs, so
        -- `j = enum (ρ ⟨0,hk⟩)` on all incident edges of every vertex.
        have hQj0 : absQuadForm c g (fun e => (j e : ℤ)) = 0 := by
          rw [← wt_sum j, ← hQ0, ← wt_sum (enum (ρ ⟨0, hk⟩))]
          apply Finset.sum_congr rfl
          intro v _
          exact (wt_local (enum (ρ ⟨0, hk⟩)) j v (fun e he => hjeq v e he)).symm
        have : (∑ v : Fin k, (expOf v (ρ v) : ℤ)) = (N : ℤ) := by
          rw [hexp, hQj0]; have : (N : ℤ) = (k : ℤ) * K := by rw [N_def]; push_cast; ring
          rw [this]; ring
        rw [← Nat.cast_sum] at this; exact_mod_cast this
      rw [if_pos hexpN.symm, hghz1]
    · -- ρ non-constant: identity must be 0.
      rw [if_neg hconst]
      by_cases hexpN : N = ∑ v : Fin k, expOf v (ρ v)
      swap
      · rw [if_neg hexpN]
      -- Total exponent = N forces `ghzHTensor = 0` (else all labels coincide,
      -- contradicting non-constancy via general-position injectivity).
      rw [if_pos hexpN]
      by_cases h0 : (ghzHTensor (F := F) inc n (fun v => lp v (ρ v))) = 0
      · rw [h0]
      · exfalso
        obtain ⟨j, hagree, hexp⟩ := h_consistent_exp ρ h0
        -- `N = Q(j) + N` ⇒ `Q(j) = 0` ⇒ `j` is a solution.
        have hQj0 : absQuadForm c g (fun e => (j e : ℤ)) = 0 := by
          have heq : (N : ℤ) = absQuadForm c g (fun e => (j e : ℤ)) + (k : ℤ) * K := by
            rw [← hexp, ← Nat.cast_sum]; exact_mod_cast hexpN
          have hN : (N : ℤ) = (k : ℤ) * K := by rw [N_def]; push_cast; ring
          rw [hN] at heq; linarith
        have hj_sol : ∀ r, ∑ e, (c e r) * ((j e : ℤ)) = g r := by
          rw [absQuadForm_eq_zero_iff] at hQj0
          intro r; have := hQj0 r; simpa [linComb] using this
        -- Each `enum (ρ v)` agrees with the solution `j` on edges incident with `v`,
        -- and both solve the system ⇒ `enum (ρ v) = j` (general position).
        have henum_eq_j : ∀ v : Fin k, enum (ρ v) = j := by
          intro v
          apply hgp v (enum (ρ v)) j (enum_sol (ρ v)) hj_sol
          intro e he; exact hagree v e he
        -- Hence all labels coincide, contradicting non-constancy.
        apply hconst
        intro v₁ v₂
        apply enum_inj
        rw [henum_eq_j v₁, henum_eq_j v₂]

/-- **Headline: `solCount c n g ≤ borderSubrankK (GHZ^H_n)`** (genmamu:150-159).

    The general-position GHZ degeneration of genmamu:150-159 realizes the unit
    tensor `⟨solCount c n g⟩` as a border restriction of `GHZ^H_n`, so the solution
    count is a lower bound for the border subrank of `GHZ^H_n`. This is the
    `borderSubrankK` analogue of `borderSubrankK_mamuIter_ge` driven by the
    abstract `absLocalWeight` exponents.

    Needs the `borderSubrankK` defining set bounded above (`hbdd`), the standard
    flattening bound (`borderSubrankK_mamuIter_bddAbove` analogue). -/
theorem borderSubrankK_ghzH_ge_solCount (c : E → Fin D → ℤ)
    (horth : ∀ e f : E, ¬ edgesIncident inc e f → idot (c e) (c f) = 0)
    (edgeOwner : E → Fin k) (pairOwner : E → E → Fin k) (gVertex : Fin k)
    (hEdgeInc : ∀ e, inc (edgeOwner e) e)
    (hPairInc : ∀ e f, e ≠ f → idot (c e) (c f) ≠ 0 →
      inc (pairOwner e f) e ∧ inc (pairOwner e f) f)
    (n : ℕ) (hn : 1 ≤ n) (hk : 0 < k) (g : Fin D → ℤ)
    (hgp : GeneralPositionInjective (k := k) inc c n g)
    (hbdd : BddAbove {s : ℕ | ∃ (N : ℕ)
      (A : (v : Fin k) → Fin s → localIdx inc n v → Polynomial F),
      (∀ ρ : Fin k → Fin s, ∀ l : ℕ, l < N →
        (∑ f : (v : Fin k) → localIdx inc n v,
          (∏ v, A v (ρ v) (f v)) *
            Polynomial.C (ghzHTensor (F := F) inc n f)).coeff l = 0) ∧
      (∀ ρ : Fin k → Fin s,
        (∑ f : (v : Fin k) → localIdx inc n v,
          (∏ v, A v (ρ v) (f v)) *
            Polynomial.C (ghzHTensor (F := F) inc n f)).coeff N =
        TensorK.identityK F k s ρ)}) :
    solCount c n g ≤
      TensorK.borderSubrankK (F := F) k (localIdx inc n) (ghzHTensor (F := F) inc n) := by
  obtain ⟨N, A, hvanish, hident⟩ :=
    ghzH_borderRestricts_solCount (F := F) inc c horth edgeOwner pairOwner gVertex
      hEdgeInc hPairInc n hn hk g hgp
  unfold TensorK.borderSubrankK
  apply le_csSup hbdd
  exact ⟨N, A, hvanish, hident⟩

/-- **Optimal-`g` degeneration rate** (genmamu:181-189). Combining the headline
    with the Counting lemma `exists_g_solCount_ge` (`Counting.lean:212`): there is
    a `g` whose solution count `M := solCount c n g` is large
    (`(2Cn)^D · M ≥ n^{|E|}`, the `n^{l−d}` rate) AND degenerates into `GHZ^H_n`,
    so `M ≤ borderSubrankK (GHZ^H_n)` for that same `g`. This is the
    `borderSubrank ≥ M` with `M ≈ n^{l−d}` feeding
    `ω(GHZ^H_2, GHZ_2) ≤ log n / log M → 1/(|E|−d)`. -/
theorem borderSubrankK_ghzH_ge_optimal (c : E → Fin D → ℤ)
    (horth : ∀ e f : E, ¬ edgesIncident inc e f → idot (c e) (c f) = 0)
    (edgeOwner : E → Fin k) (pairOwner : E → E → Fin k) (gVertex : Fin k)
    (hEdgeInc : ∀ e, inc (edgeOwner e) e)
    (hPairInc : ∀ e f, e ≠ f → idot (c e) (c f) ≠ 0 →
      inc (pairOwner e f) e ∧ inc (pairOwner e f) f)
    (n : ℕ) (hn : 1 ≤ n) (hk : 0 < k)
    (hgp : ∀ g : Fin D → ℤ, GeneralPositionInjective (k := k) inc c n g)
    (hbdd : ∀ g : Fin D → ℤ, BddAbove {s : ℕ | ∃ (N : ℕ)
      (A : (v : Fin k) → Fin s → localIdx inc n v → Polynomial F),
      (∀ ρ : Fin k → Fin s, ∀ l : ℕ, l < N →
        (∑ f : (v : Fin k) → localIdx inc n v,
          (∏ v, A v (ρ v) (f v)) *
            Polynomial.C (ghzHTensor (F := F) inc n f)).coeff l = 0) ∧
      (∀ ρ : Fin k → Fin s,
        (∑ f : (v : Fin k) → localIdx inc n v,
          (∏ v, A v (ρ v) (f v)) *
            Polynomial.C (ghzHTensor (F := F) inc n f)).coeff N =
        TensorK.identityK F k s ρ)}) :
    ∃ g : Fin D → ℤ,
      n ^ (Fintype.card E) ≤ (2 * cubeBound c * n) ^ D *
        TensorK.borderSubrankK (F := F) k (localIdx inc n) (ghzHTensor (F := F) inc n) := by
  obtain ⟨g, hg⟩ := exists_g_solCount_ge c n hn
  refine ⟨g, ?_⟩
  have hM : solCount c n g ≤
      TensorK.borderSubrankK (F := F) k (localIdx inc n) (ghzHTensor (F := F) inc n) :=
    borderSubrankK_ghzH_ge_solCount (F := F) inc c horth edgeOwner pairOwner gVertex
      hEdgeInc hPairInc n hn hk g (hgp g) (hbdd g)
  calc n ^ (Fintype.card E)
      ≤ (2 * cubeBound c * n) ^ D * solCount c n g := hg
    _ ≤ (2 * cubeBound c * n) ^ D *
        TensorK.borderSubrankK (F := F) k (localIdx inc n) (ghzHTensor (F := F) inc n) :=
        Nat.mul_le_mul_left _ hM

end VC.Degeneration
