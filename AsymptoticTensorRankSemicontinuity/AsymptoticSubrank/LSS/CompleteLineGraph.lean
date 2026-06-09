/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.LSS.Existence

/-!
# The line graph of `K_k` = Johnson graph `J(k,2)`, and its rational GOR

This file builds the graph-theoretic input for **Corollary 3.5**: a general-position
orthogonal representation of the line graph `L(K_k)` of the complete graph `K_k`.

## Source (verbatim)

Vrana–Christandl, arXiv:1603.03964,
`references/vrana-christandl-1603.03964-genmamu.tex` (tex:159-199):

* tex:172 — "the dimension `d` must be at least `|E| - min_j |E_j|`"; for `H = K_k`
  (`|E| = C(k,2)`, every vertex has degree `k-1`, so `min_j |E_j| = k-1`) this is
  `d = C(k,2) - (k-1) = C(k-1,2) = (k-1)(k-2)/2`.
* tex:191 — "Since `H` is `λ(H)`-edge-connected, its line graph is `λ(H)`-vertex-connected.
  A result by Lovász, Saks and Schrijver states that any `(n-d)`-vertex-connected graph with
  `n` vertices admits a general-position orthogonal representation in `ℝ^d`."  For `K_k`,
  `λ(K_k) = k-1`, so `L(K_k)` is `(k-1)`-vertex-connected and `n - d = C(k,2) - C(k-1,2) = k-1`.

## The graph

Vertices of `L(K_k)` are the `2`-subsets `{a,b} ⊆ Fin k`, of which there are
`n = C(k,2) = k(k-1)/2`.  Two `2`-subsets are adjacent in the line graph iff they SHARE a
vertex (intersect) and are distinct.  We index the vertex set as `Fin (k*(k-1)/2)` via the
noncomputable equivalence `pairEquiv k` onto the subtype `{s : Finset (Fin k) // s.card = 2}`.

## Main declarations

* `lineCompleteGraph k : SimpleGraph (Fin (k*(k-1)/2))` — the line graph `L(K_k)`.
* `lineCompleteGraph_card_nonNeighbors` — the `hcard` predecessor bound:
  `(precNonNbrσ … v).card ≤ (k-1)*(k-2)/2 - 1`, a pure counting statement.
* `lineCompleteGraph_connectivity` — `(k-1)`-vertex-connectivity (the genuine graph theory,
  via the explicit Menger "`k-1` disjoint paths" argument in `reachableWithin_of_disjoint`).
* `exists_rat_gor_lineCompleteGraph` — instantiates `LSS.exists_rat_gor`, producing a rational
  general-position orthogonal representation of `L(K_k)` in `ℝ^{(k-1)(k-2)/2}`.

`lineCompleteGraph_connectivity` is the explicit "`k-1` internally vertex-disjoint
paths, one survives" specialization of Menger's theorem to the Johnson graph
`J(k,2)` (genmamu tex:191 / Lovász–Saks–Schrijver).
-/

open SimpleGraph

namespace LSS

/-! ### `Nat`-arithmetic helpers (triangular numbers via `Nat.choose 2`) -/

/-- `(m+2)*(m+1)/2 = C(m+2, 2)` — the triangular-number / binomial identity, in the
subtraction-free shifted form so `rfl` closes the `m+2-1 = m+1` reduction. -/
theorem tri_eq_choose (m : ℕ) : (m + 2) * (m + 1) / 2 = (m + 2).choose 2 := by
  rw [Nat.choose_two_right]; rfl

/-- Pascal's rule for the triangular numbers: `C(m+2,2) = (m+1) + C(m+1,2)`. -/
theorem choose_two_succ (m : ℕ) : (m + 2).choose 2 = (m + 1) + (m + 1).choose 2 := by
  rw [show m + 2 = (m + 1) + 1 from rfl, Nat.choose_succ_succ (m + 1) 1, Nat.choose_one_right]

/-! ### The pair-vertex indexing -/

/-- The number of `2`-subsets of `Fin k` is `C(k,2) = k(k-1)/2`. -/
theorem card_pairSubtype (k : ℕ) :
    Fintype.card {s : Finset (Fin k) // s.card = 2} = k * (k - 1) / 2 := by
  rw [Fintype.card_finset_len, Fintype.card_fin, Nat.choose_two_right]

/-- The chosen bijection from the index type `Fin (k*(k-1)/2)` onto the `2`-subsets of
`Fin k`.  Noncomputable (`Fintype.equivFinOfCardEq`), used purely to transport the line-graph
adjacency. -/
noncomputable def pairEquiv (k : ℕ) :
    Fin (k * (k - 1) / 2) ≃ {s : Finset (Fin k) // s.card = 2} :=
  (Fintype.equivFinOfCardEq (card_pairSubtype k)).symm

/-- The `2`-subset `{a,b} ⊆ Fin k` indexed by `i : Fin (k*(k-1)/2)`. -/
noncomputable def pairOf (k : ℕ) (i : Fin (k * (k - 1) / 2)) : Finset (Fin k) :=
  (pairEquiv k i).1

theorem pairOf_card (k : ℕ) (i : Fin (k * (k - 1) / 2)) : (pairOf k i).card = 2 :=
  (pairEquiv k i).2

/-- The indexing is injective on the underlying `2`-subset: distinct indices give distinct
pairs. -/
theorem pairOf_injective (k : ℕ) {i j : Fin (k * (k - 1) / 2)} (h : pairOf k i = pairOf k j) :
    i = j := by
  have : pairEquiv k i = pairEquiv k j := Subtype.ext h
  exact (pairEquiv k).injective this

/-! ### The line graph `L(K_k)` -/

/-- **`L(K_k)` = Johnson graph `J(k,2)`** (genmamu tex:159-172).  Vertices are the `2`-subsets
of `Fin k` (indexed by `Fin (k*(k-1)/2)`); two distinct vertices are adjacent iff their pairs
intersect (share a vertex of `K_k` — i.e. the two edges of `K_k` are incident). -/
noncomputable def lineCompleteGraph (k : ℕ) : SimpleGraph (Fin (k * (k - 1) / 2)) where
  Adj i j := i ≠ j ∧ ¬ Disjoint (pairOf k i) (pairOf k j)
  symm := by
    rintro i j ⟨hne, hd⟩
    exact ⟨hne.symm, fun h => hd h.symm⟩
  loopless := by rintro i ⟨hne, _⟩; exact hne rfl

noncomputable instance (k : ℕ) : DecidableRel (lineCompleteGraph k).Adj :=
  fun _ _ => Classical.dec _

@[simp] theorem lineCompleteGraph_adj (k : ℕ) (i j : Fin (k * (k - 1) / 2)) :
    (lineCompleteGraph k).Adj i j ↔ i ≠ j ∧ ¬ Disjoint (pairOf k i) (pairOf k j) :=
  Iff.rfl

/-! ### Item 2: the predecessor bound `hcard` -/

/-- The `2`-subsets disjoint from the pair of `v` (the genuine non-neighbours of `v`, other
than `v` itself).  Every preceding non-neighbour of `v` lies here. -/
noncomputable def disjointPairs (k : ℕ) (v : Fin (k * (k - 1) / 2)) :
    Finset (Fin (k * (k - 1) / 2)) :=
  Finset.univ.filter (fun u => u ≠ v ∧ Disjoint (pairOf k u) (pairOf k v))

theorem precNonNbrσ_subset_disjointPairs (k : ℕ) (σ : Equiv.Perm (Fin (k * (k - 1) / 2)))
    (v : Fin (k * (k - 1) / 2)) :
    precNonNbrσ (lineCompleteGraph k) σ v ⊆ disjointPairs k v := by
  intro u hu
  rw [mem_precNonNbrσ] at hu
  obtain ⟨hlt, hnadj⟩ := hu
  -- `u ≠ v` since their `σ`-positions differ.
  have hne : u ≠ v := by
    intro h; subst h; exact lt_irrefl _ hlt
  -- `¬ Adj v u` with `v ≠ u` forces the pairs disjoint.
  simp only [lineCompleteGraph_adj, not_and, not_not] at hnadj
  have hdisj : Disjoint (pairOf k v) (pairOf k u) := hnadj (fun h => hne h.symm)
  rw [disjointPairs, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hne, hdisj.symm⟩

/-- The map sending a disjoint-pair index `u` to its `2`-subset, landing in the `2`-subsets of
the `(k-2)`-element complement `Fin k \ pairOf k v`. -/
theorem card_disjointPairs_le (k : ℕ) (v : Fin (k * (k - 1) / 2)) :
    (disjointPairs k v).card ≤ (k - 2).choose 2 := by
  classical
  -- Inject `disjointPairs k v` into the `2`-subsets of the complement of `pairOf k v`.
  have hcompl : (Finset.univ \ pairOf k v).card = k - 2 := by
    rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ, pairOf_card]
  calc (disjointPairs k v).card
      ≤ ((Finset.univ \ pairOf k v).powersetCard 2).card := by
        apply Finset.card_le_card_of_injOn (fun u => pairOf k u)
        · intro u hu
          rw [Finset.mem_coe, disjointPairs, Finset.mem_filter] at hu
          obtain ⟨_, _, hdisj⟩ := hu
          rw [Finset.mem_coe, Finset.mem_powersetCard]
          refine ⟨?_, pairOf_card k u⟩
          intro x hx
          rw [Finset.mem_sdiff]
          refine ⟨Finset.mem_univ _, ?_⟩
          intro hxv
          exact (Finset.disjoint_left.mp hdisj) hx hxv
        · intro a _ b _ hab
          exact pairOf_injective k hab
    _ = (k - 2).choose 2 := by
        rw [Finset.card_powersetCard, hcompl]

/-- **Item 2 — the predecessor bound (`hcard`).** For every ordering `σ` and vertex `v`, the
preceding non-neighbours of `v` number at most `e = (k-1)*(k-2)/2 - 1`.

Argument (genmamu tex:172): `precNonNbrσ … v ⊆ disjointPairs k v` (preceding non-neighbours are
disjoint pairs), and `|disjointPairs k v| ≤ C(k-2,2) = (k-2)(k-3)/2 ≤ (k-1)(k-2)/2 - 1 = e`
for `k ≥ 2`. -/
theorem lineCompleteGraph_card_nonNeighbors (k : ℕ)
    (σ : Equiv.Perm (Fin (k * (k - 1) / 2))) (v : Fin (k * (k - 1) / 2)) :
    (precNonNbrσ (lineCompleteGraph k) σ v).card ≤ (k - 1) * (k - 2) / 2 - 1 := by
  refine le_trans (Finset.card_le_card (precNonNbrσ_subset_disjointPairs k σ v)) ?_
  refine le_trans (card_disjointPairs_le k v) ?_
  -- `(k-2).choose 2 ≤ (k-1).choose 2 - 1`, via Pascal's rule
  -- `(k-1).choose 2 = (k-2) + (k-2).choose 2 ≥ (k-2).choose 2 + 1` for `k ≥ 3`.
  rcases Nat.lt_or_ge k 3 with hk | hk
  · interval_cases k <;> decide
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    change (m + 1).choose 2 ≤ (m + 2) * (m + 1) / 2 - 1
    rw [tri_eq_choose, choose_two_succ]
    omega

/-! ### Item 3: connectivity — supporting infrastructure -/

/-- The index of the `2`-subset `{a,b}` (for `a ≠ b`). -/
noncomputable def idxOf (k : ℕ) {a b : Fin k} (hab : a ≠ b) :
    Fin (k * (k - 1) / 2) :=
  (pairEquiv k).symm ⟨{a, b}, Finset.card_pair hab⟩

@[simp] theorem pairOf_idxOf (k : ℕ) {a b : Fin k} (hab : a ≠ b) :
    pairOf k (idxOf k hab) = {a, b} := by
  simp only [idxOf, pairOf, Equiv.apply_symm_apply]

theorem mem_left_idxOf (k : ℕ) {a b : Fin k} (hab : a ≠ b) :
    a ∈ pairOf k (idxOf k hab) := by rw [pairOf_idxOf]; exact Finset.mem_insert_self _ _

theorem mem_right_idxOf (k : ℕ) {a b : Fin k} (hab : a ≠ b) :
    b ∈ pairOf k (idxOf k hab) := by
  rw [pairOf_idxOf]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- `idxOf` is symmetric in its two arguments (same `2`-subset). -/
theorem idxOf_comm (k : ℕ) {a b : Fin k} (hab : a ≠ b) :
    idxOf k hab = idxOf k (Ne.symm hab) := by
  apply pairOf_injective; rw [pairOf_idxOf, pairOf_idxOf, Finset.pair_comm]

/-- `idxOf {a,b} = idxOf {c,d}` forces the pair `{a,b} = {c,d}`. -/
theorem idxOf_eq_iff (k : ℕ) {a b c d : Fin k} (hab : a ≠ b) (hcd : c ≠ d) :
    idxOf k hab = idxOf k hcd ↔ ({a, b} : Finset (Fin k)) = {c, d} := by
  constructor
  · intro h; have := congrArg (pairOf k) h; rwa [pairOf_idxOf, pairOf_idxOf] at this
  · intro h; apply pairOf_injective; rw [pairOf_idxOf, pairOf_idxOf, h]

/-- Two `2`-subsets that share an element are adjacent (when distinct). -/
theorem adj_of_inter {k : ℕ} {i j : Fin (k * (k - 1) / 2)} (hij : i ≠ j)
    {x : Fin k} (hi : x ∈ pairOf k i) (hj : x ∈ pairOf k j) :
    (lineCompleteGraph k).Adj i j := by
  refine ⟨hij, ?_⟩
  rw [Finset.not_disjoint_iff]
  exact ⟨x, hi, hj⟩

/-- A single induced edge gives `ReachableWithin`. -/
theorem reachableWithin_of_adj {k : ℕ} {T : Set (Fin (k * (k - 1) / 2))}
    {x y : Fin (k * (k - 1) / 2)} (hx : x ∈ T) (hy : y ∈ T)
    (h : (lineCompleteGraph k).Adj x y) :
    ReachableWithin (lineCompleteGraph k) T x y := by
  refine ⟨hx, hy, ?_⟩
  apply SimpleGraph.Adj.reachable
  rw [SimpleGraph.induce_adj]
  exact h

/-- `ReachableWithin` is reflexive (within a set containing the point). -/
theorem reachableWithin_refl {k : ℕ} {T : Set (Fin (k * (k - 1) / 2))}
    {x : Fin (k * (k - 1) / 2)} (hx : x ∈ T) :
    ReachableWithin (lineCompleteGraph k) T x x :=
  ⟨hx, hx, SimpleGraph.Reachable.refl _⟩

/-- `ReachableWithin` is transitive. -/
theorem reachableWithin_trans {k : ℕ} {T : Set (Fin (k * (k - 1) / 2))}
    {x y z : Fin (k * (k - 1) / 2)}
    (h₁ : ReachableWithin (lineCompleteGraph k) T x y)
    (h₂ : ReachableWithin (lineCompleteGraph k) T y z) :
    ReachableWithin (lineCompleteGraph k) T x z := by
  obtain ⟨hx, hy, r₁⟩ := h₁
  obtain ⟨hy', hz, r₂⟩ := h₂
  refine ⟨hx, hz, ?_⟩
  have : (⟨y, hy⟩ : {w // w ∈ T}) = ⟨y, hy'⟩ := rfl
  exact r₁.trans (this ▸ r₂)

/-- Extract the two elements of a `2`-subset. -/
theorem pairOf_eq_pair {k : ℕ} (i : Fin (k * (k - 1) / 2)) :
    ∃ a b : Fin k, a ≠ b ∧ pairOf k i = {a, b} := by
  have hc := pairOf_card k i
  rw [Finset.card_eq_two] at hc
  obtain ⟨a, b, hab, h⟩ := hc
  exact ⟨a, b, hab, h⟩

/-- **Core disjoint-pairs reachability** (genmamu tex:191).

For the line graph `L(K_k) = J(k,2)`: if `u = {a,b}` and `v = {c,d}` are two vertices whose
pairs are *disjoint* (`a,b,c,d` all distinct, so `k ≥ 4`), and `S` is a deleted set with
`|S| < k - 1`, then `u` and `v` remain reachable in `L(K_k) ∖ S`.

This is the only nontrivial case of `(k-1)`-vertex-connectivity (the `u = v` and
pair-intersecting cases are immediate).  The argument is the explicit "`k-1` internally
vertex-disjoint paths, one survives" form of Menger's theorem specialized to `J(k,2)`.

Concretely, index a family of `k - 1` routes by the elements `e ∈ Fin k` with `e ≠ a`:
* `e = b`: the corner route `u — {b,c} — v` (internal vertex `{b,c}`);
* `e = c`: the corner route `u — {a,c} — v` (internal vertex `{a,c}`);
* `e = d`: the corner route `u — {a,d} — v` (internal vertex `{a,d}`);
* `e ∉ {a,b,c,d}`: the length-3 route `u — {a,e} — {e,c} — v` (internal vertices
  `{a,e}, {e,c}`).
Every internal vertex of route `e` is a pair containing `e`, and one checks the internal
vertex sets are pairwise disjoint.  There are `k - 1` such routes, so a deletion set of size
`< k - 1` cannot meet all of them; any unmet route is a walk in `L(K_k) ∖ S`. -/
theorem reachableWithin_of_disjoint (k : ℕ) (_hk : 3 ≤ k)
    (S : Finset (Fin (k * (k - 1) / 2))) (hS : S.card < k - 1)
    {u v : Fin (k * (k - 1) / 2)} (hu : u ∉ S) (hv : v ∉ S) (_huv : u ≠ v)
    (hdisj : Disjoint (pairOf k u) (pairOf k v)) :
    ReachableWithin (lineCompleteGraph k) (↑S)ᶜ u v := by
  classical
  -- Extract the two elements of each pair.
  obtain ⟨a, b, hab, hpu⟩ := pairOf_eq_pair u
  obtain ⟨c, d, hcd, hpv⟩ := pairOf_eq_pair v
  -- Disjointness of the pairs gives all four elements distinct.
  rw [hpu, hpv, Finset.disjoint_left] at hdisj
  have hac : a ≠ c := fun h => hdisj (Finset.mem_insert_self _ _)
    (h ▸ Finset.mem_insert_self _ _)
  have had : a ≠ d := fun h => hdisj (Finset.mem_insert_self _ _)
    (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hbc : b ≠ c := fun h => hdisj (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    (h ▸ Finset.mem_insert_self _ _)
  have hbd : b ≠ d := fun h => hdisj (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  -- `u`, `v` membership facts via their pairs.
  have hau : a ∈ pairOf k u := hpu ▸ Finset.mem_insert_self _ _
  have hbu : b ∈ pairOf k u := hpu ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hcv : c ∈ pairOf k v := hpv ▸ Finset.mem_insert_self _ _
  have hdv : d ∈ pairOf k v := hpv ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  -- The internal-vertex Finset of route `e` (for `e ≠ a`).
  set f : Fin k → Finset (Fin (k * (k - 1) / 2)) := fun e =>
    (if h : e = a ∨ e = b then (∅ : Finset _)
      else {idxOf k (a := a) (b := e) (fun heq => h (Or.inl heq.symm))})
    ∪ (if h : e = c ∨ e = d then (∅ : Finset _)
      else {idxOf k (a := e) (b := c) (fun heq => h (Or.inl heq))}) with hf
  -- Every member of `f e` is a pair containing `e`.
  have hmem_e : ∀ e (w : Fin (k * (k - 1) / 2)), w ∈ f e → e ∈ pairOf k w := by
    intro e w hw
    simp only [hf, Finset.mem_union] at hw
    rcases hw with hw | hw
    · split_ifs at hw with hcond
      · exact absurd hw (Finset.notMem_empty _)
      · rw [Finset.mem_singleton] at hw; subst hw
        exact mem_right_idxOf k _
    · split_ifs at hw with hcond
      · exact absurd hw (Finset.notMem_empty _)
      · rw [Finset.mem_singleton] at hw; subst hw
        exact mem_left_idxOf k _
  -- Every member of `f e` has pair `{a,e}` or `{e,c}`.
  have hpair_f : ∀ e (w : Fin (k * (k - 1) / 2)), w ∈ f e →
      pairOf k w = ({a, e} : Finset (Fin k)) ∨ pairOf k w = ({e, c} : Finset (Fin k)) := by
    intro e w hw
    simp only [hf, Finset.mem_union] at hw
    rcases hw with hw | hw
    · split_ifs at hw with hcond
      · exact absurd hw (Finset.notMem_empty _)
      · rw [Finset.mem_singleton] at hw; subst hw
        left; rw [pairOf_idxOf]
    · split_ifs at hw with hcond
      · exact absurd hw (Finset.notMem_empty _)
      · rw [Finset.mem_singleton] at hw; subst hw
        right; rw [pairOf_idxOf]
  -- The internal-vertex sets are pairwise disjoint (over indices `≠ a`):
  -- a common member forces `e = e'`.
  have hinj : ∀ e e' (w : Fin (k * (k - 1) / 2)), e ≠ a → e' ≠ a →
      w ∈ f e → w ∈ f e' → e = e' := by
    intro e e' w hea hea' hwe hwe'
    have h1 := hpair_f e w hwe
    have h2 := hpair_f e' w hwe'
    -- The pair of `w` has card 2, so its two listed elements are distinct.
    have hcard2 : (pairOf k w).card = 2 := pairOf_card k w
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · -- both `{a,e} = {a,e'}`
      have : ({a, e} : Finset (Fin k)) = {a, e'} := by rw [← h1, h2]
      have he : e ∈ ({a, e'} : Finset (Fin k)) := this ▸ Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _)
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with he | he
      · exact absurd he hea
      · exact he
    · -- `{a,e} = {e',c}`: forces `a = e'`, contradicting `e' ≠ a`.
      have : ({a, e} : Finset (Fin k)) = {e', c} := by rw [← h1, h2]
      have ha : a ∈ ({e', c} : Finset (Fin k)) := this ▸ Finset.mem_insert_self _ _
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with ha | ha
      · exact absurd ha.symm hea'
      · exact absurd ha hac
    · -- `{e,c} = {a,e'}`: forces `a = e`, contradicting `e ≠ a`.
      have : ({e, c} : Finset (Fin k)) = {a, e'} := by rw [← h1, h2]
      have ha : a ∈ ({e, c} : Finset (Fin k)) := this ▸ Finset.mem_insert_self _ _
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with ha | ha
      · exact absurd ha.symm hea
      · exact absurd ha hac
    · -- both `{e,c} = {e',c}`
      have heq : ({e, c} : Finset (Fin k)) = {e', c} := by rw [← h1, h2]
      have he : e ∈ ({e', c} : Finset (Fin k)) := heq ▸ Finset.mem_insert_self _ _
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with he | he
      · exact he
      · -- `e = c` would make `{e,c}` a singleton, contradicting card 2.
        exfalso
        rw [h1, he] at hcard2
        simp at hcard2
  -- The index set `A = {e : Fin k | e ≠ a}`, of cardinality `k - 1`.
  set A : Finset (Fin k) := Finset.univ.filter (fun e => e ≠ a) with hA
  have hcardA : A.card = k - 1 := by
    rw [hA, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
  -- Pigeonhole: some route `e ∈ A` is untouched by `S`.
  have hexists : ∃ e ∈ A, Disjoint (f e) S := by
    by_contra hcon
    push_neg at hcon
    -- Every route in `A` meets `S`; choose (for ALL `e`) a witness vertex.
    have hwit : ∀ e, ∃ w, e ∈ A → (w ∈ f e ∧ w ∈ S) := by
      intro e
      by_cases he : e ∈ A
      · have := hcon e he
        rw [Finset.not_disjoint_iff] at this
        obtain ⟨w, hw1, hw2⟩ := this
        exact ⟨w, fun _ => ⟨hw1, hw2⟩⟩
      · exact ⟨u, fun h => absurd h he⟩
    choose g hg using hwit
    -- `g` maps `A` into `S` injectively, so `|A| ≤ |S|`.
    have hcardle : A.card ≤ S.card := by
      apply Finset.card_le_card_of_injOn g
      · intro e he; exact (hg e he).2
      · intro e he e' he' heq
        rw [Finset.mem_coe, hA, Finset.mem_filter] at he he'
        exact hinj e e' (g e) he.2 he'.2 (hg e (by rw [hA, Finset.mem_filter]; exact he)).1
          (heq ▸ (hg e' (by rw [hA, Finset.mem_filter]; exact he')).1)
    rw [hcardA] at hcardle
    omega
  obtain ⟨e, heA, hdisjfe⟩ := hexists
  have hea : e ≠ a := by rw [hA, Finset.mem_filter] at heA; exact heA.2
  -- The surviving vertex set `T = Sᶜ`.
  set T : Set (Fin (k * (k - 1) / 2)) := (↑S)ᶜ with hT
  have huT : u ∈ T := by simp [hT, hu]
  have hvT : v ∈ T := by simp [hT, hv]
  -- Any internal vertex of the surviving route lies in `T`.
  have hfT : ∀ w ∈ f e, w ∈ T := by
    intro w hw
    have : w ∉ S := fun hwS => (Finset.disjoint_left.mp hdisjfe) hw hwS
    simp [hT, this]
  -- Membership of the "first" internal vertex `{a,e}` in `f e` (when `e ∉ {a,b}`).
  have hfirst : ∀ (hne : e ≠ b) (hide : a ≠ e), idxOf k hide ∈ f e := by
    intro hne hide
    simp only [hf, Finset.mem_union]
    left
    rw [dif_neg (show ¬(e = a ∨ e = b) from by push_neg; exact ⟨hea, hne⟩)]
    rw [Finset.mem_singleton]
  -- Membership of the "second" internal vertex `{e,c}` in `f e` (when `e ∉ {c,d}`).
  have hsecond : ∀ (hnc : e ≠ c) (hnd : e ≠ d) (hide : e ≠ c), idxOf k hide ∈ f e := by
    intro hnc hnd hide
    simp only [hf, Finset.mem_union]
    right
    rw [dif_neg (show ¬(e = c ∨ e = d) from by push_neg; exact ⟨hnc, hnd⟩)]
    rw [Finset.mem_singleton]
  -- Reachability `u — w — v` for a single internal vertex `w` meeting `u` (at `p`) and
  -- `v` (at `q`), with `w ∈ T` and `pairOf w ≠ pairOf u`, `pairOf w ≠ pairOf v`.
  have hbridge : ∀ (w : Fin (k * (k - 1) / 2)), w ∈ T →
      pairOf k w ≠ pairOf k u → pairOf k w ≠ pairOf k v →
      (∃ p, p ∈ pairOf k u ∧ p ∈ pairOf k w) →
      (∃ q, q ∈ pairOf k v ∧ q ∈ pairOf k w) →
      ReachableWithin (lineCompleteGraph k) T u v := by
    intro w hwT hwu hwv ⟨p, hpu, hpw⟩ ⟨q, hqv, hqw⟩
    refine reachableWithin_trans (reachableWithin_of_adj huT hwT ?_)
      (reachableWithin_of_adj hwT hvT ?_)
    · exact adj_of_inter (fun h => hwu (congrArg (pairOf k) h.symm)) hpu hpw
    · exact adj_of_inter (fun h => hwv (congrArg (pairOf k) h)) hqw hqv
  -- A pair containing an element absent from another set is unequal to it.
  have pair_ne : ∀ {s t : Finset (Fin k)} {x : Fin k}, x ∈ s → x ∉ t → s ≠ t := by
    intro s t x hxs hxt h; exact hxt (h ▸ hxs)
  -- Build the walk by cases on `e`.
  by_cases heb : e = b
  · -- Corner route `u — {b,c} — v` (internal `{e,c} = {b,c}`).
    subst heb
    have hw : idxOf k hbc ∈ f e := hsecond hbc hbd hbc
    have hwpair : pairOf k (idxOf k hbc) = ({e, c} : Finset (Fin k)) := pairOf_idxOf k hbc
    refine hbridge _ (hfT _ hw) ?_ ?_ ⟨e, hbu, ?_⟩ ⟨c, hcv, ?_⟩
    · -- `{e,c} ≠ {a,e}`: `c ∈ {e,c}` but `c ∉ {a,e}`.
      rw [hwpair, hpu]
      exact pair_ne (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
            exact ⟨Ne.symm hac, Ne.symm hbc⟩)
    · -- `{e,c} ≠ {c,d}`: `e ∈ {e,c}` but `e ∉ {c,d}`.
      rw [hwpair, hpv]
      exact pair_ne (Finset.mem_insert_self _ _)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
            exact ⟨hbc, hbd⟩)
    · exact mem_left_idxOf k hbc
    · exact mem_right_idxOf k hbc
  · -- `e ≠ b`.  Split on `e = c`, `e = d`, else.
    by_cases hecc : e = c
    · -- Corner route `u — {a,c} — v` (internal `{a,e} = {a,c}`).
      subst hecc
      have hw : idxOf k (Ne.symm hea) ∈ f e := hfirst heb (Ne.symm hea)
      have hwpair : pairOf k (idxOf k (Ne.symm hea)) = ({a, e} : Finset (Fin k)) :=
        pairOf_idxOf k _
      refine hbridge _ (hfT _ hw) ?_ ?_ ⟨a, hau, ?_⟩ ⟨e, hcv, ?_⟩
      · -- `{a,e} ≠ {a,b}`: `e ∈ {a,e}` but `e ∉ {a,b}` (`e = c`, `c ≠ a`, `c ≠ b`).
        rw [hwpair, hpu]
        exact pair_ne (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
          (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
              exact ⟨hea, Ne.symm hbc⟩)
      · -- `{a,e} ≠ {c,d}`: `a ∈ {a,e}` but `a ∉ {c,d}`.
        rw [hwpair, hpv]
        exact pair_ne (Finset.mem_insert_self _ _)
          (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
              exact ⟨hac, had⟩)
      · exact mem_left_idxOf k _
      · exact mem_right_idxOf k _
    · by_cases hedd : e = d
      · -- Corner route `u — {a,d} — v` (internal `{a,e} = {a,d}`).
        subst hedd
        have hw : idxOf k (Ne.symm hea) ∈ f e := hfirst heb (Ne.symm hea)
        have hwpair : pairOf k (idxOf k (Ne.symm hea)) = ({a, e} : Finset (Fin k)) :=
          pairOf_idxOf k _
        refine hbridge _ (hfT _ hw) ?_ ?_ ⟨a, hau, ?_⟩ ⟨e, hdv, ?_⟩
        · -- `{a,e} ≠ {a,b}`: `e ∈ {a,e}` but `e ∉ {a,b}` (`e = d`).
          rw [hwpair, hpu]
          exact pair_ne (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
            (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                exact ⟨hea, Ne.symm hbd⟩)
        · -- `{a,e} ≠ {c,d}`: `a ∈ {a,e}` but `a ∉ {c,d}`.
          rw [hwpair, hpv]
          exact pair_ne (Finset.mem_insert_self _ _)
            (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                exact ⟨hac, had⟩)
        · exact mem_left_idxOf k _
        · exact mem_right_idxOf k _
      · -- Generic length-3 route `u — {a,e} — {e,c} — v` (`e ∉ {a,b,c,d}`).
        have hw1 : idxOf k (Ne.symm hea) ∈ f e := hfirst heb (Ne.symm hea)
        have hw2 : idxOf k hecc ∈ f e := hsecond hecc hedd hecc
        have hw1T : idxOf k (Ne.symm hea) ∈ T := hfT _ hw1
        have hw2T : idxOf k hecc ∈ T := hfT _ hw2
        have hp1 : pairOf k (idxOf k (Ne.symm hea)) = ({a, e} : Finset (Fin k)) :=
          pairOf_idxOf k _
        have hp2 : pairOf k (idxOf k hecc) = ({e, c} : Finset (Fin k)) := pairOf_idxOf k _
        -- `u — {a,e}` (share `a`), `{a,e} — {e,c}` (share `e`), `{e,c} — v` (share `c`).
        refine reachableWithin_trans (reachableWithin_of_adj huT hw1T ?_)
          (reachableWithin_trans (reachableWithin_of_adj hw1T hw2T ?_)
            (reachableWithin_of_adj hw2T hvT ?_))
        · -- `Adj u {a,e}` via shared `a`; distinct since `b ∈ {a,b}` but `b ∉ {a,e}`.
          refine adj_of_inter (fun h => ?_) hau (hp1 ▸ Finset.mem_insert_self _ _)
          have : pairOf k u ≠ pairOf k (idxOf k (Ne.symm hea)) := by
            rw [hpu, hp1]
            exact pair_ne (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
              (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                  exact ⟨Ne.symm hab, fun hbe => heb hbe.symm⟩)
          exact this (congrArg (pairOf k) h)
        · -- `Adj {a,e} {e,c}` via shared `e`; distinct since `a ∈ {a,e}` but `a ∉ {e,c}`.
          refine adj_of_inter (fun h => ?_)
            (hp1 ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
            (hp2 ▸ Finset.mem_insert_self _ _)
          have : pairOf k (idxOf k (Ne.symm hea)) ≠ pairOf k (idxOf k hecc) := by
            rw [hp1, hp2]
            exact pair_ne (Finset.mem_insert_self _ _)
              (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                  exact ⟨Ne.symm hea, hac⟩)
          exact this (congrArg (pairOf k) h)
        · -- `Adj {e,c} v` via shared `c`; distinct since `e ∈ {e,c}` but `e ∉ {c,d}`.
          refine adj_of_inter (fun h => ?_)
            (hp2 ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hcv
          have : pairOf k (idxOf k hecc) ≠ pairOf k v := by
            rw [hp2, hpv]
            exact pair_ne (Finset.mem_insert_self _ _)
              (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                  exact ⟨hecc, hedd⟩)
          exact this (congrArg (pairOf k) h)

/-! ### Item 3: connectivity -/

/-- **Item 3 — `(k-1)`-vertex-connectivity of `L(K_k)`** (genmamu tex:191, Lovász–Saks–Schrijver).

> "Since `H` is `λ(H)`-edge-connected, its line graph is `λ(H)`-vertex-connected."

`K_k` is `(k-1)`-edge-connected, so `L(K_k) = J(k,2)` is `(k-1)`-vertex-connected: after
deleting any set `S` of fewer than `k-1` pair-vertices, any two remaining pair-vertices
`{a,b}, {c,d}` stay reachable in the line graph.

The proof handles three cases.  The first conjunct `k-1 < C(k,2)` is Pascal arithmetic.  For
reachability: if `u = v` it is reflexivity; if the pairs of `u` and `v` *intersect* they are
directly adjacent; if the pairs are *disjoint* the work is in `reachableWithin_of_disjoint`,
the explicit "`k-1` internally vertex-disjoint paths, one survives" specialization of Menger's
theorem to `J(k,2)`. -/
theorem lineCompleteGraph_connectivity (k : ℕ) (hk : 3 ≤ k) :
    IsKVertexConnected (lineCompleteGraph k) (k - 1) := by
  classical
  constructor
  · -- First conjunct: `k - 1 < n = k*(k-1)/2`.
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    show m + 3 - 1 < (m + 3) * (m + 3 - 1) / 2
    have e1 : (m + 3) * (m + 3 - 1) / 2 = (m + 1 + 2) * (m + 1 + 1) / 2 := rfl
    rw [e1, tri_eq_choose (m + 1), choose_two_succ (m + 1)]
    have hpos : 1 ≤ (m + 1 + 1).choose 2 := Nat.choose_pos (by omega)
    omega
  · -- Reachability after deleting `S` with `|S| < k - 1`.
    intro S hS u v hu hv
    -- The complement set (vertices that survive the deletion).
    set T : Set (Fin (k * (k - 1) / 2)) := (↑S)ᶜ with hT
    have huT : u ∈ T := by simp [hT, hu]
    have hvT : v ∈ T := by simp [hT, hv]
    -- Case on whether `u = v`.
    by_cases huv : u = v
    · subst huv; exact reachableWithin_refl huT
    -- Case on whether the pairs intersect.
    by_cases hdisj : Disjoint (pairOf k u) (pairOf k v)
    · -- Disjoint pairs: choose an intermediate vertex outside `S`.
      exact reachableWithin_of_disjoint k hk S hS hu hv huv hdisj
    · -- Intersecting pairs: `u` and `v` are directly adjacent.
      exact reachableWithin_of_adj huT hvT ⟨huv, hdisj⟩

/-! ### The `Nat`-arithmetic bridge -/

/-- The dimension `D = (k-1)*(k-2)/2 = e+1`. -/
theorem dim_succ (k : ℕ) (hk : 3 ≤ k) :
    (k - 1) * (k - 2) / 2 - 1 + 1 = (k - 1) * (k - 2) / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  change (m + 2) * (m + 1) / 2 - 1 + 1 = (m + 2) * (m + 1) / 2
  rw [tri_eq_choose, choose_two_succ]
  omega

/-- `D = (k-1)*(k-2)/2 ≤ C(k,2) = k*(k-1)/2 = n`. -/
theorem dim_le_card (k : ℕ) :
    (k - 1) * (k - 2) / 2 ≤ k * (k - 1) / 2 := by
  have h : k - 2 = (k - 1) - 1 := by omega
  rw [h, ← Nat.choose_two_right, ← Nat.choose_two_right]
  exact Nat.choose_le_choose 2 (by omega)

/-- `n - D = k - 1`: `k*(k-1)/2 - (k-1)*(k-2)/2 = k-1`. -/
theorem card_sub_dim (k : ℕ) (hk : 3 ≤ k) :
    k * (k - 1) / 2 - (k - 1) * (k - 2) / 2 = k - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  change (m + 3) * (m + 2) / 2 - (m + 2) * (m + 1) / 2 = m + 2
  -- `(m+3)*(m+2)/2 = C(m+3,2) = (m+2) + C(m+2,2)` and `(m+2)*(m+1)/2 = C(m+2,2)`.
  rw [tri_eq_choose m, show (m + 3) * (m + 2) / 2 = (m + 1 + 2) * (m + 1 + 1) / 2 from rfl,
    tri_eq_choose (m + 1), choose_two_succ (m + 1)]
  have hbridge : (m + 1 + 1).choose 2 = (m + 2).choose 2 := rfl
  rw [hbridge]
  omega

/-! ### Item 4: the rational GOR for `L(K_k)` -/

/-- **Item 4 — Corollary 3.5 input: a rational GOR for `L(K_k)`** (genmamu tex:159-199).

Instantiates `LSS.exists_rat_gor` with `n = k*(k-1)/2`, `e = (k-1)*(k-2)/2 - 1`
(so `e+1 = D = (k-1)*(k-2)/2`), using:
* `hn : D ≤ n` (`dim_le_card`),
* `hconn : IsKVertexConnected (lineCompleteGraph k) (n - D)`, where `n - D = k-1`
  (`card_sub_dim`) and connectivity is `lineCompleteGraph_connectivity`,
* `hcard : ∀ σ v, (precNonNbrσ … v).card ≤ e` (`lineCompleteGraph_card_nonNeighbors`).

Output: `∃ f : Fin (k*(k-1)/2) → EuclideanSpace ℝ (Fin ((k-1)*(k-2)/2)), IsGOR (L(K_k)) f ∧
(∀ i c, (f i) c ∈ Set.range ((↑) : ℚ → ℝ))` — a general-position orthogonal representation in
`ℝ^{(k-1)(k-2)/2}` with rational coordinates, the form consumed by the VC degeneration
argument of Corollary 3.5. -/
theorem exists_rat_gor_lineCompleteGraph (k : ℕ) (hk : 3 ≤ k) :
    ∃ f : Fin (k * (k - 1) / 2) → EuclideanSpace ℝ (Fin ((k - 1) * (k - 2) / 2)),
      IsGOR (lineCompleteGraph k) f ∧
      (∀ i c, (f i) c ∈ Set.range ((↑) : ℚ → ℝ)) := by
  -- `e + 1 = D = (k-1)*(k-2)/2`, where `e = (k-1)*(k-2)/2 - 1`.
  have hD : (k - 1) * (k - 2) / 2 - 1 + 1 = (k - 1) * (k - 2) / 2 := dim_succ k hk
  -- Rewrite the target dimension `(k-1)*(k-2)/2` as `e + 1` so we can use the LSS output verbatim.
  rw [← hD]
  set e := (k - 1) * (k - 2) / 2 - 1 with he_def
  set n := k * (k - 1) / 2 with hn_def
  -- `e + 1 ≤ n`.
  have hn : e + 1 ≤ n := by rw [he_def, hD]; exact dim_le_card k
  -- `n - (e+1) = k - 1`.
  have hsub : n - (e + 1) = k - 1 := by rw [he_def, hn_def, hD]; exact card_sub_dim k hk
  -- Connectivity, transported through `n - (e+1) = k-1`.
  have hconn : IsKVertexConnected (lineCompleteGraph k) (n - (e + 1)) := by
    rw [hsub]; exact lineCompleteGraph_connectivity k hk
  -- The predecessor bound `hcard`.
  have hcard : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n),
      (precNonNbrσ (lineCompleteGraph k) σ v).card ≤ e :=
    fun σ v => lineCompleteGraph_card_nonNeighbors k σ v
  -- Instantiate the LSS existence theorem; its output has codomain `Fin (e+1)`, matching the goal.
  exact LSS.exists_rat_gor (G := lineCompleteGraph k) e hn hconn hcard

end LSS
