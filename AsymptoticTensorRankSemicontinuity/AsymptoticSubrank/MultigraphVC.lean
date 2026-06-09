/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.UniformVC
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.MinCut

/-!
# Corollary 3.5, the multigraph of `K_k` and its line-graph connectivity

Source (read verbatim):
* genmamu main theorem (general hypergraph `H`):
  `references/vrana-christandl-1603.03964-genmamu.tex:112-199`.
* The line-graph connectivity fact at genmamu:194-199:
  > "Let `H = ([k],E,I)` be a hypergraph.  Then its line graph has a general-position
  >  orthogonal representation `c : E → ℤ^{|E|−λ(H)}`. ... Since `H` is `λ(H)`-edge-connected,
  >  its line graph is `λ(H)`-vertex-connected."

This file generalizes the simple-`K_k` line graph (`LSS/CompleteLineGraph.lean`) to the
**multigraph** `H_a` of `K_k` with edge multiplicities `a : cgEdge k → ℕ+`:  each pair `e`
of legs is replaced by `a e` *parallel* edge-instances.

## The multigraph `H_a`

* Edge-instance type `mEdge a := Σ (e : cgEdge k), Fin (a e)` — `a e` parallel copies of pair `e`.
* Incidence `mInc a v ⟨e,c⟩ := v ∈ e.val` (ignores the copy index `c`); decidable, finite.
* This is the hypergraph `H_a = ([k], mEdge a, mInc a)`; each edge `⟨e,c⟩` has size 2 (pair `e`).

## The edge-connectivity `λ(H_a)`

`H_a` is `λ(H_a)`-edge-connected, where (genmamu:120, λ(H) = min over bipartitions of the number
of edges crossing)
```
λ(H_a) = min_{∅ ≠ I ⊊ [k]} ∑_{e crossing I} a e   = `mLambda a`
```
with "`e` crosses `I`" meaning the pair `e = {i,j}` has one endpoint in `I` and one outside.
Equivalently `2 ^ (mLambda a) = MinCut.minCut (fun i j => 2 ^ a {i,j})`, the dyadic min-cut
used downstream.

## The line graph `lineMultigraph a`

`lineMultigraph a : SimpleGraph (Fin (Fintype.card (mEdge a)))`, transported via the chosen
`mEdgeEquiv a : mEdge a ≃ Fin (card)`.  Two distinct edge-instances are adjacent iff they share
an endpoint of `K_k` (`¬ Disjoint` of their pairs).  Two *parallel* copies of the same pair `e`
(`e = e`, `c ≠ c'`) ARE adjacent (they share both endpoints), as required.

## Line-graph connectivity target (genmamu:194-199)

`lineMultigraph_connectivity : IsKVertexConnected (lineMultigraph a) (mLambda a)`.

The multiplicities add internally-disjoint paths, so the simple-graph Menger argument
(`LSS.lineCompleteGraph_connectivity`) generalizes; see the precise statement below.

The main graph-theoretic statement is `lineMultigraph_connectivity`; the downstream
achievability argument uses that theorem together with the multigraph definitions.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Finset BigOperators SimpleGraph

namespace Semicontinuity

universe u

open VC.Degeneration LSS

variable {k : ℕ}

/-! ## The multigraph incidence `(mEdge a, mInc a)`. -/

/-- The edge-instance type of the multigraph `H_a`: `a e` parallel copies of each pair `e`. -/
abbrev mEdge (a : cgEdge k → ℕ) : Type := Σ e : cgEdge k, Fin (a e)

instance (a : cgEdge k → ℕ) : Fintype (mEdge a) := by unfold mEdge; infer_instance
instance (a : cgEdge k → ℕ) : DecidableEq (mEdge a) := by unfold mEdge; infer_instance

/-- Incidence for the multigraph: vertex `v` is incident with the edge-instance `⟨e,c⟩`
    iff `v ∈ e` (the copy index `c` is ignored). -/
def mInc (a : cgEdge k → ℕ) : Fin k → mEdge a → Prop := fun v ec => v ∈ ec.1.val

instance (a : cgEdge k → ℕ) (v : Fin k) (ec : mEdge a) : Decidable (mInc a v ec) := by
  unfold mInc; infer_instance

/-- The underlying pair of an edge-instance (forgetting the copy index). -/
abbrev mPair (a : cgEdge k → ℕ) (ec : mEdge a) : cgEdge k := ec.1

/-- `|mEdge a| = ∑ e, a e` (the total edge count of the multigraph). -/
theorem card_mEdge (a : cgEdge k → ℕ) :
    Fintype.card (mEdge a) = ∑ e : cgEdge k, (a e : ℕ) := by
  classical
  have h : Fintype.card (mEdge a) = Fintype.card (Σ e : cgEdge k, Fin (a e)) :=
    Fintype.card_congr (Equiv.refl _)
  rw [h, Fintype.card_sigma]
  simp [Fintype.card_fin]

/-! ## The cut weight `λ(H_a)` (genmamu:120). -/

/-- The pair `e = {i,j}` *crosses* the bipartition `I` iff exactly one of `i,j` lies in `I`. -/
def crosses (I : Finset (Fin k)) (e : cgEdge k) : Prop :=
  (e.val ∩ I).Nonempty ∧ (e.val \ I).Nonempty

instance (I : Finset (Fin k)) (e : cgEdge k) : Decidable (crosses I e) := by
  unfold crosses; infer_instance

/-- The number of edge-instances of `H_a` crossing the bipartition `I`:
    `∑_{e crossing I} a e`. -/
def mCutWeight (a : cgEdge k → ℕ) (I : Finset (Fin k)) : ℕ :=
  ∑ e ∈ Finset.univ.filter (crosses I), (a e : ℕ)

/-- **The edge-connectivity `λ(H_a)`** (genmamu:120): the minimum over admissible
    bipartitions `∅ ≠ I ⊊ [k]` of the number of crossing edge-instances.
    Realised as a `Finset.inf'` over `MinCut.admissibleCuts k` (nonempty for `2 ≤ k`). -/
noncomputable def mLambda (a : cgEdge k → ℕ) (hk : 2 ≤ k) : ℕ :=
  (MinCut.admissibleCuts k).inf' (MinCut.admissibleCuts_nonempty hk) (mCutWeight a)

/-- `mLambda` is a lower bound for every admissible cut weight. -/
theorem mLambda_le_mCutWeight (a : cgEdge k → ℕ) (hk : 2 ≤ k)
    {I : Finset (Fin k)} (hI : I.Nonempty ∧ I ≠ Finset.univ) :
    mLambda a hk ≤ mCutWeight a I := by
  apply Finset.inf'_le
  rw [MinCut.mem_admissibleCuts]; exact hI

/-! ## The line graph `lineMultigraph a`.

Indexed on `Fin (Fintype.card (mEdge a))` so it is a `SimpleGraph (Fin n)`, the form consumed by
`IsKVertexConnected` and `LSS.exists_rat_gor`. -/

/-- The chosen bijection `mEdge a ≃ Fin (Fintype.card (mEdge a))`. -/
noncomputable def mEdgeEquiv (a : cgEdge k → ℕ) :
    Fin (Fintype.card (mEdge a)) ≃ mEdge a :=
  (Fintype.equivFin (mEdge a)).symm

/-- The edge-instance indexed by `i`. -/
noncomputable def mEdgeOf (a : cgEdge k → ℕ) (i : Fin (Fintype.card (mEdge a))) : mEdge a :=
  mEdgeEquiv a i

/-- **`L(H_a)`** — the line graph of the multigraph `H_a` (genmamu:159-199).  Vertices are the
    edge-instances (indexed by `Fin (card)`); two distinct instances are adjacent iff their pairs
    share a `K_k`-vertex (`¬ Disjoint`).  Parallel copies of the same pair are adjacent (they share
    both endpoints). -/
noncomputable def lineMultigraph (a : cgEdge k → ℕ) :
    SimpleGraph (Fin (Fintype.card (mEdge a))) where
  Adj i j := i ≠ j ∧ ¬ Disjoint (mEdgeOf a i).1.val (mEdgeOf a j).1.val
  symm := by
    rintro i j ⟨hne, hd⟩; exact ⟨hne.symm, fun h => hd h.symm⟩
  loopless := by rintro i ⟨hne, _⟩; exact hne rfl

noncomputable instance (a : cgEdge k → ℕ) : DecidableRel (lineMultigraph a).Adj :=
  fun _ _ => Classical.dec _

@[simp] theorem lineMultigraph_adj (a : cgEdge k → ℕ)
    (i j : Fin (Fintype.card (mEdge a))) :
    (lineMultigraph a).Adj i j ↔
      i ≠ j ∧ ¬ Disjoint (mEdgeOf a i).1.val (mEdgeOf a j).1.val :=
  Iff.rfl

/-! ## Elementary line-multigraph reachability helpers. -/

/-- A single induced edge gives `ReachableWithin` for `lineMultigraph`. -/
theorem mReachableWithin_of_adj (a : cgEdge k → ℕ)
    {T : Set (Fin (Fintype.card (mEdge a)))}
    {x y : Fin (Fintype.card (mEdge a))} (hx : x ∈ T) (hy : y ∈ T)
    (h : (lineMultigraph a).Adj x y) :
    ReachableWithin (lineMultigraph a) T x y := by
  refine ⟨hx, hy, ?_⟩
  apply SimpleGraph.Adj.reachable
  rw [SimpleGraph.induce_adj]
  exact h

/-- `ReachableWithin` is reflexive for `lineMultigraph` (within a set containing the point). -/
theorem mReachableWithin_refl (a : cgEdge k → ℕ)
    {T : Set (Fin (Fintype.card (mEdge a)))}
    {x : Fin (Fintype.card (mEdge a))} (hx : x ∈ T) :
    ReachableWithin (lineMultigraph a) T x x :=
  ⟨hx, hx, SimpleGraph.Reachable.refl _⟩

/-- `ReachableWithin` is transitive for `lineMultigraph`. -/
theorem mReachableWithin_trans (a : cgEdge k → ℕ)
    {T : Set (Fin (Fintype.card (mEdge a)))}
    {x y z : Fin (Fintype.card (mEdge a))}
    (h₁ : ReachableWithin (lineMultigraph a) T x y)
    (h₂ : ReachableWithin (lineMultigraph a) T y z) :
    ReachableWithin (lineMultigraph a) T x z := by
  obtain ⟨hx, hy, r₁⟩ := h₁
  obtain ⟨hy', hz, r₂⟩ := h₂
  refine ⟨hx, hz, ?_⟩
  have : (⟨y, hy⟩ : {w // w ∈ T}) = ⟨y, hy'⟩ := rfl
  exact r₁.trans (this ▸ r₂)

/-- Edge-instances whose underlying pairs cross `I`, counted as line-graph vertices. -/
noncomputable def crossingMEdgeIndices (a : cgEdge k → ℕ) (I : Finset (Fin k)) :
    Finset (Fin (Fintype.card (mEdge a))) :=
  Finset.univ.filter (fun i => crosses I (mEdgeOf a i).1)

/-- Counting crossing edge-instances by first summing over underlying pairs gives `mCutWeight`. -/
theorem card_crossingMEdgeIndices (a : cgEdge k → ℕ) (I : Finset (Fin k)) :
    (crossingMEdgeIndices a I).card = mCutWeight a I := by
  classical
  let B : Finset (mEdge a) := Finset.univ.filter (fun ec : mEdge a => crosses I ec.1)
  have hidx : (crossingMEdgeIndices a I).card = B.card := by
    refine Finset.card_bij (fun i _ => mEdgeOf a i) ?_ ?_ ?_
    · intro i hi
      simp only [B, crossingMEdgeIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hi
    · intro i _ j _ hij
      exact (mEdgeEquiv a).injective hij
    · intro ec hec
      refine ⟨(mEdgeEquiv a).symm ec, ?_, ?_⟩
      · simp only [B, crossingMEdgeIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hec ⊢
        simpa [mEdgeOf]
      · simp [mEdgeOf]
  rw [hidx]
  unfold B mCutWeight mEdge
  rw [show (Finset.univ.filter (fun ec : Σ e : cgEdge k, Fin (a e) => crosses I ec.1)).card =
      ((Finset.univ.filter (crosses I)).sigma
        (fun e : cgEdge k => (Finset.univ : Finset (Fin (a e))))).card by
    congr
    ext ec
    simp]
  rw [Finset.card_sigma]
  congr
  ext e
  by_cases h : crosses I e <;> simp

/-- If every crossing edge-instance lies in `S`, then the cut weight is at most `S.card`. -/
theorem mCutWeight_le_card_of_crossing_subset (a : cgEdge k → ℕ) (I : Finset (Fin k))
    (S : Finset (Fin (Fintype.card (mEdge a))))
    (hsub : crossingMEdgeIndices a I ⊆ S) :
    mCutWeight a I ≤ S.card := by
  rw [← card_crossingMEdgeIndices a I]
  exact Finset.card_le_card hsub

/-! ## the multigraph line-graph connectivity (genmamu:194-199). -/

/-- **(genmamu:194-199)** — the line graph of the `λ(H_a)`-edge-connected multigraph
    `H_a` is `λ(H_a)`-vertex-connected.

    For the multigraph `H_a` of `K_k` with multiplicities `a`, the edge-connectivity is
    `λ(H_a) = mLambda a = min_{∅≠I⊊[k]} ∑_{e crossing I} a e`.  genmamu:199 ("Since `H` is
    `λ(H)`-edge-connected, its line graph is `λ(H)`-vertex-connected") then gives
    `IsKVertexConnected (lineMultigraph a) (mLambda a)`.

    This generalizes `LSS.lineCompleteGraph_connectivity` (the simple `a ≡ 1` case,
    `mLambda = k-1`); the multiplicities only add internally vertex-disjoint paths.

    Hypotheses: `3 ≤ k` (so `K_k` is `2`-connected as a base) and `1 ≤ mLambda a hk` (the
    multigraph is connected — automatic since every pair has `a e ≥ 1` and `K_k` is connected for
    `k ≥ 2`; carried explicitly as the `IsKVertexConnected` first conjunct needs `λ < |E_a|`). -/
theorem lineMultigraph_connectivity (a : cgEdge k → ℕ) (hk : 3 ≤ k)
    (hpos : 1 ≤ mLambda a (by omega : 2 ≤ k)) :
    IsKVertexConnected (lineMultigraph a) (mLambda a (by omega)) := by
  classical
  constructor
  · -- First conjunct (genmamu:105-109, 194-199): `λ(H_a) < |E_a|` (#line-graph vertices).
    -- Since `H_a` is connected (`1 ≤ mLambda`), at least one edge is present; take a present
    -- edge `{x,y}` (admissible cut since `k ≥ 3`).  That edge does NOT cross the cut `{x,y}`
    -- (both endpoints inside), so `mCutWeight {x,y} ≤ |E_a| - a{x,y} < |E_a|`.
    -- `|E_a| = ∑_e a e ≥ mLambda ≥ 1`, so some present edge `e0` with `1 ≤ a e0` exists.
    have hsumpos : 1 ≤ ∑ e : cgEdge k, a e := by
      have hadm0 : (({⟨0, by omega⟩} : Finset (Fin k))).Nonempty ∧
          (({⟨0, by omega⟩} : Finset (Fin k))) ≠ Finset.univ := by
        refine ⟨Finset.singleton_nonempty _, ?_⟩
        intro h
        have : Fintype.card (Fin k) = 1 := by
          rw [← Finset.card_univ, ← h, Finset.card_singleton]
        simp [Fintype.card_fin] at this; omega
      have hle : mLambda a (by omega : 2 ≤ k) ≤ mCutWeight a {⟨0, by omega⟩} :=
        mLambda_le_mCutWeight a (by omega) hadm0
      have hcw : mCutWeight a ({⟨0, by omega⟩} : Finset (Fin k)) ≤ ∑ e : cgEdge k, a e := by
        unfold mCutWeight
        exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      omega
    -- Extract a present edge `e0`.
    obtain ⟨e0, _, he0⟩ : ∃ e0 ∈ (Finset.univ : Finset (cgEdge k)), 1 ≤ a e0 := by
      by_contra hno
      push_neg at hno
      have : ∑ e : cgEdge k, a e = 0 := by
        apply Finset.sum_eq_zero
        intro e he
        have := hno e he
        omega
      omega
    -- `e0 = {x,y}`, the cut `I := e0.val` is admissible (k ≥ 3 ⟹ `e0.val ≠ univ`).
    have hIne : (e0.val : Finset (Fin k)) ≠ Finset.univ := by
      intro h
      have : Fintype.card (Fin k) = 2 := by
        rw [← Finset.card_univ, ← h, e0.2]
      simp [Fintype.card_fin] at this; omega
    have hInonempty : (e0.val : Finset (Fin k)).Nonempty := by
      rw [← Finset.card_pos, e0.2]; norm_num
    have hadm : (e0.val : Finset (Fin k)).Nonempty ∧ (e0.val : Finset (Fin k)) ≠ Finset.univ :=
      ⟨hInonempty, hIne⟩
    -- `e0` does NOT cross its own pair-cut `e0.val` (both endpoints inside ⟹ `e0.val \ e0.val =
    -- ∅`).
    have he0_notcross : e0 ∉ Finset.univ.filter (crosses e0.val) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hcr
      obtain ⟨_, hsd⟩ := hcr
      rw [Finset.sdiff_self] at hsd
      exact Finset.not_nonempty_empty hsd
    -- `mCutWeight (e0.val) = ∑_{e crossing} a e ≤ ∑_{e ≠ e0} a e ≤ |E_a| - a e0 < |E_a|`.
    have hcutlt : mCutWeight a (e0.val) < Fintype.card (mEdge a) := by
      rw [card_mEdge]
      unfold mCutWeight
      calc ∑ e ∈ Finset.univ.filter (crosses e0.val), a e
          ≤ ∑ e ∈ (Finset.univ.erase e0), a e :=
            Finset.sum_le_sum_of_subset (by
              intro e he
              rw [Finset.mem_erase]
              refine ⟨?_, Finset.mem_univ _⟩
              intro hee
              subst hee
              exact he0_notcross he)
        _ < ∑ e : cgEdge k, a e := by
            rw [← Finset.sum_erase_add _ _ (Finset.mem_univ e0)]
            omega
    exact lt_of_le_of_lt (mLambda_le_mCutWeight a (by omega) hadm) hcutlt
  · intro S hS u v hu hv
    set T : Set (Fin (Fintype.card (mEdge a))) := (↑S)ᶜ with hT
    have huT : u ∈ T := by simp [hT, hu]
    have hvT : v ∈ T := by simp [hT, hv]
    by_contra hnot
    -- `C` is the component of `u` in the line graph after deleting `S`.
    set C : Finset (Fin (Fintype.card (mEdge a))) :=
      Finset.univ.filter
        (fun x => x ∉ S ∧ ReachableWithin (lineMultigraph a) T u x) with hC
    have huC : u ∈ C := by
      rw [hC]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hu, mReachableWithin_refl a huT⟩
    have hC_notS :
        ∀ {x : Fin (Fintype.card (mEdge a))}, x ∈ C → x ∉ S := by
      intro x hx
      have hx' : x ∉ S ∧ ReachableWithin (lineMultigraph a) T u x := by
        simpa [hC] using hx
      exact hx'.1
    have hC_reach :
        ∀ {x : Fin (Fintype.card (mEdge a))}, x ∈ C →
          ReachableWithin (lineMultigraph a) T u x := by
      intro x hx
      have hx' : x ∉ S ∧ ReachableWithin (lineMultigraph a) T u x := by
        simpa [hC] using hx
      exact hx'.2
    have hvnotC : v ∉ C := by
      intro hvC
      exact hnot (hC_reach hvC)
    set I : Finset (Fin k) :=
      Finset.univ.filter
        (fun p => ∃ x ∈ C, p ∈ (mEdgeOf a x).1.val) with hI
    have hInonempty : I.Nonempty := by
      have hpair : (mEdgeOf a u).1.val.Nonempty := by
        rw [← Finset.card_pos, (mEdgeOf a u).1.2]
        norm_num
      obtain ⟨p, hp⟩ := hpair
      exact ⟨p, by
        rw [hI]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨u, huC, hp⟩⟩
    have hv_endpoint_notI : ∀ p ∈ (mEdgeOf a v).1.val, p ∉ I := by
      intro p hpv hpI
      obtain ⟨x, hxC, hpx⟩ : ∃ x ∈ C, p ∈ (mEdgeOf a x).1.val := by
        simpa [hI] using hpI
      have hxT : x ∈ T := by simp [hT, hC_notS hxC]
      have hxreach : ReachableWithin (lineMultigraph a) T u x := hC_reach hxC
      have hxv : x ≠ v := by
        intro hxv
        subst x
        exact hvnotC hxC
      have hadj : (lineMultigraph a).Adj x v := by
        refine ⟨hxv, ?_⟩
        rw [Finset.not_disjoint_iff]
        exact ⟨p, hpx, hpv⟩
      exact hnot (mReachableWithin_trans a hxreach (mReachableWithin_of_adj a hxT hvT hadj))
    have hInotuniv : I ≠ Finset.univ := by
      intro h
      have hpair : (mEdgeOf a v).1.val.Nonempty := by
        rw [← Finset.card_pos, (mEdgeOf a v).1.2]
        norm_num
      obtain ⟨p, hp⟩ := hpair
      exact hv_endpoint_notI p hp (by rw [h]; simp)
    have hcross_subset : crossingMEdgeIndices a I ⊆ S := by
      intro w hw
      by_contra hwS
      have hwcross : crosses I (mEdgeOf a w).1 := by
        simpa [crossingMEdgeIndices] using hw
      obtain ⟨hpNonempty, hqNonempty⟩ := hwcross
      obtain ⟨p, hpint⟩ := hpNonempty
      have hp_pair : p ∈ (mEdgeOf a w).1.val := (Finset.mem_inter.mp hpint).1
      have hpI : p ∈ I := (Finset.mem_inter.mp hpint).2
      obtain ⟨q, hqdiff⟩ := hqNonempty
      have hq_pair : q ∈ (mEdgeOf a w).1.val := (Finset.mem_sdiff.mp hqdiff).1
      have hq_notI : q ∉ I := (Finset.mem_sdiff.mp hqdiff).2
      obtain ⟨x, hxC, hpx⟩ : ∃ x ∈ C, p ∈ (mEdgeOf a x).1.val := by
        simpa [hI] using hpI
      have hxT : x ∈ T := by simp [hT, hC_notS hxC]
      have hwT : w ∈ T := by simp [hT, hwS]
      by_cases hxw : x = w
      · subst x
        exact hq_notI (by
          rw [hI]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨w, hxC, hq_pair⟩)
      · have hadj : (lineMultigraph a).Adj x w := by
          refine ⟨hxw, ?_⟩
          rw [Finset.not_disjoint_iff]
          exact ⟨p, hpx, hp_pair⟩
        have hwreach : ReachableWithin (lineMultigraph a) T u w :=
          mReachableWithin_trans a (hC_reach hxC) (mReachableWithin_of_adj a hxT hwT hadj)
        have hwC : w ∈ C := by
          rw [hC]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hwS, hwreach⟩
        exact hq_notI (by
          rw [hI]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨w, hwC, hq_pair⟩)
    have hleCut : mLambda a (by omega) ≤ mCutWeight a I :=
      mLambda_le_mCutWeight a (by omega) ⟨hInonempty, hInotuniv⟩
    have hcutLeS : mCutWeight a I ≤ S.card :=
      mCutWeight_le_card_of_crossing_subset a I S hcross_subset
    omega

end Semicontinuity

namespace Semicontinuity

universe u

open Finset BigOperators Polynomial SimpleGraph
open VC.Degeneration LSS

variable {k : ℕ}

/-! ## multigraph Vrana-Christandl achievability. -/

theorem m_edgesIncident_iff (a : cgEdge k → ℕ) (e f : mEdge a) :
    edgesIncident (mInc a) e f ↔ ¬ Disjoint e.1.val f.1.val := by
  unfold edgesIncident mInc
  rw [Finset.not_disjoint_iff]

theorem m_edgesIncident_self (a : cgEdge k → ℕ) (e : mEdge a) :
    edgesIncident (mInc a) e e := by
  rw [m_edgesIncident_iff]
  intro hdisj
  have hne : (e.1.val).Nonempty := by
    rw [← Finset.card_pos, e.1.2]; norm_num
  obtain ⟨x, hx⟩ := hne
  exact (Finset.disjoint_left.mp hdisj) hx hx

theorem m_not_adj_of_not_incident (a : cgEdge k → ℕ) {e f : mEdge a} (hef : e ≠ f)
    (hni : ¬ edgesIncident (mInc a) e f) :
    ¬ (lineMultigraph a).Adj ((mEdgeEquiv a).symm e) ((mEdgeEquiv a).symm f) := by
  rw [lineMultigraph_adj]
  rintro ⟨_, hnd⟩
  apply hni
  rw [m_edgesIncident_iff]
  simpa [mEdgeOf] using hnd

noncomputable def mIntRep {N D : ℕ} {a : cgEdge k → ℕ}
    (f : Fin N → EuclideanSpace ℝ (Fin D))
    (hrat : ∀ i r, (f i) r ∈ Set.range ((↑) : ℚ → ℝ))
    (eqv : mEdge a ≃ Fin N) (e : mEdge a) (r : Fin D) : ℤ :=
  (qCoord f hrat (eqv e) r).num *
    ((cgDen f hrat (eqv e) : ℤ) / ((qCoord f hrat (eqv e) r).den : ℤ))

theorem mIntRep_cast {N D : ℕ} {a : cgEdge k → ℕ}
    (f : Fin N → EuclideanSpace ℝ (Fin D))
    (hrat : ∀ i r, (f i) r ∈ Set.range ((↑) : ℚ → ℝ))
    (eqv : mEdge a ≃ Fin N) (e : mEdge a) (r : Fin D) :
    ((mIntRep f hrat eqv e r : ℤ) : ℚ)
      = qCoord f hrat (eqv e) r * (cgDen f hrat (eqv e) : ℚ) := by
  obtain ⟨t, ht⟩ := cgDen_dvd f hrat (eqv e) r
  set q := qCoord f hrat (eqv e) r with hq
  set m := cgDen f hrat (eqv e) with hm
  have hqden : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_nz
  unfold mIntRep
  rw [← hq, ← hm]
  have hdivt : (m : ℤ) / (q.den : ℤ) = (t : ℤ) := by
    rw [ht]; push_cast; rw [Int.mul_ediv_cancel_left _ hqden]
  rw [hdivt]
  rw [ht]; push_cast
  have hqq : (q.num : ℚ) = q * (q.den : ℚ) := by
    have hd := Rat.num_div_den q
    have hqden' : ((q.den : ℚ)) ≠ 0 := by exact_mod_cast q.den_nz
    field_simp at hd
    linarith [hd]
  rw [hqq]; ring

noncomputable def mRealRep {N D : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin D))
    (hrat : ∀ i r, (f i) r ∈ Set.range ((↑) : ℚ → ℝ)) (i : Fin N) :
    EuclideanSpace ℝ (Fin D) :=
  cgRealRep f hrat i

theorem mRealRep_apply {N D : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin D))
    (hrat : ∀ i r, (f i) r ∈ Set.range ((↑) : ℚ → ℝ)) (i : Fin N) (r : Fin D) :
    (mRealRep f hrat i) r = (cgDen f hrat i : ℝ) * (f i) r := by
  exact cgRealRep_apply f hrat i r

theorem mRealRep_eq_mIntRep {N D : ℕ} {a : cgEdge k → ℕ}
    (f : Fin N → EuclideanSpace ℝ (Fin D))
    (hrat : ∀ i r, (f i) r ∈ Set.range ((↑) : ℚ → ℝ))
    (eqv : mEdge a ≃ Fin N) (e : mEdge a) (r : Fin D) :
    (mRealRep f hrat (eqv e)) r = ((mIntRep f hrat eqv e r : ℤ) : ℝ) := by
  rw [mRealRep_apply]
  have hq : ((mIntRep f hrat eqv e r : ℤ) : ℚ)
      = qCoord f hrat (eqv e) r * (cgDen f hrat (eqv e) : ℚ) :=
    mIntRep_cast f hrat eqv e r
  have := congrArg (fun q : ℚ => (q : ℝ)) hq
  push_cast at this
  rw [this, ← qCoord_spec f hrat (eqv e) r]
  push_cast
  ring

theorem generalPosition_mIntRep {N D : ℕ} {a : cgEdge k → ℕ}
    (f : Fin N → EuclideanSpace ℝ (Fin D))
    (hf : IsGP f) (hrat : ∀ i r, (f i) r ∈ Set.range ((↑) : ℚ → ℝ))
    (eqv : mEdge a ≃ Fin N) :
    GeneralPosition (mIntRep f hrat eqv) := by
  have hgp' : IsGP (mRealRep f hrat) :=
    isGP_smul hf (fun i => by
      have := cgDen_pos f hrat i; positivity)
  exact generalPosition_of_isGP (c := mIntRep f hrat eqv) (f := mRealRep f hrat) eqv hgp'
    (fun e r => mRealRep_eq_mIntRep f hrat eqv e r)

theorem idot_mIntRep_eq_inner {N D : ℕ} {a : cgEdge k → ℕ}
    (f : Fin N → EuclideanSpace ℝ (Fin D))
    (hrat : ∀ i r, (f i) r ∈ Set.range ((↑) : ℚ → ℝ))
    (eqv : mEdge a ≃ Fin N) (e e' : mEdge a) :
    ((idot (mIntRep f hrat eqv e) (mIntRep f hrat eqv e') : ℤ) : ℝ)
      = inner ℝ (mRealRep f hrat (eqv e)) (mRealRep f hrat (eqv e')) := by
  rw [PiLp.inner_apply]
  unfold idot
  push_cast
  apply Finset.sum_congr rfl
  intro r _
  rw [RCLike.inner_apply, conj_trivial]
  rw [mRealRep_eq_mIntRep, mRealRep_eq_mIntRep]
  ring

theorem horth_mIntRep {D : ℕ} {a : cgEdge k → ℕ}
    (f : Fin (Fintype.card (mEdge a)) → EuclideanSpace ℝ (Fin D))
    (hf : IsGOR (lineMultigraph a) f)
    (hrat : ∀ i r, (f i) r ∈ Set.range ((↑) : ℚ → ℝ)) :
    ∀ e e' : mEdge a, ¬ edgesIncident (mInc a) e e' →
      idot (mIntRep f hrat ((mEdgeEquiv a).symm) e)
        (mIntRep f hrat ((mEdgeEquiv a).symm) e') = 0 := by
  intro e e' hni
  have hne : e ≠ e' := by
    rintro rfl; exact hni (m_edgesIncident_self a e)
  have hvne : (mEdgeEquiv a).symm e ≠ (mEdgeEquiv a).symm e' :=
    fun h => hne ((mEdgeEquiv a).symm.injective h)
  have hnadj := m_not_adj_of_not_incident a hne hni
  have hor : inner ℝ (f ((mEdgeEquiv a).symm e)) (f ((mEdgeEquiv a).symm e')) = (0 : ℝ) :=
    hf.isOR ((mEdgeEquiv a).symm e) ((mEdgeEquiv a).symm e') hvne hnadj
  have hscaled : inner ℝ (mRealRep f hrat ((mEdgeEquiv a).symm e))
      (mRealRep f hrat ((mEdgeEquiv a).symm e')) = (0 : ℝ) := by
    unfold mRealRep cgRealRep
    rw [inner_smul_left, inner_smul_right, hor]
    simp
  have hreal := idot_mIntRep_eq_inner f hrat ((mEdgeEquiv a).symm) e e'
  rw [hscaled] at hreal
  exact_mod_cast hreal

theorem mInc_iff_crosses_singleton (a : cgEdge k → ℕ) (v : Fin k) (e : mEdge a) :
    mInc a v e ↔ crosses ({v} : Finset (Fin k)) e.1 := by
  classical
  constructor
  · intro hv
    refine ⟨?_, ?_⟩
    · exact ⟨v, by simpa [mInc] using hv⟩
    · have hcard : e.1.val.card = 2 := e.1.2
      have hproper : e.1.val ≠ {v} := by
        intro h
        have := congrArg Finset.card h
        simp [hcard] at this
      have hsdiff_ne : (e.1.val \ {v}).Nonempty := by
        by_contra hne
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        have hsub : e.1.val ⊆ ({v} : Finset (Fin k)) := by
          intro x hx
          by_contra hxv
          have : x ∈ e.1.val \ {v} := by simp [hx, hxv]
          simp [hne] at this
        have h_eq : e.1.val = {v} := by
          apply Finset.eq_of_subset_of_card_le hsub
          rw [hcard, Finset.card_singleton]
          norm_num
        exact hproper h_eq
      exact hsdiff_ne
  · rintro ⟨hleft, _⟩
    obtain ⟨x, hx⟩ := hleft
    have hxpair : x ∈ e.1.val := (Finset.mem_inter.mp hx).1
    have hxv : x = v := by simpa using (Finset.mem_inter.mp hx).2
    simpa [mInc, hxv] using hxpair

theorem card_incident_mEdge_eq_cut_singleton (a : cgEdge k → ℕ) (v : Fin k) :
    (Finset.univ.filter (fun e : mEdge a => mInc a v e)).card =
      mCutWeight a ({v} : Finset (Fin k)) := by
  classical
  rw [← card_crossingMEdgeIndices a ({v} : Finset (Fin k))]
  refine Finset.card_bij (fun e _ => (mEdgeEquiv a).symm e) ?_ ?_ ?_
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    simpa [crossingMEdgeIndices, mEdgeOf, mInc_iff_crosses_singleton a v e] using he
  · intro e _ f _ h
    exact (mEdgeEquiv a).symm.injective h
  · intro i hi
    refine ⟨mEdgeOf a i, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hcross : crosses ({v} : Finset (Fin k)) (mEdgeOf a i).1 := by
        simpa [crossingMEdgeIndices] using hi
      exact (mInc_iff_crosses_singleton a v (mEdgeOf a i)).2 hcross
    · simp [mEdgeOf]

theorem card_nonInc_mEdge_le (a : cgEdge k → ℕ) (hk2 : 2 ≤ k) (v : Fin k) :
    (Finset.univ.filter (fun e : mEdge a => ¬ mInc a v e)).card ≤
      Fintype.card (mEdge a) - mLambda a hk2 := by
  classical
  have hpart := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (mEdge a)))
      (p := fun e : mEdge a => mInc a v e)
  have hinc : (Finset.univ.filter (fun e : mEdge a => mInc a v e)).card =
      mCutWeight a ({v} : Finset (Fin k)) :=
    card_incident_mEdge_eq_cut_singleton a v
  have hadm : ({v} : Finset (Fin k)).Nonempty ∧ ({v} : Finset (Fin k)) ≠ Finset.univ := by
    refine ⟨Finset.singleton_nonempty _, ?_⟩
    intro h
    have : Fintype.card (Fin k) = 1 := by
      rw [← Finset.card_univ, ← h, Finset.card_singleton]
    simp [Fintype.card_fin] at this
    omega
  have hlambda : mLambda a hk2 ≤
      (Finset.univ.filter (fun e : mEdge a => mInc a v e)).card := by
    rw [hinc]
    exact mLambda_le_mCutWeight a hk2 hadm
  have hsum : (Finset.univ.filter (fun e : mEdge a => mInc a v e)).card +
      (Finset.univ.filter (fun e : mEdge a => ¬ mInc a v e)).card =
      Fintype.card (mEdge a) := by
    simpa [add_comm] using hpart
  omega

theorem mLambda_le_card_mEdge (a : cgEdge k → ℕ) (hk : 3 ≤ k) :
    mLambda a (by omega : 2 ≤ k) ≤ Fintype.card (mEdge a) := by
  classical
  let v : Fin k := ⟨0, by omega⟩
  have hle := mLambda_le_mCutWeight a (by omega : 2 ≤ k)
    (I := ({v} : Finset (Fin k))) ?_
  · have hcut :
        mCutWeight a ({v} : Finset (Fin k)) ≤ Fintype.card (mEdge a) := by
      rw [← card_crossingMEdgeIndices a ({v} : Finset (Fin k))]
      simpa using Finset.card_le_univ (crossingMEdgeIndices a ({v} : Finset (Fin k)))
    exact le_trans hle hcut
  · refine ⟨Finset.singleton_nonempty _, ?_⟩
    intro h
    have : Fintype.card (Fin k) = 1 := by
      rw [← Finset.card_univ, ← h, Finset.card_singleton]
    simp [Fintype.card_fin] at this
    omega

theorem card_sub_mD_eq_mLambda (a : cgEdge k → ℕ) (hk : 3 ≤ k) :
    Fintype.card (mEdge a) -
        (Fintype.card (mEdge a) - mLambda a (by omega : 2 ≤ k)) =
      mLambda a (by omega : 2 ≤ k) := by
  exact Nat.sub_sub_self (mLambda_le_card_mEdge a hk)

theorem mD_le_card (a : cgEdge k → ℕ) (hk : 3 ≤ k) :
    Fintype.card (mEdge a) - mLambda a (by omega : 2 ≤ k) ≤
      Fintype.card (mEdge a) := by
  exact Nat.sub_le _ _

theorem mEdgeOwner_inc_aux (e : cgEdge k) : (e.val).Nonempty := by
  rw [← Finset.card_pos, e.2]; norm_num

noncomputable def mEdgeOwner (a : cgEdge k → ℕ) (e : mEdge a) : Fin k :=
  (mEdgeOwner_inc_aux e.1).choose

theorem mEdgeOwner_inc (a : cgEdge k → ℕ) (e : mEdge a) :
    mInc a (mEdgeOwner a e) e := by
  unfold mEdgeOwner mInc
  exact (mEdgeOwner_inc_aux e.1).choose_spec

noncomputable def mPairOwner (a : cgEdge k → ℕ) (e f : mEdge a) : Fin k := by
  classical
  exact if h : edgesIncident (mInc a) e f then h.choose else mEdgeOwner a e

theorem mPairOwner_inc (a : cgEdge k → ℕ) {e f : mEdge a}
    (h : edgesIncident (mInc a) e f) :
    mInc a (mPairOwner a e f) e ∧ mInc a (mPairOwner a e f) f := by
  classical
  unfold mPairOwner
  rw [dif_pos h]
  exact h.choose_spec

/-- **Predecessor non-neighbour bound** for
    `lineMultigraph a`, the `hcard` hypothesis of `LSS.exists_rat_gor`.

    Multigraph generalization of `LSS.lineCompleteGraph_card_nonNeighbors`
    (`LSS/CompleteLineGraph.lean`): the non-neighbours of an edge-instance `v` in `L(H_a)`
    are the edge-instances whose pair is *disjoint* from `v`'s pair; their count is bounded
    by `|E_a| − λ(H_a) − 1`.  In the simple case this is `C(k,2) − (k−1) − 1`; here the
    multiplicities scale both `|E_a|` and the disjoint count, and the `−1` comes from a
    positive copy of an edge incident with `v`'s second endpoint but not its first (which is
    a neighbour, removed from the bound).

    This is a pure finite counting fact (no analysis). The core
    `multigraph_asympSubrank_ge` and the washout argument consume its statement. -/
theorem lineMultigraph_card_nonNeighbors (a : cgEdge k → ℕ) (hk : 3 ≤ k)
    (σ : Equiv.Perm (Fin (Fintype.card (mEdge a))))
    (v : Fin (Fintype.card (mEdge a))) :
    (precNonNbrσ (lineMultigraph a) σ v).card ≤
      Fintype.card (mEdge a) - mLambda a (by omega : 2 ≤ k) - 1 := by
  classical
  let ev : mEdge a := mEdgeOf a v
  obtain ⟨i, j, hij, hev⟩ := Finset.card_eq_two.mp ev.1.2
  let P : Finset (Fin (Fintype.card (mEdge a))) :=
    precNonNbrσ (lineMultigraph a) σ v
  let T : Finset (Fin (Fintype.card (mEdge a))) :=
    Finset.univ.filter
      (fun u => ¬ mInc a i (mEdgeOf a u) ∧ ¬ mInc a j (mEdgeOf a u))
  let U : Finset (Fin (Fintype.card (mEdge a))) :=
    Finset.univ.filter (fun u => ¬ mInc a i (mEdgeOf a u))
  have hi_ev : i ∈ ev.1.val := by
    rw [hev]
    exact Finset.mem_insert_self _ _
  have hj_ev : j ∈ ev.1.val := by
    rw [hev]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hPsubT : P ⊆ T := by
    intro u hu
    have hu' : u ∈ precNonNbrσ (lineMultigraph a) σ v := by
      simpa [P] using hu
    have hmem := (mem_precNonNbrσ (lineMultigraph a) σ).1 hu'
    obtain ⟨hlt, hnadj⟩ := hmem
    have huv : u ≠ v := by
      intro huv
      subst u
      exact (lt_irrefl _ hlt)
    have hdisj : Disjoint ev.1.val (mEdgeOf a u).1.val := by
      by_contra hnot
      exact hnadj ⟨huv.symm, by simpa [ev] using hnot⟩
    have hi_not : ¬ mInc a i (mEdgeOf a u) := by
      intro hiu
      exact (Finset.disjoint_left.mp hdisj) hi_ev (by simpa [mInc] using hiu)
    have hj_not : ¬ mInc a j (mEdgeOf a u) := by
      intro hju
      exact (Finset.disjoint_left.mp hdisj) hj_ev (by simpa [mInc] using hju)
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hi_not, hj_not⟩
  -- `{i,j}` is the pair of `ev`; reconstruct the cgEdge `eij` and `ev.1 = eij`.
  have hij_pair : ev.1.val = ({i, j} : Finset (Fin k)) := hev
  let eij : cgEdge k := ⟨({i, j} : Finset (Fin k)), Finset.card_pair hij⟩
  -- `T` (indices) bijects with `Tset := {e : mEdge a | ¬inc i ∧ ¬inc j}`.
  have hTcard :
      T.card = (Finset.univ.filter (fun ec : mEdge a => ¬ mInc a i ec ∧ ¬ mInc a j ec)).card := by
    refine Finset.card_bij (fun u _ => mEdgeOf a u) ?_ ?_ ?_
    · intro u hu
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      exact hu
    · intro u _ w _ huw
      exact (mEdgeEquiv a).injective (by simpa [mEdgeOf] using huw)
    · intro ec hec
      refine ⟨(mEdgeEquiv a).symm ec, ?_, ?_⟩
      · simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hec ⊢
        simpa [mEdgeOf] using hec
      · simp [mEdgeOf]
  -- **Partition** `mEdge a` into: `Tset` (neither i nor j), `Cross` (crosses {i,j}),
  -- `Pair` (instances of the pair {i,j}).  These are pairwise disjoint and cover `univ`.
  -- For a size-2 edge `e`: `e` crosses `{i,j}` ⟺ exactly one of i,j ∈ e; `e.1 = {i,j}` ⟺ both;
  -- neither ⟺ `e ∈ Tset`.
  set Tset : Finset (mEdge a) :=
    Finset.univ.filter (fun ec : mEdge a => ¬ mInc a i ec ∧ ¬ mInc a j ec) with hTset
  set Cross : Finset (mEdge a) :=
    Finset.univ.filter (fun ec : mEdge a => crosses ({i, j} : Finset (Fin k)) ec.1) with hCross
  set Pair : Finset (mEdge a) :=
    Finset.univ.filter (fun ec : mEdge a => ec.1 = eij) with hPair
  -- A vertex `x` is in `e.1` ⟺ `mInc a x e`.
  have hincmem : ∀ (x : Fin k) (ec : mEdge a), mInc a x ec ↔ x ∈ ec.1.val := fun x ec => Iff.rfl
  -- Membership trichotomy for each edge-instance.
  have hcover : ∀ ec : mEdge a, ec ∈ Tset ∨ ec ∈ Cross ∨ ec ∈ Pair := by
    intro ec
    have hcard2 : ec.1.val.card = 2 := ec.1.2
    by_cases hi : i ∈ ec.1.val <;> by_cases hj : j ∈ ec.1.val
    · -- both i,j ∈ ec ⟹ ec.1 = {i,j} (size 2) ⟹ Pair.
      right; right
      simp only [hPair, Finset.mem_filter, Finset.mem_univ, true_and]
      have hsub : ({i, j} : Finset (Fin k)) ⊆ ec.1.val := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have : ec.1.val = ({i, j} : Finset (Fin k)) :=
        (Finset.eq_of_subset_of_card_le hsub (by rw [hcard2, Finset.card_pair hij])).symm
      exact Subtype.ext this
    · -- i ∈, j ∉ ⟹ crosses {i,j}: the OTHER endpoint of `ec` lies outside `{i,j}`.
      right; left
      simp only [hCross, Finset.mem_filter, Finset.mem_univ, true_and, crosses]
      obtain ⟨x, y, hxy, hxy_eq⟩ := Finset.card_eq_two.mp hcard2
      -- `i ∈ {x,y}`; the other of `x,y` is `≠ i, ≠ j`, hence outside `{i,j}`.
      have hi_xy : i ∈ ({x, y} : Finset (Fin k)) := hxy_eq ▸ hi
      have hj_nxy : j ∉ ({x, y} : Finset (Fin k)) := fun h => hj (hxy_eq ▸ h)
      rw [Finset.mem_insert, Finset.mem_singleton] at hi_xy
      refine ⟨⟨i, Finset.mem_inter.mpr ⟨hi, Finset.mem_insert_self _ _⟩⟩, ?_⟩
      -- pick the other endpoint
      rcases hi_xy with rfl | rfl
      · refine ⟨y, Finset.mem_sdiff.mpr
          ⟨hxy_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_⟩⟩
        rw [Finset.mem_insert, Finset.mem_singleton]; push_neg
        refine ⟨fun h => hxy h.symm, fun h => hj_nxy ?_⟩
        rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · refine ⟨x, Finset.mem_sdiff.mpr ⟨hxy_eq ▸ Finset.mem_insert_self _ _, ?_⟩⟩
        rw [Finset.mem_insert, Finset.mem_singleton]; push_neg
        refine ⟨fun h => hxy h, fun h => hj_nxy ?_⟩
        rw [h]; exact Finset.mem_insert_self _ _
    · -- i ∉, j ∈ ⟹ crosses {i,j}: symmetric.
      right; left
      simp only [hCross, Finset.mem_filter, Finset.mem_univ, true_and, crosses]
      obtain ⟨x, y, hxy, hxy_eq⟩ := Finset.card_eq_two.mp hcard2
      have hj_xy : j ∈ ({x, y} : Finset (Fin k)) := hxy_eq ▸ hj
      have hi_nxy : i ∉ ({x, y} : Finset (Fin k)) := fun h => hi (hxy_eq ▸ h)
      rw [Finset.mem_insert, Finset.mem_singleton] at hj_xy
      refine ⟨⟨j, Finset.mem_inter.mpr
        ⟨hj, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩⟩, ?_⟩
      rcases hj_xy with rfl | rfl
      · refine ⟨y, Finset.mem_sdiff.mpr
          ⟨hxy_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_⟩⟩
        rw [Finset.mem_insert, Finset.mem_singleton]; push_neg
        refine ⟨fun h => hi_nxy ?_, fun h => hxy h.symm⟩
        rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · refine ⟨x, Finset.mem_sdiff.mpr ⟨hxy_eq ▸ Finset.mem_insert_self _ _, ?_⟩⟩
        rw [Finset.mem_insert, Finset.mem_singleton]; push_neg
        refine ⟨fun h => hi_nxy ?_, fun h => hxy h⟩
        rw [h]; exact Finset.mem_insert_self _ _
    · -- neither ⟹ Tset.
      left
      simp only [hTset, Finset.mem_filter, Finset.mem_univ, true_and, hincmem]
      exact ⟨hi, hj⟩
  have hdisj_TsetCross : Disjoint Tset Cross := by
    rw [Finset.disjoint_left]
    intro ec hT hC
    simp only [hTset, Finset.mem_filter, Finset.mem_univ, true_and, hincmem] at hT
    simp only [hCross, Finset.mem_filter, Finset.mem_univ, true_and, crosses] at hC
    obtain ⟨x, hx⟩ := hC.1
    have hxpair : x ∈ ec.1.val := (Finset.mem_inter.mp hx).1
    have hxij : x ∈ ({i, j} : Finset (Fin k)) := (Finset.mem_inter.mp hx).2
    rw [Finset.mem_insert, Finset.mem_singleton] at hxij
    rcases hxij with rfl | rfl
    · exact hT.1 hxpair
    · exact hT.2 hxpair
  have hdisj_TsetPair : Disjoint Tset Pair := by
    rw [Finset.disjoint_left]
    intro ec hT hP
    simp only [hTset, Finset.mem_filter, Finset.mem_univ, true_and, hincmem] at hT
    simp only [hPair, Finset.mem_filter, Finset.mem_univ, true_and] at hP
    apply hT.1
    rw [hP]; exact Finset.mem_insert_self _ _
  have hdisj_CrossPair : Disjoint Cross Pair := by
    rw [Finset.disjoint_left]
    intro ec hC hP
    simp only [hCross, Finset.mem_filter, Finset.mem_univ, true_and, crosses] at hC
    simp only [hPair, Finset.mem_filter, Finset.mem_univ, true_and] at hP
    obtain ⟨y, hy⟩ := hC.2
    have hypair : y ∈ ec.1.val := (Finset.mem_sdiff.mp hy).1
    have hynij : y ∉ ({i, j} : Finset (Fin k)) := (Finset.mem_sdiff.mp hy).2
    apply hynij
    rw [hP] at hypair
    exact hypair
  -- Cardinalities: `|Cross| = mCutWeight {i,j}`, `|Pair| = a eij`.
  have hCrosscard : Cross.card = mCutWeight a ({i, j} : Finset (Fin k)) := by
    rw [← card_crossingMEdgeIndices a ({i, j} : Finset (Fin k))]
    refine Finset.card_bij (fun ec _ => (mEdgeEquiv a).symm ec) ?_ ?_ ?_
    · intro ec hec
      simp only [hCross, Finset.mem_filter, Finset.mem_univ, true_and] at hec
      simp only [crossingMEdgeIndices, Finset.mem_filter, Finset.mem_univ, true_and, mEdgeOf,
        Equiv.apply_symm_apply]
      exact hec
    · intro ec _ ed _ h
      exact (mEdgeEquiv a).symm.injective h
    · intro idx hidx
      refine ⟨mEdgeOf a idx, ?_, by simp [mEdgeOf]⟩
      simp only [crossingMEdgeIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hidx
      simp only [hCross, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hidx
  have hPaircard : Pair.card = a eij := by
    -- `Pair = {⟨eij, c⟩ | c : Fin (a eij)}`, card `a eij`.
    rw [hPair]
    have hbij : (Finset.univ : Finset (Fin (a eij))).card =
        (Finset.univ.filter (fun ec : mEdge a => ec.1 = eij)).card := by
      refine Finset.card_bij (fun c (_ : c ∈ (Finset.univ : Finset (Fin (a eij)))) =>
        (⟨eij, c⟩ : mEdge a)) ?_ ?_ ?_
      · intro c _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      · intro c _ d _ h
        simpa [Sigma.mk.injEq, heq_eq_eq] using h
      · intro ec hec
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hec
        obtain ⟨e, c⟩ := ec
        subst hec
        exact ⟨c, Finset.mem_univ _, rfl⟩
    rw [← hbij, Finset.card_univ, Fintype.card_fin]
  -- `a eij ≥ 1` (the witness `v = ev` is an instance of pair `{i,j} = eij`).
  have haij_pos : 1 ≤ a eij := by
    have hevPair : ev ∈ Pair := by
      simp only [hPair, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Subtype.ext hij_pair
    have : 0 < Pair.card := Finset.card_pos.mpr ⟨ev, hevPair⟩
    rw [hPaircard] at this; omega
  -- `mCutWeight {i,j} ≥ λ` (admissible cut, `k ≥ 3`).
  have hadmij : (({i, j} : Finset (Fin k))).Nonempty ∧
      (({i, j} : Finset (Fin k))) ≠ Finset.univ := by
    refine ⟨⟨i, Finset.mem_insert_self _ _⟩, ?_⟩
    intro h
    have : Fintype.card (Fin k) = 2 := by
      rw [← Finset.card_univ, ← h, Finset.card_pair hij]
    simp [Fintype.card_fin] at this; omega
  have hcutij : mLambda a (by omega : 2 ≤ k) ≤ mCutWeight a ({i, j} : Finset (Fin k)) :=
    mLambda_le_mCutWeight a (by omega) hadmij
  -- Partition card: `|Tset| + |Cross| + |Pair| = |E|`.
  have hpartition : Tset.card + Cross.card + Pair.card = Fintype.card (mEdge a) := by
    have hunion : Tset ∪ Cross ∪ Pair = (Finset.univ : Finset (mEdge a)) := by
      apply Finset.eq_univ_of_forall
      intro ec
      rcases hcover ec with h | h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
      · exact Finset.mem_union_right _ h
    have hdisj1 : Disjoint (Tset ∪ Cross) Pair := by
      rw [Finset.disjoint_union_left]; exact ⟨hdisj_TsetPair, hdisj_CrossPair⟩
    have : (Tset ∪ Cross ∪ Pair).card = Tset.card + Cross.card + Pair.card := by
      rw [Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hdisj_TsetCross]
    rw [hunion] at this
    rw [← this, Finset.card_univ]
  -- Conclude `|T| = |Tset| = |E| - mCutWeight{i,j} - a eij ≤ |E| - λ - 1`.
  have hTle :
      T.card ≤ Fintype.card (mEdge a) - mLambda a (by omega : 2 ≤ k) - 1 := by
    rw [hTcard, ← hTset, hCrosscard, hPaircard] at *
    rw [hTcard, ← hTset]
    omega
  exact le_trans (Finset.card_le_card hPsubT) hTle

theorem exists_mGorData (a : cgEdge k → ℕ) (hk : 3 ≤ k)
    (hpos : 1 ≤ mLambda a (by omega : 2 ≤ k)) :
    ∃ (c : mEdge a → Fin (Fintype.card (mEdge a) - mLambda a (by omega : 2 ≤ k)) → ℤ),
      (∀ e f : mEdge a, ¬ edgesIncident (mInc a) e f → idot (c e) (c f) = 0) ∧
      (∀ (N : ℕ) (g : Fin (Fintype.card (mEdge a) - mLambda a (by omega : 2 ≤ k)) → ℤ),
        GeneralPositionInjective (k := k) (mInc a) c N g) := by
  classical
  let card := Fintype.card (mEdge a)
  let D := card - mLambda a (by omega : 2 ≤ k)
  let e := D - 1
  have hDpos : 0 < D := by
    have hlt := (lineMultigraph_connectivity a hk hpos).1
    dsimp [D, card]
    omega
  have heD : e + 1 = D := by dsimp [e]; omega
  have hn : e + 1 ≤ card := by
    rw [heD]
    dsimp [D, card]
    exact mD_le_card a hk
  have hsub : card - (e + 1) = mLambda a (by omega : 2 ≤ k) := by
    rw [heD]
    dsimp [D, card]
    exact card_sub_mD_eq_mLambda a hk
  have hconn : IsKVertexConnected (lineMultigraph a) (card - (e + 1)) := by
    rw [hsub]
    exact lineMultigraph_connectivity a hk hpos
  have hcard : ∀ (σ : Equiv.Perm (Fin card)) v, (precNonNbrσ (lineMultigraph a) σ v).card ≤ e := by
    intro σ v
    dsimp [e, D, card]
    exact lineMultigraph_card_nonNeighbors a hk σ v
  obtain ⟨f, hgor, hrat⟩ := LSS.exists_rat_gor (G := lineMultigraph a) e hn hconn hcard
  change ∃ (c : mEdge a → Fin D → ℤ),
      (∀ e f : mEdge a, ¬ edgesIncident (mInc a) e f → idot (c e) (c f) = 0) ∧
      (∀ (N : ℕ) (g : Fin D → ℤ),
        GeneralPositionInjective (k := k) (mInc a) c N g)
  rw [← heD]
  refine ⟨mIntRep f hrat ((mEdgeEquiv a).symm), ?_, ?_⟩
  · exact horth_mIntRep f hgor hrat
  · intro N g
    have hgp : GeneralPosition (mIntRep f hrat ((mEdgeEquiv a).symm)) :=
      generalPosition_mIntRep f hgor.isGP hrat ((mEdgeEquiv a).symm)
    have hDcard : e + 1 ≤ Fintype.card (mEdge a) := by
      simpa [card] using hn
    have hdef : ∀ v₀ : Fin k,
        (Finset.univ.filter (fun e : mEdge a => ¬ mInc a v₀ e)).card ≤
          e + 1 := by
      intro v₀
      rw [heD]
      dsimp [D, card]
      exact card_nonInc_mEdge_le a (by omega : 2 ≤ k) v₀
    exact generalPositionInjective_of_generalPosition (mInc a) hgp hDcard hdef N g

theorem borderSubrank_ghzH_fixedC_m {F : Type u} [Field F] (a : cgEdge k → ℕ) (hk : 3 ≤ k)
    {c : mEdge a → Fin (Fintype.card (mEdge a) - mLambda a (by omega : 2 ≤ k)) → ℤ}
    (horth : ∀ e f : mEdge a, ¬ edgesIncident (mInc a) e f → idot (c e) (c f) = 0)
    (hgpAll : ∀ (N : ℕ) (g : Fin (Fintype.card (mEdge a) - mLambda a (by omega : 2 ≤ k)) → ℤ),
      GeneralPositionInjective (k := k) (mInc a) c N g)
    {N : ℕ} (hN : 1 ≤ N) :
    N ^ (Fintype.card (mEdge a)) ≤
      (2 * cubeBound c * N) ^ (Fintype.card (mEdge a) - mLambda a (by omega : 2 ≤ k)) *
      borderSubrank (ghzH_asKTensor (F := F) (mInc a) hN) := by
  classical
  have hk2 : 2 ≤ k := by omega
  have hk0 : 0 < k := by omega
  set edgeOwner := mEdgeOwner a with hEO
  set pairOwner := mPairOwner a with hPO
  have hEdgeInc : ∀ e, mInc a (edgeOwner e) e := mEdgeOwner_inc a
  have hPairInc : ∀ e f, e ≠ f → idot (c e) (c f) ≠ 0 →
      mInc a (pairOwner e f) e ∧ mInc a (pairOwner e f) f := by
    intro e f hef hidot
    have hinc : edgesIncident (mInc a) e f := by
      by_contra hni; exact hidot (horth e f hni)
    exact mPairOwner_inc a hinc
  obtain ⟨g, hg⟩ := exists_g_solCount_ge c N hN
  have hM : solCount c N g ≤ borderSubrank (ghzH_asKTensor (F := F) (mInc a) hN) :=
    solCount_le_borderSubrank_ghzH (mInc a) c horth edgeOwner pairOwner ⟨0, hk0⟩
      hEdgeInc hPairInc hN hk0 g (hgpAll N g)
      (bddAbove_borderSubrankK_ghzH (mInc a) hN hk2)
      (bddAbove_borderRestricts_ghzH (mInc a) hN hk2)
  calc N ^ (Fintype.card (mEdge a))
      ≤ (2 * cubeBound c * N) ^
          (Fintype.card (mEdge a) - mLambda a (by omega : 2 ≤ k)) * solCount c N g := hg
    _ ≤ (2 * cubeBound c * N) ^
          (Fintype.card (mEdge a) - mLambda a (by omega : 2 ≤ k)) *
        borderSubrank (ghzH_asKTensor (F := F) (mInc a) hN) :=
        Nat.mul_le_mul_left _ hM

theorem ghzH_kronPow_equiv_inc {F : Type u} [Field F] {E : Type*} [Fintype E]
    [DecidableEq E] {k : ℕ} (inc : Fin k → E → Prop) [∀ v e, Decidable (inc v e)]
    {n : ℕ} (hn : 1 ≤ n) (m : ℕ) (hnm : 1 ≤ n ^ (m + 1)) :
    (⟨_, kronPowNat (ghzH_asKTensor (F := F) inc hn) m⟩ : TT F k).2
      ∼ₜ (⟨_, ghzH_asKTensor (F := F) inc hnm⟩ : TT F k).2 := by
  classical
  induction m with
  | zero =>
      have hnm' : 1 ≤ n := by simpa using hnm
      have hproof : hnm' = hn := Subsingleton.elim _ _
      convert (RestrictsEquiv.refl (ghzH_asKTensor (F := F) inc hn)) using 2
      · simp
      · simp
  | succ m ih =>
      let T := ghzH_asKTensor (F := F) inc hn
      have hNm : 1 ≤ n ^ (m + 1) := Nat.one_le_pow (m + 1) n hn
      have hprod : 1 ≤ n ^ (m + 1) * n := by
        simpa [pow_succ] using hnm
      have hcongr :
          (kronPowNat T m ⊠ T)
            ∼ₜ (ghzH_asKTensor (F := F) inc hNm ⊠ T) :=
        RestrictsEquiv.kron_congr (ih hNm) (RestrictsEquiv.refl T)
      have hstep :
          (ghzH_asKTensor (F := F) inc hNm ⊠ T)
            ∼ₜ ghzH_asKTensor (F := F) inc hprod :=
        ghzH_kron_step_equiv (F := F) inc hNm hn hprod
      simpa [T, kronPowNat, pow_succ] using hcongr.trans hstep

theorem ghzH_m_kronPow_equiv {F : Type u} [Field F] (a : cgEdge k → ℕ) (hk : 3 ≤ k)
    {n : ℕ} (hn : 1 ≤ n) (m : ℕ) (hnm : 1 ≤ n ^ (m + 1)) :
    (⟨_, kronPowNat (ghzH_asKTensor (F := F) (mInc a) hn) m⟩ : TT F k).2
      ∼ₜ (⟨_, ghzH_asKTensor (F := F) (mInc a) hnm⟩ : TT F k).2 := by
  exact ghzH_kronPow_equiv_inc (F := F) (inc := mInc a) hn m hnm

theorem ghzH_m_mk_ne_zero {F : Type u} [Field F] [NeZero k] (a : cgEdge k → ℕ)
    (hk : 3 ≤ k) {n : ℕ} (hn : 1 ≤ n) :
    TensorClass.mk ⟨_, ghzH_asKTensor (F := F) (mInc a) hn⟩ ≠ (0 : TensorClass F k) := by
  classical
  set i₀ : mEdge a → Fin n := fun _ => ⟨0, by omega⟩ with hi₀
  set idx : ∀ v : Fin k, Fin ((ghzHFormat (mInc a) hn v : ℕ+) : ℕ) :=
    fun v => (ghzHEquiv (mInc a) hn v) (globalToLocal (mInc a) i₀ v) with hidx
  apply mk_ne_zero_of_entry _ (idx := idx)
  have hval : ghzH_asKTensor (F := F) (mInc a) hn idx = 1 := by
    unfold ghzH_asKTensor reindexKTensor
    have : (fun v => (ghzHEquiv (mInc a) hn v).symm (idx v))
        = globalToLocal (mInc a) i₀ := by
      funext v; rw [hidx]; simp
    rw [this]
    exact ghzHTensor_globalToLocal (mInc a) i₀
  rw [hval]; exact one_ne_zero

theorem multigraph_asympSubrank_ge {F : Type u} [Field F] [Infinite F]
    (a : cgEdge k → ℕ) (hk : 3 ≤ k)
    (hpos : 1 ≤ mLambda a (by omega : 2 ≤ k)) :
    (2 : ℝ) ^ (mLambda a (by omega : 2 ≤ k)) ≤
      asympSubrank (ghzH_asKTensor (F := F) (mInc a) (by norm_num : (1:ℕ) ≤ 2)) := by
  classical
  haveI : NeZero k := ⟨by omega⟩
  have hk2 : 2 ≤ k := by omega
  have hn1 : 1 ≤ (2 : ℕ) := by norm_num
  obtain ⟨c, horth, hgpAll⟩ := exists_mGorData a hk hpos
  let C : ℕ := cubeBound c
  let Dexp : ℕ := Fintype.card (mEdge a) - mLambda a (by omega : 2 ≤ k)
  let K : ℝ := (((2 * C) ^ Dexp : ℕ) : ℝ)
  set Q : ℝ := asympSubrank (ghzH_asKTensor (F := F) (mInc a) hn1) with hQ
  have hQnn : 0 ≤ Q := by rw [hQ]; exact asympSubrank_nonneg' hk2 _
  have hCpos : 1 ≤ C := one_le_cubeBound c
  have hKpos : 0 < K := by
    change 0 < (((2 * C) ^ Dexp : ℕ) : ℝ)
    have : 0 < (2 * C) ^ Dexp := pow_pos (by omega) Dexp
    exact_mod_cast this
  have hcardD :
      Fintype.card (mEdge a) = mLambda a (by omega : 2 ≤ k) + Dexp := by
    dsimp [Dexp]
    have := Nat.sub_add_cancel (mLambda_le_card_mEdge a hk)
    omega
  have hamp : ∀ m : ℕ, 1 ≤ m →
      ((2 : ℝ) ^ (mLambda a (by omega : 2 ≤ k))) ^ m ≤ K * Q ^ m := by
    intro m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    set N : ℕ := 2 ^ (m' + 1) with hN
    have hNpos : 1 ≤ N := Nat.one_le_pow _ _ (by omega)
    have hbound := borderSubrank_ghzH_fixedC_m (F := F) a hk (c := c) horth hgpAll
      (N := N) hNpos
    have hbr : (borderSubrank (ghzH_asKTensor (F := F) (mInc a) hNpos) : ℝ)
        ≤ asympSubrank (ghzH_asKTensor (F := F) (mInc a) hNpos) :=
      borderSubrank_le_asympSubrank hk2 _
    have hpow : asympSubrank (ghzH_asKTensor (F := F) (mInc a) hNpos) = Q ^ (m' + 1) := by
      have hequiv := ghzH_m_kronPow_equiv (F := F) a hk hn1 m' hNpos
      have h1 : asympSubrank (ghzH_asKTensor (F := F) (mInc a) hNpos)
          = asympSubrank (kronPowNat (ghzH_asKTensor (F := F) (mInc a) hn1) m') :=
        (asympSubrank_congr hk2 hequiv).symm
      rw [h1, asympSubrank_kronPowNat hk2 _ (ghzH_m_mk_ne_zero a hk hn1) m', ← hQ]
    have hboundR : ((N ^ (Fintype.card (mEdge a)) : ℕ) : ℝ) ≤
        (((2 * C * N) ^ Dexp : ℕ) : ℝ) *
          (borderSubrank (ghzH_asKTensor (F := F) (mInc a) hNpos) : ℝ) := by
      exact_mod_cast hbound
    have hchain : ((N : ℝ) ^ (Fintype.card (mEdge a))) ≤
        (((2 * C * N) ^ Dexp : ℕ) : ℝ) * Q ^ (m' + 1) := by
      calc ((N : ℝ) ^ (Fintype.card (mEdge a)))
          = ((N ^ (Fintype.card (mEdge a)) : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (((2 * C * N) ^ Dexp : ℕ) : ℝ) *
            (borderSubrank (ghzH_asKTensor (F := F) (mInc a) hNpos) : ℝ) := hboundR
        _ ≤ (((2 * C * N) ^ Dexp : ℕ) : ℝ) *
            asympSubrank (ghzH_asKTensor (F := F) (mInc a) hNpos) := by
            apply mul_le_mul_of_nonneg_left hbr; positivity
        _ = (((2 * C * N) ^ Dexp : ℕ) : ℝ) * Q ^ (m' + 1) := by rw [hpow]
    set P : ℝ := (2 : ℝ) ^ ((m' + 1) * Dexp) with hP
    have hPpos : 0 < P := by rw [hP]; positivity
    have hNr : (N : ℝ) = (2 : ℝ) ^ (m' + 1) := by rw [hN]; push_cast; ring
    have hLHS : ((N : ℝ) ^ (Fintype.card (mEdge a))) =
        ((2 : ℝ) ^ (mLambda a (by omega : 2 ≤ k))) ^ (m' + 1) * P := by
      rw [hNr, hP, ← pow_mul, ← pow_mul, ← pow_add, hcardD]
      ring_nf
    have hRHS : (((2 * C * N) ^ Dexp : ℕ) : ℝ) = K * P := by
      change (((2 * cubeBound c * N) ^ Dexp : ℕ) : ℝ) = K * P
      change _ = (((2 * cubeBound c) ^ Dexp : ℕ) : ℝ) * P
      rw [hP]
      push_cast
      rw [hNr, mul_pow, ← pow_mul]
    rw [hLHS, hRHS] at hchain
    have hcancel :
        ((2 : ℝ) ^ (mLambda a (by omega : 2 ≤ k))) ^ (m' + 1) * P ≤
          (K * P) * Q ^ (m' + 1) := hchain
    have hfin :
        ((2 : ℝ) ^ (mLambda a (by omega : 2 ≤ k))) ^ (m' + 1) * P ≤
          (K * Q ^ (m' + 1)) * P := by
      rw [mul_right_comm K P (Q ^ (m' + 1))] at hcancel
      linarith [hcancel]
    exact le_of_mul_le_mul_right hfin hPpos
  have := washout_const_le (s := (2 : ℝ) ^ (mLambda a (by omega : 2 ≤ k))) (Q := Q) (K := K)
    (by positivity) hQnn hKpos hamp
  rwa [hQ] at this

end Semicontinuity

namespace Semicontinuity

universe u

open VC.Degeneration LSS

variable {k : ℕ}

/-! ## Weighted pair-unit Kronecker product. -/

/-- Weighted pair-unit Kronecker product
`⊠_{i<j} ⟨q i j⟩_{i,j}`.

This is the weighted analogue of `pairUnitKronAll`: it uses the same `cgPairsList`,
`pairUnitTT`, and `kronFoldl` machinery, but the rank of the factor at the pair `p`
is `q p.1 p.2` instead of a uniform `n`.  As for `pairUnitTT`, zero weights are handled
by the rank-one branch, so the definition is total. -/
noncomputable def pairUnitKronQ (F : Type u) [Field F] {k : ℕ}
    (q : Fin k → Fin k → ℕ) : TT F k :=
  kronFoldl (TT.of (unitTensor F (k := k) (1 : ℕ+)))
    ((cgPairsList k).map (fun p => pairUnitTT (F := F) (q p.1 p.2) p))

/-! ## `subrank` / `asympSubrank` are monotone under `Restricts`.

These are the load-bearing monotonicity lemmas: a restriction `S ≤ₜ T` only enlarges
the set of unit-tensors that restrict into the target, so `subrank S ≤ subrank T`, and
the same holds level-by-level for Kronecker powers, hence for `asympSubrank`.  The
`subrank` base case uses the abstract Strassen-preorder bridge
(`SpectrumBridge.subrank_eq_abstract` + abstract `StrassenPreorder.subrank_mono`),
where `pF.rel (mk S) (mk T) = Restricts S T` (`TensorStrassenPreorder.relClass_mk`). -/

/-- **`subrank` is monotone under `Restricts`** (piece 1, base case).
Via the abstract bridge: `pF.rel (mk S) (mk T)` is definitionally `Restricts S T`
(`relClass_mk`), so abstract `subrank_mono` plus the concrete↔abstract bridge gives it. -/
theorem subrank_mono_restricts {F : Type u} [Field F] {k : ℕ} [NeZero k] (hk : 2 ≤ k)
    {dS dT : Fin k → ℕ+} {S : KTensor F dS} {T : KTensor F dT}
    (hST : Restricts S T) : subrank S ≤ subrank T := by
  classical
  set pF := tensorStrassenPreorder (F := F) hk with hpF
  have hrel : pF.rel (TensorClass.mk ⟨dS, S⟩) (TensorClass.mk ⟨dT, T⟩) := by
    rw [hpF]; change Restricts S T; exact hST
  have h := pF.subrank_mono hrel
  rw [← subrank_eq_abstract hk S, ← subrank_eq_abstract hk T] at h
  exact_mod_cast h

/-- **`Restricts` is preserved by `kronPowNat`** (piece 1, power step).
`Restricts S T → Restricts (kronPowNat S n) (kronPowNat T n)`, by induction on `n`
using `Restricts.kron_congr` (`kronPowNat (·) (n+1) = kronPowNat (·) n ⊠ ·`). -/
theorem restricts_kronPowNat {F : Type u} [Field F] {k : ℕ}
    {dS dT : Fin k → ℕ+} {S : KTensor F dS} {T : KTensor F dT}
    (hST : Restricts S T) : ∀ n : ℕ,
      Restricts (kronPowNat S n) (kronPowNat T n)
  | 0 => hST
  | n + 1 => Restricts.kron_congr (restricts_kronPowNat hST n) hST

/-- **`asympSubrank` is monotone under `Restricts`** (piece 1, headline).
Each `sSup`-range term `subrank(S^{⊠(n+1)})^{1/(n+1)}` is `≤` the `T`-term by the base
case (`subrank_mono_restricts` on `restricts_kronPowNat`) and `rpow`-monotonicity; the
`T`-range is bounded above (`concrete_asympSubrankSet_bddAbove`), so `sSup` is monotone. -/
theorem asympSubrank_mono_restricts {F : Type u} [Field F] {k : ℕ} [NeZero k] (hk : 2 ≤ k)
    {dS dT : Fin k → ℕ+} {S : KTensor F dS} {T : KTensor F dT}
    (hST : Restricts S T) : asympSubrank S ≤ asympSubrank T := by
  classical
  unfold asympSubrank
  apply Real.sSup_le
  · rintro x ⟨n, rfl⟩
    have hmono : (subrank (kronPowNat S n) : ℝ) ≤ (subrank (kronPowNat T n) : ℝ) := by
      exact_mod_cast subrank_mono_restricts hk (restricts_kronPowNat hST n)
    have hterm :
        (subrank (kronPowNat S n) : ℝ) ^ ((1 : ℝ) / ((n : ℝ) + 1))
          ≤ (subrank (kronPowNat T n) : ℝ) ^ ((1 : ℝ) / ((n : ℝ) + 1)) := by
      apply Real.rpow_le_rpow (by positivity) hmono
      positivity
    refine le_trans hterm ?_
    exact le_csSup (concrete_asympSubrankSet_bddAbove hk T) ⟨n, rfl⟩
  · exact asympSubrank_nonneg' hk T

/-! ## The `pairUnitKronQ → kronPowNat` restriction (tex:983-985).

For `q = subrankPair T`, the weighted pair-unit Kronecker product
`pairUnitKronQ F q = ⊠_{i<j} ⟨subrankPair T i j⟩_{i,j}` restricts to `T^{⊠ k(k-1)/2}`.
In the Lean `kronPowNat` convention `kronPowNat T n = T^{⊠(n+1)}`, this is
`kronPowNat T ((cgPairsList k).length - 1)`, and `(cgPairsList k).length = k(k-1)/2`.
This is exactly the paper's ingredient 1 at tex:984-985. -/

/-- **`(cgPairsList k).length = k(k-1)/2`** (the number of ordered pairs `i < j`). -/
theorem cgPairsList_length {k : ℕ} :
    (cgPairsList k).length = k * (k - 1) / 2 := by
  classical
  unfold cgPairsList
  rw [Finset.length_toList]
  -- the `i < j` pairs and the `j < i` pairs have equal cardinality (swap bijection),
  -- and together with the `k` diagonal pairs they partition `Fin k × Fin k` (`k²`).
  set Lt : Finset (Fin k × Fin k) := Finset.univ.filter (fun p => p.1 < p.2) with hLt
  set Gt : Finset (Fin k × Fin k) := Finset.univ.filter (fun p => p.2 < p.1) with hGt
  set Eq' : Finset (Fin k × Fin k) := Finset.univ.filter (fun p => p.1 = p.2) with hEq
  have hcard_eq : Lt.card = Gt.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro a ha
      rw [hGt, Finset.mem_filter]
      rw [hLt, Finset.mem_filter] at ha
      exact ⟨Finset.mem_univ _, ha.2⟩
    · intro a ha b hb h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1
    · intro b hb
      rw [hGt, Finset.mem_filter] at hb
      exact ⟨(b.2, b.1), by rw [hLt, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hb.2⟩, by simp⟩
  -- The diagonal `{p | p.1 = p.2}` has card `k`.
  have hdiag : Eq'.card = k := by
    have hbij : Eq'.card = (Finset.univ : Finset (Fin k)).card := by
      refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
      · intro a _; exact Finset.mem_univ _
      · intro a ha b hb h
        rw [hEq, Finset.mem_filter] at ha hb
        have ha2 : a.1 = a.2 := ha.2
        have hb2 : b.1 = b.2 := hb.2
        exact Prod.ext h (by rw [← ha2, ← hb2]; exact h)
      · intro b _
        exact ⟨(b, b), by rw [hEq, Finset.mem_filter]; exact ⟨Finset.mem_univ _, rfl⟩, rfl⟩
    rw [hbij, Finset.card_univ, Fintype.card_fin]
  -- The three filters partition `univ` and sum to `k²`.
  have hk2 : (Finset.univ : Finset (Fin k × Fin k)).card = k * k := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  -- `Lt`, `Gt`, `Eq'` are pairwise disjoint and their union is `univ`.
  have hdisj_LtGt : Disjoint Lt Gt := by
    rw [Finset.disjoint_left]
    intro p hpL hpG
    rw [hLt, Finset.mem_filter] at hpL
    rw [hGt, Finset.mem_filter] at hpG
    omega
  have hdisj_un_Eq : Disjoint (Lt ∪ Gt) Eq' := by
    rw [Finset.disjoint_left]
    intro p hpU hpE
    rw [hEq, Finset.mem_filter] at hpE
    rw [Finset.mem_union, hLt, hGt, Finset.mem_filter, Finset.mem_filter] at hpU
    rcases hpU with h | h <;> omega
  have hunion : Lt ∪ Gt ∪ Eq' = (Finset.univ : Finset (Fin k × Fin k)) := by
    apply Finset.eq_univ_of_forall
    intro p
    rw [Finset.mem_union, Finset.mem_union, hLt, hGt, hEq,
      Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · exact Or.inl (Or.inl ⟨Finset.mem_univ _, h⟩)
    · exact Or.inr ⟨Finset.mem_univ _, h⟩
    · exact Or.inl (Or.inr ⟨Finset.mem_univ _, h⟩)
  have htotal : Lt.card + Gt.card + Eq'.card = k * k := by
    rw [← hk2, ← hunion, Finset.card_union_of_disjoint hdisj_un_Eq,
      Finset.card_union_of_disjoint hdisj_LtGt]
  rw [hdiag] at htotal
  rw [← hcard_eq] at htotal
  -- `2 * Lt.card + k = k²`, so `Lt.card = (k² - k)/2 = k(k-1)/2`.
  have hkk : k * k = k * (k - 1) + k := by
    cases k with
    | zero => rfl
    | succ n => rw [Nat.succ_sub_one]; ring
  omega

/-- **Restriction preserves nonzeroness**: if `S ≤ₜ T` and `mk S ≠ 0` then `mk T ≠ 0`.
If `T = 0` (all entries `0`), the restriction formula gives `S jdx = ∑ … · 0 = 0`, so
`S = 0`, contradicting `mk S ≠ 0`. -/
theorem mk_ne_zero_of_restricts {F : Type u} [Field F] {k : ℕ} [NeZero k]
    {dS dT : Fin k → ℕ+} {S : KTensor F dS} {T : KTensor F dT}
    (hres : Restricts S T) (hS : TensorClass.mk ⟨dS, S⟩ ≠ (0 : TensorClass F k)) :
    TensorClass.mk ⟨dT, T⟩ ≠ (0 : TensorClass F k) := by
  classical
  intro h0
  -- `mk T = 0 ⟹ T = 0` (as a function: all entries vanish).
  have hTequiv : T ∼ₜ (zeroT : KTensor F (fun _ => (1 : ℕ+))) :=
    Quotient.exact (h0.trans TensorClass.zero_def)
  -- Extract the leg-matrices of the restriction `S ≤ₜ T`.
  obtain ⟨A, hA⟩ := hres
  -- Extract the restriction `T ≤ₜ zeroT`: gives `T idx = ∑ … · zeroT … = 0`.
  obtain ⟨B, hB⟩ := hTequiv.1
  -- Every entry of `T` is `0`.
  have hTzero : ∀ idx, T idx = 0 := by
    intro idx
    rw [hB idx]
    apply Finset.sum_eq_zero
    intro z _
    -- `zeroT z = 0`.
    simp [zeroT]
  -- Hence every entry of `S` is `0`, so `mk S = 0`.
  apply hS
  have hSzero : ∀ jdx, S jdx = 0 := by
    intro jdx
    rw [hA jdx]
    apply Finset.sum_eq_zero
    intro idx _
    rw [hTzero idx, mul_zero]
  -- `S = 0` as a tensor, so `mk S = mk zeroT = 0`.
  have hSeq : S = (0 : KTensor F dS) := by funext jdx; exact hSzero jdx
  rw [hSeq, TensorClass.zero_def]
  exact Quotient.sound (zeroT_equiv_zero (F := F) (d := dS)).symm

/-- **A positive `subrankPair` forces `T ≠ 0`** (Fekete precondition for the
power law).  The rank-`subrankPair` pair-unit is nonzero (its diagonal entry is `1`)
and restricts to `T` (`subrankPair_unitPair_restricts`), so `T ≠ 0`
(`mk_ne_zero_of_restricts`). -/
theorem mk_ne_zero_of_subrankPair_pos {F : Type u} [Field F] {k : ℕ} [NeZero k]
    {d : Fin k → ℕ+} (T : KTensor F d) {i j : Fin k} (hij : i ≠ j)
    (hp : 0 < subrankPair T i j) :
    TensorClass.mk ⟨d, T⟩ ≠ (0 : TensorClass F k) := by
  classical
  have hres := subrankPair_unitPair_restricts T i j hij hp
  set S : KTensor F _ := unitPairTensor (F := F) ⟨subrankPair T i j, hp⟩ i j hij with hS
  have hSne : TensorClass.mk ⟨_, S⟩ ≠ (0 : TensorClass F k) := by
    refine mk_ne_zero_of_entry S (idx := fun _ => ⟨0, by positivity⟩) ?_
    rw [hS, unitPairTensor]
    simp only [if_pos]
    norm_num
  exact mk_ne_zero_of_restricts hres hSne

/-- **`pairUnitKronQ` restricts to `kronPowNat T`** for `q = subrankPair T`
(tex:983-985, ingredient 1).  Each pair-unit `⟨subrankPair T i j⟩_{i,j}` restricts
to `T` (`subrankPair_unitPair_restricts`); folding these (`Restricts.kronFoldl`) and
absorbing the rank-`1` base unit (`one_kron`) gives `pairUnitKronQ ≤ₜ T^{⊠ N}` where
`N = (cgPairsList k).length`, i.e. `kronPowNat T (N - 1)`.

Requires `0 < subrankPair T i j` for every pair `i < j` (`hpos`) — exactly the
`1 ≤ q i j` hypothesis of `weightedVC`. -/
theorem pairUnitKronQ_subrankPair_restricts_kronPow {F : Type u} [Field F] {k : ℕ}
    {d : Fin k → ℕ+} (T : KTensor F d) (hk : 2 ≤ k)
    (hpos : ∀ i j : Fin k, i ≠ j → 0 < subrankPair T i j) :
    TTRestricts (pairUnitKronQ F (fun i j => subrankPair T i j))
      (TT.of (kronPowNat T ((cgPairsList k).length - 1))) := by
  classical
  -- The list of pairs is nonempty (`k ≥ 2`), so write it `p₀ :: ps`.
  have hlen : 1 ≤ (cgPairsList k).length := by
    rw [cgPairsList_length]
    have hge : 2 ≤ k * (k - 1) := by
      have h1 : 1 ≤ k - 1 := by omega
      calc 2 = 2 * 1 := by ring
        _ ≤ k * (k - 1) := Nat.mul_le_mul hk h1
    omega
  -- Each pair `p` in the list has `p.1 < p.2`, hence `p.1 ≠ p.2`.
  have hmem : ∀ p ∈ cgPairsList k, p.1 < p.2 := by
    intro p hp
    unfold cgPairsList at hp
    rw [Finset.mem_toList, Finset.mem_filter] at hp
    exact hp.2
  -- Each factor `pairUnitTT (subrankPair T p.1 p.2) p` restricts to `T`.
  have hfactor : ∀ p ∈ cgPairsList k,
      TTRestricts (pairUnitTT (F := F) (subrankPair T p.1 p.2) p) (TT.of T) := by
    intro p hp
    have hlt := hmem p hp
    have hne : p.1 ≠ p.2 := ne_of_lt hlt
    have hp0 : 0 < subrankPair T p.1 p.2 := hpos p.1 p.2 hne
    -- `pairUnitTT` takes the non-junk branch here.
    have hbranch : pairUnitTT (F := F) (subrankPair T p.1 p.2) p
        = TT.of (unitPairTensor (F := F) ⟨subrankPair T p.1 p.2, hp0⟩ p.1 p.2 hne) := by
      unfold pairUnitTT
      rw [dif_pos ⟨hne, hp0⟩]
    rw [hbranch]
    exact subrankPair_unitPair_restricts T p.1 p.2 hne hp0
  -- The base unit restricts to itself.
  have hbase : TTRestricts (TT.of (unitTensor F (k := k) (1 : ℕ+)))
      (TT.of (unitTensor F (k := k) (1 : ℕ+))) := Restricts.refl _
  -- Pointwise restriction list: each `pairUnitTT (q p) p ≤ₜ T`.
  have hforall : List.Forall₂ TTRestricts
      ((cgPairsList k).map (fun p => pairUnitTT (F := F) (subrankPair T p.1 p.2) p))
      (List.replicate (cgPairsList k).length (TT.of T)) := by
    rw [← List.map_const' (l := cgPairsList k) (b := TT.of T)]
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr ?_
    intro p hp
    exact hfactor p hp
  -- Fold the restrictions: `pairUnitKronQ ≤ₜ kronFoldl (unit 1) (replicate N T)`.
  have hfold : TTRestricts (pairUnitKronQ F (fun i j => subrankPair T i j))
      (kronFoldl (TT.of (unitTensor F (k := k) (1 : ℕ+)))
        (List.replicate (cgPairsList k).length (TT.of T))) := by
    unfold pairUnitKronQ
    exact Restricts.kronFoldl hbase hforall
  -- `kronFoldl (unit 1) (replicate N T) ∼ₜ kronPowNat T (N - 1)`.
  -- Peel: `replicate N T = T :: replicate (N-1) T` (N ≥ 1).
  obtain ⟨N', hN'⟩ : ∃ N', (cgPairsList k).length = N' + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hlen).symm⟩
  have hpeel : kronFoldl (TT.of (unitTensor F (k := k) (1 : ℕ+)))
      (List.replicate (cgPairsList k).length (TT.of T))
      = kronFoldl ((TT.of (unitTensor F (k := k) (1 : ℕ+))).kron (TT.of T))
          (List.replicate N' (TT.of T)) := by
    rw [hN', List.replicate_succ, kronFoldl_cons]
  -- `(unit 1) ⊠ T ∼ₜ T`, so the fold base restricts to `TT.of T` (one direction).
  have hbase_le : TTRestricts ((TT.of (unitTensor F (k := k) (1 : ℕ+))).kron (TT.of T))
      (TT.of T) := (one_kron T).1
  -- Congruence of `kronFoldl` under `≤ₜ` on the base (tail fixed by refl).
  have hfold_le : TTRestricts
      (kronFoldl ((TT.of (unitTensor F (k := k) (1 : ℕ+))).kron (TT.of T))
        (List.replicate N' (TT.of T)))
      (kronFoldl (TT.of T) (List.replicate N' (TT.of T))) := by
    have hrefl : List.Forall₂ TTRestricts
        (List.replicate N' (TT.of T)) (List.replicate N' (TT.of T)) :=
      List.forall₂_same.mpr (fun x _ => Restricts.refl x.2)
    exact Restricts.kronFoldl hbase_le hrefl
  -- `kronFoldl (TT.of T) (replicate N' T) = TT.of (kronPowNat T N')`, `N' = N - 1`.
  have hpow : kronFoldl (TT.of T) (List.replicate N' (TT.of T))
      = TT.of (kronPowNat T N') := (kronPowNat_eq_foldl T N').symm
  have hN'_eq : N' = (cgPairsList k).length - 1 := by omega
  -- Assemble: `pairUnitKronQ ≤ₜ ... ∼ₜ TT.of (kronPowNat T (N-1))`.
  have hchain : TTRestricts (pairUnitKronQ F (fun i j => subrankPair T i j))
      (TT.of (kronPowNat T N')) := by
    have h1 : TTRestricts (pairUnitKronQ F (fun i j => subrankPair T i j))
        (kronFoldl ((TT.of (unitTensor F (k := k) (1 : ℕ+))).kron (TT.of T))
          (List.replicate N' (TT.of T))) := by
      rw [← hpeel]; exact hfold
    have h2 : TTRestricts
        (kronFoldl ((TT.of (unitTensor F (k := k) (1 : ℕ+))).kron (TT.of T))
          (List.replicate N' (TT.of T)))
        (TT.of (kronPowNat T N')) := by
      rw [← hpow]; exact hfold_le
    exact Restricts.trans h1 h2
  rw [hN'_eq] at hchain
  exact hchain

/-! ## The dyadic weight `2^a` and `2^mLambda = minCut(2^a)`.

For multiplicities `a : cgEdge k → ℕ+`, the dyadic weight `dyadicWeight a i j := 2^(a{i,j})`
(junk `1` off-diagonal `i = j`) satisfies `cutProduct (dyadicWeight a) I = 2^(mCutWeight a I)`
(the ordered cross-pairs `(i,j)` of `I` biject with the crossing edges `{i,j}`), hence
`minCut (dyadicWeight a) = 2^(mLambda a)`. -/

/-- The dyadic weight `2^(a{i,j})` (with `1` on the diagonal). -/
noncomputable def dyadicWeight {k : ℕ} (a : cgEdge k → ℕ) : Fin k → Fin k → ℕ :=
  fun i j => if h : i ≠ j then 2 ^ ((a (edgeOf i j h) : ℕ)) else 1

/-- An ordered cross-pair `(i,j)` of `I` (`i ∈ I, j ∉ I`) has `i ≠ j`. -/
theorem mem_cross_ne {k : ℕ} {I : Finset (Fin k)} {p : Fin k × Fin k}
    (hp : p ∈ I ×ˢ (Finset.univ \ I)) : p.1 ≠ p.2 := by
  rw [Finset.mem_product, Finset.mem_sdiff] at hp
  intro h; rw [h] at hp; exact hp.2.2 hp.1

/-- The edge `{i,j}` of a cross-pair `(i,j)` crosses `I`. -/
theorem mem_cross_edgeOf_crosses {k : ℕ} {I : Finset (Fin k)} {p : Fin k × Fin k}
    (hp : p ∈ I ×ˢ (Finset.univ \ I)) :
    crosses I (edgeOf p.1 p.2 (mem_cross_ne hp)) := by
  rw [Finset.mem_product, Finset.mem_sdiff] at hp
  refine ⟨⟨p.1, ?_⟩, ⟨p.2, ?_⟩⟩
  · rw [Finset.mem_inter]; exact ⟨by rw [mem_edgeOf]; exact Or.inl rfl, hp.1⟩
  · rw [Finset.mem_sdiff]; exact ⟨by rw [mem_edgeOf]; exact Or.inr rfl, hp.2.2⟩

/-- The map `(i,j) ↦ {i,j}` is injective on cross-pairs of `I`: the `I`-endpoint and the
non-`I`-endpoint are uniquely determined. -/
theorem mem_cross_edgeOf_inj {k : ℕ} {I : Finset (Fin k)} {p p' : Fin k × Fin k}
    (hp : p ∈ I ×ˢ (Finset.univ \ I)) (hp' : p' ∈ I ×ˢ (Finset.univ \ I))
    (he : edgeOf p.1 p.2 (mem_cross_ne hp) = edgeOf p'.1 p'.2 (mem_cross_ne hp')) :
    p = p' := by
  rw [Finset.mem_product, Finset.mem_sdiff] at hp hp'
  have hval : ({p.1, p.2} : Finset (Fin k)) = ({p'.1, p'.2} : Finset (Fin k)) := by
    have := Subtype.ext_iff.mp he
    simpa [edgeOf] using this
  have h1mem : p.1 ∈ ({p'.1, p'.2} : Finset (Fin k)) := by rw [← hval]; simp
  have h2mem : p.2 ∈ ({p'.1, p'.2} : Finset (Fin k)) := by rw [← hval]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1mem h2mem
  have h11 : p.1 = p'.1 := by
    rcases h1mem with h | h
    · exact h
    · exact absurd (h ▸ hp.1) hp'.2.2
  have h22 : p.2 = p'.2 := by
    rcases h2mem with h | h
    · exact absurd (h ▸ hp'.1) hp.2.2
    · exact h
  exact Prod.ext h11 h22

/-- Every crossing edge `e` of `I` is `{i,j}` for a (unique) cross-pair `(i,j)`:
its `I`-endpoint and its non-`I`-endpoint. -/
theorem crosses_exists_cross_pair {k : ℕ} {I : Finset (Fin k)} {e : cgEdge k}
    (he : crosses I e) :
    ∃ p, ∃ hp : p ∈ I ×ˢ (Finset.univ \ I), edgeOf p.1 p.2 (mem_cross_ne hp) = e := by
  classical
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := he
  rw [Finset.mem_inter] at hi
  rw [Finset.mem_sdiff] at hj
  have hij : i ≠ j := fun h => hj.2 (h ▸ hi.2)
  have hmem : (i, j) ∈ I ×ˢ (Finset.univ \ I) := by
    rw [Finset.mem_product, Finset.mem_sdiff]
    exact ⟨hi.2, Finset.mem_univ _, hj.2⟩
  refine ⟨(i, j), hmem, ?_⟩
  apply Subtype.ext
  change ({i, j} : Finset (Fin k)) = e.val
  have hsub : ({i, j} : Finset (Fin k)) ⊆ e.val := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hi.1
    · exact hj.1
  have hcard2 : ({i, j} : Finset (Fin k)).card = 2 := Finset.card_pair hij
  exact Finset.eq_of_subset_of_card_le hsub (by rw [e.2, hcard2])

/-- `cutProduct (dyadicWeight a) I = 2 ^ (mCutWeight a I)`: the ordered cross-pairs
`(i,j)` of `I` (`i ∈ I, j ∉ I`) biject with the crossing edges `{i,j}` via `(i,j) ↦ {i,j}`,
turning the product of `2^(a·)` into `2^(∑ a·) = 2^(mCutWeight a I)`. -/
theorem cutProduct_dyadicWeight {k : ℕ} (a : cgEdge k → ℕ) (I : Finset (Fin k)) :
    MinCut.cutProduct (dyadicWeight a) I = 2 ^ (mCutWeight a I) := by
  classical
  unfold MinCut.cutProduct mCutWeight
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_bij (fun p hp => edgeOf p.1 p.2 (mem_cross_ne hp)) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, mem_cross_edgeOf_crosses hp⟩
  · intro p hp p' hp' he
    exact mem_cross_edgeOf_inj hp hp' he
  · intro e he
    rw [Finset.mem_filter] at he
    exact crosses_exists_cross_pair he.2
  · intro p hp
    change dyadicWeight a p.1 p.2 = 2 ^ ((a (edgeOf p.1 p.2 (mem_cross_ne hp)) : ℕ))
    rw [dyadicWeight, dif_pos (mem_cross_ne hp)]

/-- **`2^(mLambda a) = minCut (dyadicWeight a)`** (piece 4b): apply
`cutProduct_dyadicWeight` cut-by-cut and commute `2^·` with the `Finset.inf'`
(both `mLambda` and `minCut` are `inf'` over the same admissible cuts). -/
theorem two_pow_mLambda_eq_minCut_dyadicWeight {k : ℕ} (a : cgEdge k → ℕ) (hk : 2 ≤ k) :
    2 ^ (mLambda a hk) = MinCut.minCut (dyadicWeight a) hk := by
  classical
  unfold mLambda MinCut.minCut
  rw [Finset.comp_inf'_eq_inf'_comp (MinCut.admissibleCuts_nonempty hk)
        (g := fun n : ℕ => 2 ^ n)
        (fun x y => by
          rcases le_total x y with h | h
          · rw [min_eq_left h, min_eq_left (Nat.pow_le_pow_right (by norm_num) h)]
          · rw [min_eq_right h, min_eq_right (Nat.pow_le_pow_right (by norm_num) h)])]
  apply Finset.inf'_congr (MinCut.admissibleCuts_nonempty hk) rfl
  intro I hI
  exact (cutProduct_dyadicWeight a I).symm

/-- **Dyadic floor weight** for the weighted Vrana-Christandl washout
(semicontinuity tex:987-990).

For the `m`-th power of `q`, replace each entry by the largest dyadic power below it,
but keep entries `0` and `1` at weight `1`.  On the off-diagonal hypotheses used in
Corollary 3.5 this means exactly that rank-`1` pair-units are omitted from the
multigraph approximation, as in the dyadic-floor argument around tex:987-990. -/
noncomputable def dyadicFloorWeight {k : ℕ} (q : Fin k → Fin k → ℕ) (m : ℕ) :
    Fin k → Fin k → ℕ :=
  fun i j => if q i j ≤ 1 then 1 else 2 ^ Nat.log 2 ((q i j) ^ m)

/-- **Per-edge dyadic loss** (semicontinuity tex:987-990).

Every powered weight is at most twice its dyadic floor.  The proof uses
`Nat.lt_pow_succ_log_self`; entries `≤ 1` are handled by the explicit `1` branch of
`dyadicFloorWeight`. -/
theorem dyadicFloorWeight_loss {k : ℕ} (q : Fin k → Fin k → ℕ) {m : ℕ} (hm : 1 ≤ m) :
    ∀ i j, (q i j) ^ m ≤ 2 * dyadicFloorWeight q m i j := by
  intro i j
  unfold dyadicFloorWeight
  by_cases hsmall : q i j ≤ 1
  · rw [if_pos hsmall]
    have h01 : q i j = 0 ∨ q i j = 1 := by omega
    rcases h01 with h0 | h1
    · rw [h0]
      cases m with
      | zero => omega
      | succ m => simp
    · simp [h1]
  · rw [if_neg hsmall]
    have hxlt :
        (q i j) ^ m < 2 ^ (Nat.log 2 ((q i j) ^ m) + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ((q i j) ^ m)
    calc
      (q i j) ^ m ≤ 2 ^ (Nat.log 2 ((q i j) ^ m) + 1) := Nat.le_of_lt hxlt
      _ = 2 * 2 ^ Nat.log 2 ((q i j) ^ m) := by
        rw [pow_succ]
        ring

/-- A `cgEdge k` (a 2-element subset) decomposed into an ordered pair of its endpoints. -/
noncomputable def edgeEndpts {k : ℕ} (e : cgEdge k) : Fin k × Fin k :=
  ((Finset.card_eq_two.mp e.2).choose,
   (Finset.card_eq_two.mp e.2).choose_spec.choose)

theorem edgeEndpts_spec {k : ℕ} (e : cgEdge k) :
    (edgeEndpts e).1 ≠ (edgeEndpts e).2 ∧
      e.val = ({(edgeEndpts e).1, (edgeEndpts e).2} : Finset (Fin k)) := by
  have h := (Finset.card_eq_two.mp e.2).choose_spec.choose_spec
  exact h

/-- **The dyadic-floor multigraph** `aFloor q m : cgEdge k → ℕ` (genmamu:232).

The multiplicity of the pair `e = {i,j}` is the dyadic exponent `Nat.log 2` of the
dyadic floor weight `dyadicFloorWeight q m i j`.  Since `dyadicFloorWeight` is always a
power of two (`1 = 2^0` on the `q ≤ 1` branch, `2^(log₂(q^m))` otherwise), this recovers
exactly that exponent, and pairs with `q i j = 1` (exponent `0`) are absent from the
multigraph `H_{aFloor}` (`Fin 0` empty), matching genmamu's incomplete-`H` /
weighted-edges picture (tex:105-109, 232). -/
noncomputable def aFloor {k : ℕ} (q : Fin k → Fin k → ℕ) (m : ℕ) : cgEdge k → ℕ :=
  fun e => Nat.log 2 (dyadicFloorWeight q m (edgeEndpts e).1 (edgeEndpts e).2)

theorem dyadicFloorWeight_isPow {k : ℕ} (q : Fin k → Fin k → ℕ) (m : ℕ) (i j : Fin k) :
    2 ^ Nat.log 2 (dyadicFloorWeight q m i j) = dyadicFloorWeight q m i j := by
  unfold dyadicFloorWeight
  by_cases hsmall : q i j ≤ 1
  · rw [if_pos hsmall]; simp
  · rw [if_neg hsmall]
    rw [Nat.log_pow (by norm_num : 1 < 2)]

/-- **`dyadicWeight (aFloor q m) = dyadicFloorWeight q m`** off-diagonal (genmamu:232).

`dyadicWeight a i j = 2^(a {i,j})` and `aFloor q m {i,j} = log₂(dyadicFloorWeight q m i j)`;
since `dyadicFloorWeight` is a power of two and (under `hsym`) symmetric in `i,j`, the two
agree off-diagonal; on the diagonal `dyadicWeight = 1 = dyadicFloorWeight` (`q i i`-branch
is `1` when `q i i ≤ 1`, and the diagonal is never used in cut products). -/
theorem dyadicWeight_aFloor_eq {k : ℕ} (q : Fin k → Fin k → ℕ) (m : ℕ)
    (hsym : ∀ i j, q i j = q j i) (hk : 2 ≤ k) :
    MinCut.minCut (dyadicWeight (aFloor q m)) hk = MinCut.minCut (dyadicFloorWeight q m) hk := by
  classical
  -- Both `minCut`s are `inf'` of cut products over admissible cuts; show the cut products
  -- agree.  The cut product only multiplies off-diagonal `(i,j)` with `i ≠ j`.
  unfold MinCut.minCut
  apply Finset.inf'_congr (MinCut.admissibleCuts_nonempty hk) rfl
  intro I hI
  unfold MinCut.cutProduct
  apply Finset.prod_congr rfl
  intro p hp
  rw [Finset.mem_product, Finset.mem_sdiff] at hp
  have hne : p.1 ≠ p.2 := by intro h; rw [h] at hp; exact hp.2.2 hp.1
  -- `dyadicWeight (aFloor) p.1 p.2 = 2^(aFloor {p.1,p.2}) = 2^(log₂ dyadicFloorWeight) =
  -- dyadicFloorWeight`.
  rw [dyadicWeight, dif_pos hne]
  -- `aFloor (edgeOf p.1 p.2 hne) = log₂ (dyadicFloorWeight q m a b)` for the (unordered) endpoints.
  unfold aFloor
  -- The endpoints of `edgeOf p.1 p.2` form the set `{p.1,p.2}`; under `hsym`, `dyadicFloorWeight`
  -- is symmetric, so it equals `dyadicFloorWeight q m p.1 p.2` regardless of endpoint order.
  set ab := edgeEndpts (edgeOf p.1 p.2 hne) with hab
  have hset : ({ab.1, ab.2} : Finset (Fin k)) = ({p.1, p.2} : Finset (Fin k)) := by
    have heq' := (edgeEndpts_spec (edgeOf p.1 p.2 hne)).2
    have hval : (edgeOf p.1 p.2 hne).val = ({p.1, p.2} : Finset (Fin k)) := by
      unfold edgeOf; rfl
    rw [hab, ← heq', hval]
  -- From equal 2-element sets `{ab.1,ab.2} = {p.1,p.2}`, the dyadic floor weights agree (using
  -- hsym).
  have hdfw : dyadicFloorWeight q m ab.1 ab.2 = dyadicFloorWeight q m p.1 p.2 := by
    have hdfsym : ∀ x y, dyadicFloorWeight q m x y = dyadicFloorWeight q m y x := by
      intro x y; unfold dyadicFloorWeight; rw [hsym x y]
    -- `{ab.1,ab.2} = {p.1,p.2}` ⟹ either ab=(p.1,p.2) or ab=(p.2,p.1).
    have hab1 : ab.1 ∈ ({p.1, p.2} : Finset (Fin k)) := by
      rw [← hset]; exact Finset.mem_insert_self _ _
    have hab2 : ab.2 ∈ ({p.1, p.2} : Finset (Fin k)) := by
      rw [← hset]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have habne : ab.1 ≠ ab.2 := (edgeEndpts_spec (edgeOf p.1 p.2 hne)).1
    rw [Finset.mem_insert, Finset.mem_singleton] at hab1 hab2
    rcases hab1 with h1 | h1 <;> rcases hab2 with h2 | h2
    · exact absurd (h1.trans h2.symm) habne
    · rw [h1, h2]
    · rw [h1, h2]; exact hdfsym p.2 p.1
    · exact absurd (h1.trans h2.symm) habne
  rw [hdfw, dyadicFloorWeight_isPow]

private lemma unitTensor_one_kronPowNat_equiv {F : Type u} [Field F] {k : ℕ} (n : ℕ) :
    (unitTensor F (k := k) (1 : ℕ+)) ∼ₜ
      kronPowNat (unitTensor F (k := k) (1 : ℕ+)) n := by
  classical
  induction n with
  | zero =>
      exact RestrictsEquiv.refl _
  | succ n ih =>
      have hbase :
          (unitTensor F (k := k) (1 : ℕ+) ⊠ unitTensor F (k := k) (1 : ℕ+))
            ∼ₜ (kronPowNat (unitTensor F (k := k) (1 : ℕ+)) n ⊠
                unitTensor F (k := k) (1 : ℕ+)) :=
        RestrictsEquiv.kron_congr ih (RestrictsEquiv.refl _)
      exact ((one_kron (unitTensor F (k := k) (1 : ℕ+))).symm.trans hbase)

private lemma unitPairTensor_pow_equiv_kronPowNat {F : Type u} [Field F] {k : ℕ}
    (i j : Fin k) (hij : i ≠ j) (r : ℕ) (hr : 1 ≤ r) (m : ℕ) (hm : 1 ≤ m) :
    unitPairTensor (F := F) ⟨r ^ m, Nat.one_le_pow m r hr⟩ i j hij
      ∼ₜ kronPowNat (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) (m - 1) := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  clear hm
  induction n with
  | zero =>
      convert RestrictsEquiv.refl (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) using 2
      · simp
      · simp
  | succ n ih =>
      have hpow_pos : 1 ≤ r ^ (n + 1) := Nat.one_le_pow (n + 1) r hr
      have hmul_pos : 1 ≤ r ^ (n + 1) * r := Nat.mul_pos
        (by exact_mod_cast hpow_pos) (by exact_mod_cast hr)
      have hsplit :
          unitPairTensor (F := F) ⟨r ^ (n + 2), Nat.one_le_pow (n + 2) r hr⟩ i j hij
            ∼ₜ
          (unitPairTensor (F := F) ⟨r ^ (n + 1), hpow_pos⟩ i j hij ⊠
            unitPairTensor (F := F) ⟨r, hr⟩ i j hij) := by
        have hmul : r ^ (n + 2) = r ^ (n + 1) * r := by
          rw [pow_succ]
        simpa [hmul] using unitPairTensor_kron_equiv (F := F) i j hij
          ⟨r ^ (n + 1), hpow_pos⟩ ⟨r, hr⟩
      have hcongr :
          (unitPairTensor (F := F) ⟨r ^ (n + 1), hpow_pos⟩ i j hij ⊠
              unitPairTensor (F := F) ⟨r, hr⟩ i j hij)
            ∼ₜ
          (kronPowNat (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) n ⊠
              unitPairTensor (F := F) ⟨r, hr⟩ i j hij) :=
        RestrictsEquiv.kron_congr ih (RestrictsEquiv.refl _)
      simpa [kronPowNat] using hsplit.trans hcongr

/-! ### Multigraph GHZ assembly for dyadic edge multiplicities.

These private helpers mirror the simple-graph partial-edge assembly in `UniformVC`
(genmamu tex:124-159, 232), with `ec.1 ∈ S` selecting all parallel copies over
the pair `ec.1`. -/

/-- Incidence of the multigraph `H_a` restricted to pair set `S`: all copies over
    pairs in `S` are kept, and all other copies are ignored. -/
private def mIncOn {k : ℕ} (a : cgEdge k → ℕ) (S : Finset (cgEdge k)) :
    Fin k → mEdge a → Prop :=
  fun v ec => ec.1 ∈ S ∧ v ∈ ec.1.val

private instance mIncOn_decidable {k : ℕ} (a : cgEdge k → ℕ) (S : Finset (cgEdge k))
    (v : Fin k) (ec : mEdge a) : Decidable (mIncOn a S v ec) := by
  unfold mIncOn
  infer_instance

open VC.Degeneration in
/-- For disjoint pair sets `S,T`, local indices for `mIncOn a (S∪T)` split into
    the product of local indices for `S` and for `T` (genmamu tex:152-156). -/
private noncomputable def localIdxMUnionEquiv {k : ℕ} {a : cgEdge k → ℕ}
    {S T : Finset (cgEdge k)} (hST : Disjoint S T) (n : ℕ) (v : Fin k) :
    localIdx (mIncOn a (S ∪ T)) n v
      ≃ localIdx (mIncOn a S) n v × localIdx (mIncOn a T) n v := by
  classical
  have hpred : ∀ ec : mEdge a,
      mIncOn a (S ∪ T) v ec ↔ (mIncOn a S v ec ∨ mIncOn a T v ec) := by
    intro ec
    unfold mIncOn
    rw [Finset.mem_union]
    tauto
  have hdisj : Disjoint (mIncOn a S v) (mIncOn a T v) := by
    intro p hpS hpT ec hpec
    exact (Finset.disjoint_left.mp hST (hpS ec hpec).1) (hpT ec hpec).1
  let eSplit : {ec : mEdge a // mIncOn a (S ∪ T) v ec}
      ≃ {ec : mEdge a // mIncOn a S v ec} ⊕ {ec : mEdge a // mIncOn a T v ec} :=
    (Equiv.subtypeEquivRight hpred).trans (subtypeOrEquiv _ _ hdisj)
  exact (Equiv.arrowCongr eSplit (Equiv.refl (Fin n))).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

open VC.Degeneration in
/-- Global consistency for a disjoint union of multigraph pair sets factors as
    consistency on the two parts (genmamu tex:152-156). -/
private theorem ghzHTensor_mUnion_iff {k : ℕ} {a : cgEdge k → ℕ}
    {S T : Finset (cgEdge k)} (hST : Disjoint S T)
    (n : ℕ) (f : (v : Fin k) → localIdx (mIncOn a S) n v)
    (g : (v : Fin k) → localIdx (mIncOn a T) n v) :
    (∃ h : mEdge a → Fin n, ∀ v : Fin k, ∀ ec : {ec : mEdge a // mIncOn a (S ∪ T) v ec},
        (localIdxMUnionEquiv hST n v).symm (f v, g v) ec = h ec.1)
      ↔
    (∃ i : mEdge a → Fin n, ∀ v : Fin k, ∀ ec : {ec // mIncOn a S v ec}, f v ec = i ec.1) ∧
      (∃ j : mEdge a → Fin n, ∀ v : Fin k, ∀ ec : {ec // mIncOn a T v ec}, g v ec = j ec.1) := by
  classical
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨⟨h, ?_⟩, ⟨h, ?_⟩⟩
    · intro v ec
      have heU : mIncOn a (S ∪ T) v ec.1 := by
        exact ⟨Finset.mem_union_left _ ec.2.1, ec.2.2⟩
      have hsy := hh v ⟨ec.1, heU⟩
      rw [← hsy]
      simp only [localIdxMUnionEquiv, Equiv.symm_trans_apply, Equiv.arrowCongr_symm,
        Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.refl_apply, Function.comp_apply,
        Equiv.symm_symm]
      simp [subtypeOrEquiv, subtypeOrLeftEmbedding, Equiv.subtypeEquivRight, dif_pos ec.2]
    · intro v ec
      have heU : mIncOn a (S ∪ T) v ec.1 := by
        exact ⟨Finset.mem_union_right _ ec.2.1, ec.2.2⟩
      have hnotS : ¬ mIncOn a S v ec.1 := by
        intro hSe
        exact (Finset.disjoint_left.mp hST hSe.1) ec.2.1
      have hsy := hh v ⟨ec.1, heU⟩
      rw [← hsy]
      simp only [localIdxMUnionEquiv, Equiv.symm_trans_apply, Equiv.arrowCongr_symm,
        Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.refl_apply, Function.comp_apply,
        Equiv.symm_symm]
      simp [subtypeOrEquiv, subtypeOrLeftEmbedding, Equiv.subtypeEquivRight, dif_neg hnotS]
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    refine ⟨fun ec => if ec.1 ∈ S then i ec else j ec, ?_⟩
    intro v ec
    obtain ⟨heU, hv⟩ := ec.2
    by_cases hS : ec.1.1 ∈ S
    · have hf := hi v ⟨ec.1, ⟨hS, hv⟩⟩
      have hSi : mIncOn a S v ec.1 := ⟨hS, hv⟩
      simp only [hS, if_true]
      rw [← hf]
      simp only [localIdxMUnionEquiv, Equiv.symm_trans_apply, Equiv.arrowCongr_symm,
        Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.refl_apply, Function.comp_apply,
        Equiv.symm_symm]
      simp [subtypeOrEquiv, subtypeOrLeftEmbedding, Equiv.subtypeEquivRight, dif_pos hSi]
    · have hT : ec.1.1 ∈ T := by
        rcases Finset.mem_union.mp heU with h | h
        · exact absurd h hS
        · exact h
      have hnotS : ¬ mIncOn a S v ec.1 := fun hSe => hS hSe.1
      have hg := hj v ⟨ec.1, ⟨hT, hv⟩⟩
      simp only [hS, if_false]
      rw [← hg]
      simp only [localIdxMUnionEquiv, Equiv.symm_trans_apply, Equiv.arrowCongr_symm,
        Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.refl_apply, Function.comp_apply,
        Equiv.symm_symm]
      simp [subtypeOrEquiv, subtypeOrLeftEmbedding, Equiv.subtypeEquivRight, dif_neg hnotS]

open VC.Degeneration in
/-- Disjoint pair-set GHZ merge for multigraphs (genmamu tex:152-156). -/
private theorem ghzH_mDisjointUnion_equiv {F : Type u} [Field F] {k : ℕ}
    {a : cgEdge k → ℕ} {S T : Finset (cgEdge k)} (hST : Disjoint S T)
    {n : ℕ} (hn : 1 ≤ n) :
    (ghzH_asKTensor (F := F) (mIncOn a S) hn ⊠ ghzH_asKTensor (F := F) (mIncOn a T) hn)
      ∼ₜ ghzH_asKTensor (F := F) (mIncOn a (S ∪ T)) hn := by
  classical
  refine restrictsEquiv_of_forall_legEquiv ?e ?hval
  · intro v
    exact (kronDecodeEquiv.trans
      ((ghzHEquiv (mIncOn a S) hn v).symm.prodCongr (ghzHEquiv (mIncOn a T) hn v).symm)).trans
        ((localIdxMUnionEquiv hST n v).symm.trans (ghzHEquiv (mIncOn a (S ∪ T)) hn v))
  · intro idx
    unfold ghzH_asKTensor reindexKTensor
    rw [kron_apply]
    let f : (v : Fin k) → localIdx (mIncOn a S) n v :=
      fun v => (ghzHEquiv (mIncOn a S) hn v).symm (kronDecodeL (idx v))
    let g : (v : Fin k) → localIdx (mIncOn a T) n v :=
      fun v => (ghzHEquiv (mIncOn a T) hn v).symm (kronDecodeR (idx v))
    have harg : (fun v : Fin k =>
        (ghzHEquiv (mIncOn a (S ∪ T)) hn v).symm
          ((((kronDecodeEquiv.trans
            ((ghzHEquiv (mIncOn a S) hn v).symm.prodCongr (ghzHEquiv (mIncOn a T) hn v).symm)).trans
              ((localIdxMUnionEquiv hST n v).symm.trans (ghzHEquiv (mIncOn a (S ∪ T)) hn v)))
            (idx v)))) =
        fun v => (localIdxMUnionEquiv hST n v).symm (f v, g v) := by
      funext v
      simp only [Equiv.trans_apply, Equiv.prodCongr_apply, kronDecodeEquiv_apply]
      rw [Equiv.symm_apply_apply]
      rfl
    rw [harg]
    unfold ghzHTensor
    have hpiff := ghzHTensor_mUnion_iff hST n f g
    by_cases hp : ∃ i : mEdge a → Fin n,
        ∀ v : Fin k, ∀ ec : {ec // mIncOn a S v ec}, f v ec = i ec.1
    · by_cases hq : ∃ j : mEdge a → Fin n,
          ∀ v : Fin k, ∀ ec : {ec // mIncOn a T v ec}, g v ec = j ec.1
      · rw [if_pos hp, if_pos hq, if_pos (hpiff.mpr ⟨hp, hq⟩)]
        simp
      · rw [if_pos hp, if_neg hq]
        have hr : ¬ ∃ h : mEdge a → Fin n, ∀ v : Fin k,
            ∀ ec : {ec // mIncOn a (S ∪ T) v ec},
              (localIdxMUnionEquiv hST n v).symm (f v, g v) ec = h ec.1 :=
          fun hr => hq (hpiff.mp hr).2
        rw [if_neg hr]
        simp
    · have hr : ¬ ∃ h : mEdge a → Fin n, ∀ v : Fin k,
          ∀ ec : {ec // mIncOn a (S ∪ T) v ec},
            (localIdxMUnionEquiv hST n v).symm (f v, g v) ec = h ec.1 :=
        fun hr => hp (hpiff.mp hr).1
      rw [if_neg hp, if_neg hr]
      simp

open VC.Degeneration in
/-- Dropping the vacuous `ec.1 ∈ univ` conjunct identifies the full restricted
    multigraph GHZ with `ghzH (mInc a)` (genmamu tex:124-159, 232). -/
private theorem ghzH_mIncOn_univ_equiv_mInc {F : Type u} [Field F] {k : ℕ}
    (a : cgEdge k → ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ghzH_asKTensor (F := F) (mIncOn a (Finset.univ : Finset (cgEdge k))) hn
      ∼ₜ ghzH_asKTensor (F := F) (mInc a) hn := by
  classical
  let edgeDrop (v : Fin k) :
      {ec : mEdge a // mIncOn a (Finset.univ : Finset (cgEdge k)) v ec}
        ≃ {ec : mEdge a // mInc a v ec} :=
    Equiv.subtypeEquivRight (fun ec : mEdge a => by
      simp [mIncOn, mInc])
  let localDrop (v : Fin k) :
      localIdx (mIncOn a (Finset.univ : Finset (cgEdge k))) n v
        ≃ localIdx (mInc a) n v :=
    Equiv.arrowCongr (edgeDrop v) (Equiv.refl (Fin n))
  refine restrictsEquiv_of_forall_legEquiv ?e ?hval
  · intro v
    exact (ghzHEquiv (mIncOn a (Finset.univ : Finset (cgEdge k))) hn v).symm.trans
      ((localDrop v).trans (ghzHEquiv (mInc a) hn v))
  · intro idx
    unfold ghzH_asKTensor reindexKTensor ghzHTensor
    let fOn : (v : Fin k) → localIdx (mIncOn a (Finset.univ : Finset (cgEdge k))) n v :=
      fun v => (ghzHEquiv (mIncOn a (Finset.univ : Finset (cgEdge k))) hn v).symm (idx v)
    let f : (v : Fin k) → localIdx (mInc a) n v :=
      fun v => localDrop v (fOn v)
    have harg :
        (fun v : Fin k =>
          (ghzHEquiv (mInc a) hn v).symm
            (((ghzHEquiv (mIncOn a (Finset.univ : Finset (cgEdge k))) hn v).symm.trans
              ((localDrop v).trans (ghzHEquiv (mInc a) hn v))) (idx v))) = f := by
      funext v
      simp [f, fOn, localDrop]
    rw [harg]
    have hiff :
        (∃ i : mEdge a → Fin n,
          ∀ v : Fin k, ∀ ec : {ec : mEdge a // mIncOn a (Finset.univ : Finset (cgEdge k)) v ec},
            fOn v ec = i ec.1)
        ↔
        (∃ i : mEdge a → Fin n,
          ∀ v : Fin k, ∀ ec : {ec : mEdge a // mInc a v ec}, f v ec = i ec.1) := by
      constructor
      · rintro ⟨i, hi⟩
        refine ⟨i, ?_⟩
        intro v ec
        have heOn : mIncOn a (Finset.univ : Finset (cgEdge k)) v ec.1 := by
          exact ⟨Finset.mem_univ _, ec.2⟩
        simpa [f, localDrop, edgeDrop] using hi v ⟨ec.1, heOn⟩
      · rintro ⟨i, hi⟩
        refine ⟨i, ?_⟩
        intro v ec
        have he : mInc a v ec.1 := ec.2.2
        have := hi v ⟨ec.1, he⟩
        simpa [f, localDrop, edgeDrop] using this
    by_cases hOn :
        ∃ i : mEdge a → Fin n,
          ∀ v : Fin k, ∀ ec : {ec : mEdge a // mIncOn a (Finset.univ : Finset (cgEdge k)) v ec},
            fOn v ec = i ec.1
    · rw [if_pos hOn, if_pos (hiff.mp hOn)]
    · rw [if_neg hOn, if_neg (fun h => hOn (hiff.mpr h))]

/-- `Fin (2^m)` encoded as assignments of one rank-2 label to each of `m`
    parallel copies (genmamu tex:124-159, 232). -/
private noncomputable def finTwoPowEquiv (m : ℕ) : Fin (2 ^ m) ≃ (Fin m → Fin 2) := by
  classical
  have hcard : 2 ^ m = Fintype.card (Fin m → Fin 2) := by
    simp [Fintype.card_fin]
  exact (finCongr hcard).trans (Fintype.equivFin (Fin m → Fin 2)).symm

private lemma finTwoPowEquiv_inj {m : ℕ} {x y : Fin (2 ^ m)}
    (h : finTwoPowEquiv m x = finTwoPowEquiv m y) : x = y :=
  (finTwoPowEquiv m).injective h

private noncomputable def mIncOnSingletonCopiesEquiv {k : ℕ} (a : cgEdge k → ℕ)
    (e₀ : cgEdge k) (v : Fin k) (hv : v ∈ e₀.val) :
    {ec : mEdge a // mIncOn a ({e₀} : Finset (cgEdge k)) v ec} ≃ Fin (a e₀) where
  toFun ec := by
    have heq : ec.1.1 = e₀ := by
      exact Finset.mem_singleton.mp ec.2.1
    exact Fin.cast (congrArg a heq) ec.1.2
  invFun c := ⟨⟨e₀, c⟩, by simp [mIncOn, hv]⟩
  left_inv ec := by
    obtain ⟨⟨e, c⟩, hmem, hinc⟩ := ec
    dsimp
    have heq : e = e₀ := Finset.mem_singleton.mp hmem
    subst e
    simp
  right_inv c := by
    simp

private noncomputable def mSingleLocEquiv {k : ℕ} (a : cgEdge k → ℕ)
    (e₀ : cgEdge k) (i j v : Fin k) (hij : i ≠ j)
    (hmem : ∀ x : Fin k, x ∈ e₀.val ↔ x = i ∨ x = j) :
    localIdx (mIncOn a ({e₀} : Finset (cgEdge k))) 2 v
      ≃ Fin ((naturalPairFormat (⟨2 ^ a e₀, Nat.one_le_pow (a e₀) 2 (by norm_num)⟩ : ℕ+)
          i j v : ℕ+) : ℕ) := by
  classical
  by_cases hv : v ∈ e₀.val
  · have hfmt : ((naturalPairFormat
        (⟨2 ^ a e₀, Nat.one_le_pow (a e₀) 2 (by norm_num)⟩ : ℕ+) i j v : ℕ+) : ℕ)
        = 2 ^ a e₀ := by
      have hvij := (hmem v).mp hv
      simp [naturalPairFormat, hvij]
    exact ((Equiv.arrowCongr (mIncOnSingletonCopiesEquiv a e₀ v hv)
      (Equiv.refl (Fin 2))).trans (finTwoPowEquiv (a e₀)).symm).trans
        (finCongr hfmt.symm)
  · haveI : IsEmpty {ec : mEdge a // mIncOn a ({e₀} : Finset (cgEdge k)) v ec} :=
      ⟨fun ec => by
        have heq : ec.1.1 = e₀ := Finset.mem_singleton.mp ec.2.1
        exact hv (by simpa [heq] using ec.2.2)⟩
    have hfmt : ((naturalPairFormat
        (⟨2 ^ a e₀, Nat.one_le_pow (a e₀) 2 (by norm_num)⟩ : ℕ+) i j v : ℕ+) : ℕ)
        = 1 := by
      have hvij : ¬ (v = i ∨ v = j) := fun h => hv ((hmem v).mpr h)
      simp only [naturalPairFormat]
      rw [if_neg]
      · rfl
      · push_neg
        exact ⟨fun h => hvij (Or.inl h), fun h => hvij (Or.inr h)⟩
    haveI : Unique (Fin ((naturalPairFormat
        (⟨2 ^ a e₀, Nat.one_le_pow (a e₀) 2 (by norm_num)⟩ : ℕ+) i j v : ℕ+) : ℕ)) := by
      rw [hfmt]
      infer_instance
    exact Equiv.ofUnique _ _

open VC.Degeneration in
/-- One unordered pair with `a e₀` parallel rank-2 edges is the pair-unit of
    rank `2^(a e₀)` (genmamu tex:124-159, 232). -/
private theorem pairUnit_equiv_mIncOn_singleton {F : Type u} [Field F] {k : ℕ}
    (a : cgEdge k → ℕ) (i j : Fin k) (hij : i ≠ j) :
    unitPairTensor (F := F) ⟨2 ^ a (edgeOf i j hij),
        Nat.one_le_pow (a (edgeOf i j hij)) 2 (by norm_num)⟩ i j hij
      ∼ₜ ghzH_asKTensor (F := F)
        (mIncOn a ({edgeOf i j hij} : Finset (cgEdge k))) (by norm_num : (1 : ℕ) ≤ 2) := by
  classical
  set e₀ := edgeOf i j hij with he₀
  have hmem : ∀ x : Fin k, x ∈ e₀.val ↔ x = i ∨ x = j := by
    intro x
    rw [he₀]
    exact mem_edgeOf i j x hij
  let locEquiv : ∀ v : Fin k,
      localIdx (mIncOn a ({e₀} : Finset (cgEdge k))) 2 v
        ≃ Fin ((naturalPairFormat
          (⟨2 ^ a e₀, Nat.one_le_pow (a e₀) 2 (by norm_num)⟩ : ℕ+) i j v : ℕ+) : ℕ) :=
    fun v => mSingleLocEquiv a e₀ i j v hij hmem
  refine restrictsEquiv_of_forall_legEquiv
    (fun v => (locEquiv v).symm.trans
      (ghzHEquiv (mIncOn a ({e₀} : Finset (cgEdge k)))
        (by norm_num : (1 : ℕ) ≤ 2) v)) ?_
  intro idx
  unfold ghzH_asKTensor reindexKTensor unitPairTensor ghzHTensor
  have harg : (fun v : Fin k =>
      (ghzHEquiv (mIncOn a ({e₀} : Finset (cgEdge k))) (by norm_num : (1 : ℕ) ≤ 2) v).symm
        (((locEquiv v).symm.trans
          (ghzHEquiv (mIncOn a ({e₀} : Finset (cgEdge k)))
            (by norm_num : (1 : ℕ) ≤ 2) v)) (idx v)))
        = fun v => (locEquiv v).symm (idx v) := by
    funext v
    simp [Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [harg]
  set fLoc : (v : Fin k) → localIdx (mIncOn a ({e₀} : Finset (cgEdge k))) 2 v :=
    fun v => (locEquiv v).symm (idx v) with hfLoc
  have hii_mem : i ∈ e₀.val := (hmem i).mpr (Or.inl rfl)
  have hjj_mem : j ∈ e₀.val := (hmem j).mpr (Or.inr rfl)
  by_cases hag : (idx i).val = (idx j).val
  · rw [if_pos hag, if_pos]
    let leftCode : Fin (a e₀) → Fin 2 := finTwoPowEquiv (a e₀)
      (Fin.cast (by simp [naturalPairFormat]) (idx i))
    refine ⟨fun ec => if h : ec.1 = e₀ then leftCode (Fin.cast (congrArg a h) ec.2) else 0, ?_⟩
    intro w ec
    obtain ⟨⟨e, c⟩, hpair_mem, hvpair⟩ := ec
    dsimp at hpair_mem hvpair ⊢
    have hpair : e = e₀ := Finset.mem_singleton.mp hpair_mem
    have hv_endpoint : w = i ∨ w = j := (hmem w).mp (by simpa [hpair] using hvpair)
    rcases hv_endpoint with rfl | rfl
    · subst e
      simp [fLoc, locEquiv, mSingleLocEquiv, mIncOnSingletonCopiesEquiv, leftCode, hii_mem]
    · subst e
      have hidx : idx w = Fin.cast (by simp [naturalPairFormat]) (idx i) := by
        apply Fin.ext
        simp [hag.symm]
      change ((locEquiv w).symm (idx w)) ⟨⟨e₀, c⟩, by simp [mIncOn, hjj_mem]⟩ =
        (if h : e₀ = e₀ then leftCode (Fin.cast (congrArg a h) c) else 0)
      rw [hidx]
      simp [locEquiv, mSingleLocEquiv, mIncOnSingletonCopiesEquiv, leftCode, hjj_mem]
  · rw [if_neg hag, if_neg]
    rintro ⟨glob, hglob⟩
    have hfun : finTwoPowEquiv (a e₀) (Fin.cast (by simp [naturalPairFormat]) (idx i))
        = finTwoPowEquiv (a e₀) (Fin.cast (by simp [naturalPairFormat]) (idx j)) := by
      funext c
      have hi_inc : mIncOn a ({e₀} : Finset (cgEdge k)) i ⟨e₀, c⟩ := by
        simp [mIncOn, hii_mem]
      have hj_inc : mIncOn a ({e₀} : Finset (cgEdge k)) j ⟨e₀, c⟩ := by
        simp [mIncOn, hjj_mem]
      have hi := hglob i ⟨⟨e₀, c⟩, hi_inc⟩
      have hj := hglob j ⟨⟨e₀, c⟩, hj_inc⟩
      have hicode :
          finTwoPowEquiv (a e₀) (Fin.cast (by simp [naturalPairFormat]) (idx i)) c
            = fLoc i ⟨⟨e₀, c⟩, hi_inc⟩ := by
        simp [fLoc, locEquiv, mSingleLocEquiv, mIncOnSingletonCopiesEquiv, hii_mem]
      have hjcode :
          finTwoPowEquiv (a e₀) (Fin.cast (by simp [naturalPairFormat]) (idx j)) c
            = fLoc j ⟨⟨e₀, c⟩, hj_inc⟩ := by
        simp [fLoc, locEquiv, mSingleLocEquiv, mIncOnSingletonCopiesEquiv, hjj_mem]
      rw [hicode, hjcode, hi, hj]
    have heq := finTwoPowEquiv_inj hfun
    exact hag (by
      have := congrArg Fin.val heq
      simpa using this)

open VC.Degeneration in
private theorem ghzH_mIncOn_empty_equiv {F : Type u} [Field F] {k : ℕ}
    (a : cgEdge k → ℕ) (hk : 0 < k) {n : ℕ} (hn : 1 ≤ n) :
    ghzH_asKTensor (F := F) (mIncOn a (∅ : Finset (cgEdge k))) hn
      ∼ₜ unitTensor F (k := k) 1 := by
  classical
  haveI hempty : ∀ v : Fin k, IsEmpty {ec : mEdge a // mIncOn a (∅ : Finset (cgEdge k)) v ec} :=
    fun v => ⟨fun ec => by simpa [mIncOn] using ec.2.1⟩
  haveI huS : ∀ v : Fin k,
      Unique (Fin ((ghzHFormat (mIncOn a (∅ : Finset (cgEdge k))) hn v : ℕ+) : ℕ)) := fun v => by
    have : Fintype.card (localIdx (mIncOn a (∅ : Finset (cgEdge k))) n v) = 1 := by
      rw [Fintype.card_eq_one_iff]
      exact ⟨fun ec => (hempty v).elim ec, fun f => funext fun ec => (hempty v).elim ec⟩
    rw [show ((ghzHFormat (mIncOn a (∅ : Finset (cgEdge k))) hn v : ℕ+) : ℕ) = 1 from this]
    infer_instance
  haveI huT : ∀ v : Fin k,
      Unique (Fin (((fun _ : Fin k => (1 : ℕ+)) v : ℕ+) : ℕ)) := fun v => by
    change Unique (Fin 1)
    infer_instance
  refine restrictsEquiv_of_forall_legEquiv
    (fun v => by haveI := huS v; haveI := huT v; exact Equiv.ofUnique _ _) ?_
  intro idx
  have hghz : ghzH_asKTensor (F := F) (mIncOn a (∅ : Finset (cgEdge k))) hn idx = (1 : F) := by
    unfold ghzH_asKTensor reindexKTensor ghzHTensor
    rw [if_pos]
    refine ⟨fun _ => ⟨0, hn⟩, ?_⟩
    intro v ec
    exact (hempty v).elim ec
  have hunit : ∀ g : (∀ ℓ : Fin k, Fin (((1 : ℕ+) : ℕ))),
      unitTensor F (k := k) (1 : ℕ+) g = (1 : F) := by
    intro g
    unfold unitTensor
    rw [if_pos]
    intro a b
    apply Fin.ext
    have ha := (g a).isLt
    have hb := (g b).isLt
    simp only [PNat.one_coe] at ha hb
    omega
  rw [hghz, hunit]

private theorem pairUnitFold_dyadic_equiv_partialMGHZ {F : Type u} [Field F] {k : ℕ}
    (a : cgEdge k → ℕ) (hk : 0 < k) (ps : List (Fin k × Fin k))
    (hlt : ∀ p ∈ ps, p.1 < p.2)
    (hnodup : (ps.filterMap pairEdge).Nodup) :
    (kronFoldl (TT.of (unitTensor F (k := k) (1 : ℕ+)))
      (ps.map (fun p => pairUnitTT (F := F) (dyadicWeight a p.1 p.2) p))).2
      ∼ₜ ghzH_asKTensor (F := F) (mIncOn a (ps.filterMap pairEdge).toFinset)
        (by norm_num : (1 : ℕ) ≤ 2) := by
  classical
  induction ps using List.reverseRecOn with
  | nil =>
      simp only [List.map_nil, kronFoldl_nil, List.filterMap_nil, List.toFinset_nil]
      exact (ghzH_mIncOn_empty_equiv (F := F) a hk (by norm_num : (1 : ℕ) ≤ 2)).symm
  | append_singleton ps p ih =>
      have hlt' : ∀ q ∈ ps, q.1 < q.2 := fun q hq => hlt q (List.mem_append_left _ hq)
      have hppair : p.1 < p.2 := hlt p (by simp)
      have hpne : p.1 ≠ p.2 := ne_of_lt hppair
      have hpe : pairEdge p = some (edgeOf p.1 p.2 hpne) := by
        unfold pairEdge
        rw [dif_pos hppair]
      have hfmEdges : (ps ++ [p]).filterMap pairEdge
          = ps.filterMap pairEdge ++ [edgeOf p.1 p.2 hpne] := by
        rw [List.filterMap_append]
        simp [hpe]
      have hnodup' : (ps.filterMap pairEdge).Nodup := by
        rw [hfmEdges] at hnodup
        exact (List.nodup_append.mp hnodup).1
      have hdisj : Disjoint (ps.filterMap pairEdge).toFinset
          ({edgeOf p.1 p.2 hpne} : Finset (cgEdge k)) := by
        rw [Finset.disjoint_singleton_right, List.mem_toFinset]
        rw [hfmEdges] at hnodup
        intro hmem
        exact (List.disjoint_of_nodup_append hnodup) hmem (by simp)
      have hpUnit : pairUnitTT (F := F) (dyadicWeight a p.1 p.2) p =
          TT.of (unitPairTensor (F := F)
            ⟨2 ^ a (edgeOf p.1 p.2 hpne),
              Nat.one_le_pow (a (edgeOf p.1 p.2 hpne)) 2 (by norm_num)⟩ p.1 p.2 hpne) := by
        unfold pairUnitTT dyadicWeight
        rw [dif_pos hpne]
        rw [dif_pos]
        exact ⟨hpne, Nat.one_le_pow (a (edgeOf p.1 p.2 hpne)) 2 (by norm_num)⟩
      rw [List.map_append, List.map_singleton, kronFoldl_concat]
      have hIH := ih hlt' hnodup'
      have hstep1 :
          ((kronFoldl (TT.of (unitTensor F (k := k) (1 : ℕ+)))
              (ps.map (fun p => pairUnitTT (F := F) (dyadicWeight a p.1 p.2) p))).kron
              (pairUnitTT (F := F) (dyadicWeight a p.1 p.2) p)).2
            ∼ₜ (ghzH_asKTensor (F := F) (mIncOn a (ps.filterMap pairEdge).toFinset)
                  (by norm_num : (1 : ℕ) ≤ 2)
                ⊠ ghzH_asKTensor (F := F)
                  (mIncOn a ({edgeOf p.1 p.2 hpne} : Finset (cgEdge k)))
                  (by norm_num : (1 : ℕ) ≤ 2)) := by
        rw [hpUnit]
        exact RestrictsEquiv.kron_congr hIH
          (pairUnit_equiv_mIncOn_singleton (F := F) a p.1 p.2 hpne)
      have hstep2 :
          (ghzH_asKTensor (F := F) (mIncOn a (ps.filterMap pairEdge).toFinset)
              (by norm_num : (1 : ℕ) ≤ 2)
            ⊠ ghzH_asKTensor (F := F)
              (mIncOn a ({edgeOf p.1 p.2 hpne} : Finset (cgEdge k)))
              (by norm_num : (1 : ℕ) ≤ 2))
            ∼ₜ ghzH_asKTensor (F := F)
              (mIncOn a ((ps.filterMap pairEdge).toFinset ∪ {edgeOf p.1 p.2 hpne}))
              (by norm_num : (1 : ℕ) ≤ 2) :=
        ghzH_mDisjointUnion_equiv (F := F) hdisj (by norm_num : (1 : ℕ) ≤ 2)
      have hunionEq : (ps.filterMap pairEdge).toFinset ∪ {edgeOf p.1 p.2 hpne}
          = ((ps ++ [p]).filterMap pairEdge).toFinset := by
        rw [hfmEdges, List.toFinset_append]
        simp
      rw [hunionEq] at hstep2
      exact hstep1.trans hstep2

private lemma TensorClass_mk_kronFoldl {F : Type u} [Field F] {k : ℕ} [NeZero k]
    (T₀ : TT F k) (Ts : List (TT F k)) :
    TensorClass.mk (kronFoldl T₀ Ts)
      = TensorClass.mk T₀ * (Ts.map TensorClass.mk).prod := by
  induction Ts generalizing T₀ with
  | nil =>
      simp
  | cons T Ts ih =>
      rw [kronFoldl_cons, ih]
      change TensorClass.mk (T₀.kron T) * (Ts.map TensorClass.mk).prod =
        TensorClass.mk T₀ * (TensorClass.mk T * (Ts.map TensorClass.mk).prod)
      change (TensorClass.mk T₀ * TensorClass.mk T) * (Ts.map TensorClass.mk).prod =
        TensorClass.mk T₀ * (TensorClass.mk T * (Ts.map TensorClass.mk).prod)
      ring

private lemma TensorClass_mk_pairUnitKronQ {F : Type u} [Field F] {k : ℕ} [NeZero k]
    (q : Fin k → Fin k → ℕ) :
    TensorClass.mk (pairUnitKronQ F q)
      = (TensorClass.mk (TT.of (unitTensor F (k := k) (1 : ℕ+)))) *
          (((cgPairsList k).map (fun p => pairUnitTT (F := F) (q p.1 p.2) p)).map
            TensorClass.mk).prod := by
  unfold pairUnitKronQ
  exact TensorClass_mk_kronFoldl _ _

private lemma TensorClass_mk_pairUnitTT_pow {F : Type u} [Field F] {k : ℕ} [NeZero k]
    (q : Fin k → Fin k → ℕ) (hq : ∀ i j, i ≠ j → 1 ≤ q i j)
    (m : ℕ) (hm : 1 ≤ m) {p : Fin k × Fin k} (hp : p ∈ cgPairsList k) :
    TensorClass.mk (pairUnitTT (F := F) ((q p.1 p.2) ^ m) p)
      = (TensorClass.mk (pairUnitTT (F := F) (q p.1 p.2) p) : TensorClass F k) ^ m := by
  classical
  have hlt : p.1 < p.2 := by
    unfold cgPairsList at hp
    rw [Finset.mem_toList, Finset.mem_filter] at hp
    exact hp.2
  have hne : p.1 ≠ p.2 := ne_of_lt hlt
  have hqpos : 1 ≤ q p.1 p.2 := hq p.1 p.2 hne
  have hqpow : 1 ≤ (q p.1 p.2) ^ m := Nat.one_le_pow m (q p.1 p.2) hqpos
  have hleft :
      pairUnitTT (F := F) ((q p.1 p.2) ^ m) p
        = TT.of (unitPairTensor (F := F) ⟨(q p.1 p.2) ^ m, hqpow⟩ p.1 p.2 hne) := by
    unfold pairUnitTT
    rw [dif_pos ⟨hne, hqpow⟩]
  have hright :
      pairUnitTT (F := F) (q p.1 p.2) p
        = TT.of (unitPairTensor (F := F) ⟨q p.1 p.2, hqpos⟩ p.1 p.2 hne) := by
    unfold pairUnitTT
    rw [dif_pos ⟨hne, hqpos⟩]
  rw [hleft, hright]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hequiv := unitPairTensor_pow_equiv_kronPowNat (F := F) p.1 p.2 hne
    (q p.1 p.2) hqpos (n + 1) (by omega)
  have hmk := TensorClass.mk_eq_of_equiv
    (x := TT.of (unitPairTensor (F := F) ⟨(q p.1 p.2) ^ (n + 1), hqpow⟩ p.1 p.2 hne))
    (y := TT.of (kronPowNat (unitPairTensor (F := F) ⟨q p.1 p.2, hqpos⟩ p.1 p.2 hne) n))
    hequiv
  have hpow := mkPow (F := F) (k := k)
    (unitPairTensor (F := F) ⟨q p.1 p.2, hqpos⟩ p.1 p.2 hne) n
  simpa using hmk.trans hpow.symm

private lemma TensorClass_prod_pairUnitTT_pow_list {F : Type u} [Field F] {k : ℕ} [NeZero k]
    (q : Fin k → Fin k → ℕ) (hq : ∀ i j, i ≠ j → 1 ≤ q i j)
    (m : ℕ) (hm : 1 ≤ m) :
    ∀ (ps : List (Fin k × Fin k)), (∀ p ∈ ps, p ∈ cgPairsList k) →
    (ps.map (fun p =>
        TensorClass.mk (pairUnitTT (F := F) ((q p.1 p.2) ^ m) p))).prod
      =
    ((ps.map (fun p =>
        TensorClass.mk (pairUnitTT (F := F) (q p.1 p.2) p))).prod) ^ m
  | [], _ => by simp
  | p :: ps, hmem => by
      have hp : p ∈ cgPairsList k := hmem p (by simp)
      have htail : ∀ x ∈ ps, x ∈ cgPairsList k := by
        intro x hx
        exact hmem x (by simp [hx])
      have hpEq := TensorClass_mk_pairUnitTT_pow (F := F) (k := k) q hq m hm
        (hp := hp)
      simp only [List.map_cons, List.prod_cons]
      rw [hpEq, TensorClass_prod_pairUnitTT_pow_list (F := F) (k := k) q hq m hm ps htail]
      exact (mul_pow _ _ _).symm

private lemma TensorClass_prod_pairUnitTT_pow {F : Type u} [Field F] {k : ℕ} [NeZero k]
    (q : Fin k → Fin k → ℕ) (hq : ∀ i j, i ≠ j → 1 ≤ q i j)
    (m : ℕ) (hm : 1 ≤ m) :
    (((cgPairsList k).map
        (fun p => pairUnitTT (F := F) ((q p.1 p.2) ^ m) p)).map TensorClass.mk).prod
      =
    ((((cgPairsList k).map
        (fun p => pairUnitTT (F := F) (q p.1 p.2) p)).map TensorClass.mk).prod) ^ m := by
  classical
  rw [List.map_map, List.map_map]
  exact TensorClass_prod_pairUnitTT_pow_list (F := F) (k := k) q hq m hm
    (cgPairsList k) (fun p hp => hp)

/-- **Step C, quotient-level fold regrouping** (genmamu tex:152-156, 232):
the weighted pair-unit fold with weights `q_{ij}^m` is restriction-equivalent to the
`m`-fold Kronecker power of the weighted pair-unit fold with weights `q_{ij}`. -/
theorem pairUnitKronQ_pow_equiv_kronPow {F : Type u} [Field F] {k : ℕ}
    (q : Fin k → Fin k → ℕ) (hq : ∀ i j, i ≠ j → 1 ≤ q i j)
    (m : ℕ) (hm : 1 ≤ m) :
    (pairUnitKronQ F (fun i j => (q i j)^m)).2
      ∼ₜ kronPowNat (pairUnitKronQ F q).2 (m - 1) := by
  classical
  by_cases hk2 : 2 ≤ k
  · haveI : NeZero k := ⟨by omega⟩
    have hmk_left := TensorClass_mk_pairUnitKronQ (F := F) (k := k)
      (fun i j => (q i j) ^ m)
    have hmk_right := TensorClass_mk_pairUnitKronQ (F := F) (k := k) q
    have hprod := TensorClass_prod_pairUnitTT_pow (F := F) (k := k) q hq m hm
    have hclass :
        TensorClass.mk (pairUnitKronQ F (fun i j => (q i j) ^ m))
          =
        TensorClass.mk ⟨_, kronPowNat (pairUnitKronQ F q).2 (m - 1)⟩ := by
      obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hm
      subst m
      have hpow := mkPow (F := F) (k := k) (pairUnitKronQ F q).2 n
      rw [hmk_left, hprod]
      rw [show 1 + n - 1 = n by omega]
      rw [← hpow, hmk_right]
      have hunit :
          TensorClass.mk (TT.of (unitTensor F (k := k) (1 : ℕ+))) = (1 : TensorClass F k) :=
        TensorClass.one_def.symm
      rw [hunit]
      rw [Nat.add_comm 1 n]
      simp
    exact Quotient.exact hclass
  · have hlen0 : (cgPairsList k) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro p hp
      have hlt : p.1 < p.2 := by
        unfold cgPairsList at hp
        rw [Finset.mem_toList, Finset.mem_filter] at hp
        exact hp.2
      have hk : 2 ≤ k := by
        have hi := p.1.isLt
        have hj := p.2.isLt
        rw [Fin.lt_def] at hlt
        omega
      exact hk2 hk
    unfold pairUnitKronQ
    rw [hlen0]
    simp only [List.map_nil, kronFoldl_nil]
    exact unitTensor_one_kronPowNat_equiv (F := F) (k := k) (m - 1)

/-- **General multiplicity GHZ↔pair-unit identification**
(genmamu tex:124-159, 232).

For an ARBITRARY multigraph `H_a` on `[k]` (`a : cgEdge k → ℕ`, `a e` parallel rank-2 edges
per pair `e`), the all-rank-2 GHZ `GHZ^{H_a}_2 = ghzH (mInc a) 2` is restriction-equivalent to
the weighted pair-unit Kronecker product `⊠_e ⟨2^{a e}⟩_e = pairUnitKronQ (dyadicWeight a)`.

This is genmamu's GHZ^H construction (tex:124-159: `GHZ^{H_1+H_2} = GHZ^{H_1} ⊗ GHZ^{H_2}`, single
edge `S` ↦ GHZ on `S`) read at rank 2 with multiplicities: decompose `GHZ^{H_a}` over edge-instances
`Σ e, Fin (a e)`, merge the `a e` parallel rank-2 pair-units on each pair `e` into `⟨2^{a e}⟩_e` via
`unitPairTensor_kron_equiv`, and merge disjoint pairs via `ghzH_disjointUnion_equiv` — the
varying-rank
/ multiplicity analogue of `pairUnitKronAll_equiv_ghzH` (`pairUnitFold_equiv_partialGHZ`). -/
private theorem ghzH_mInc_equiv_pairUnitKronQ_dyadicWeight {F : Type u} [Field F]
    (a : cgEdge k → ℕ) (hk : 3 ≤ k) :
    ghzH_asKTensor (F := F) (mInc a) (by norm_num : (1:ℕ) ≤ 2)
      ∼ₜ (pairUnitKronQ F (dyadicWeight a)).2 := by
  classical
  have hk0 : 0 < k := by omega
  have hmem : ∀ p ∈ cgPairsList k, p.1 < p.2 := by
    intro p hp
    unfold cgPairsList at hp
    rw [Finset.mem_toList, Finset.mem_filter] at hp
    exact hp.2
  have hlist_nodup : (cgPairsList k).Nodup := by
    unfold cgPairsList
    exact Finset.nodup_toList _
  have hedge_inj : ∀ p q : Fin k × Fin k, p.1 < p.2 → q.1 < q.2 →
      pairEdge p = pairEdge q → p = q := by
    intro p q hp hq hpq
    unfold pairEdge at hpq
    rw [dif_pos hp, dif_pos hq] at hpq
    injection hpq with heq
    have hset : ({p.1, p.2} : Finset (Fin k)) = ({q.1, q.2} : Finset (Fin k)) := by
      have := congrArg Subtype.val heq
      simpa [edgeOf] using this
    have hp1_mem : p.1 ∈ ({q.1, q.2} : Finset (Fin k)) := by
      rw [← hset]
      simp
    have hp2_mem : p.2 ∈ ({q.1, q.2} : Finset (Fin k)) := by
      rw [← hset]
      simp
    rw [Finset.mem_insert, Finset.mem_singleton] at hp1_mem hp2_mem
    rcases hp1_mem with hp1 | hp1 <;> rcases hp2_mem with hp2 | hp2
    · exact absurd (hp1.trans hp2.symm) (ne_of_lt hp)
    · exact Prod.ext hp1 hp2
    · have : q.2 < q.1 := by simpa [hp1, hp2] using hp
      exact absurd this (not_lt_of_ge (le_of_lt hq))
    · exact absurd (hp1.trans hp2.symm) (ne_of_lt hp)
  have hfm_nodup : ((cgPairsList k).filterMap pairEdge).Nodup := by
    refine List.Nodup.filterMap ?_ hlist_nodup
    intro p q e hpe hqe
    have hp : p.1 < p.2 := by
      unfold pairEdge at hpe
      by_contra h
      rw [dif_neg h] at hpe
      exact (Option.not_mem_none e) hpe
    have hq : q.1 < q.2 := by
      unfold pairEdge at hqe
      by_contra h
      rw [dif_neg h] at hqe
      exact (Option.not_mem_none e) hqe
    have hpe' : pairEdge p = some e := by rw [Option.mem_def] at hpe; exact hpe
    have hqe' : pairEdge q = some e := by rw [Option.mem_def] at hqe; exact hqe
    exact hedge_inj p q hp hq (hpe'.trans hqe'.symm)
  have hedge_univ : ((cgPairsList k).filterMap pairEdge).toFinset
      = (Finset.univ : Finset (cgEdge k)) := by
    rw [Finset.eq_univ_iff_forall]
    intro e
    rw [List.mem_toFinset, List.mem_filterMap]
    obtain ⟨x, y, hxy, hval⟩ := Finset.card_eq_two.mp e.2
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · refine ⟨(x, y), ?_, ?_⟩
      · unfold cgPairsList
        rw [Finset.mem_toList, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hlt⟩
      · unfold pairEdge
        rw [dif_pos hlt]
        congr 1
        exact Subtype.ext (by rw [edgeOf]; exact hval.symm)
    · refine ⟨(y, x), ?_, ?_⟩
      · unfold cgPairsList
        rw [Finset.mem_toList, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hgt⟩
      · unfold pairEdge
        rw [dif_pos hgt]
        congr 1
        refine Subtype.ext ?_
        rw [edgeOf, hval]
        exact Finset.pair_comm y x
  have hfold := pairUnitFold_dyadic_equiv_partialMGHZ (F := F) a hk0 (cgPairsList k)
    hmem hfm_nodup
  change ghzH_asKTensor (F := F) (mInc a) (by norm_num : (1:ℕ) ≤ 2)
      ∼ₜ (kronFoldl (TT.of (unitTensor F (k := k) (1 : ℕ+)))
        ((cgPairsList k).map (fun p => pairUnitTT (F := F) (dyadicWeight a p.1 p.2) p))).2
  rw [hedge_univ] at hfold
  exact (ghzH_mIncOn_univ_equiv_mInc (F := F) a (by norm_num : (1 : ℕ) ≤ 2)).symm.trans
    hfold.symm

/-- `dyadicWeight (aFloor q m) i j = dyadicFloorWeight q m i j` off-diagonal: the dyadic exponent
`aFloor q m {i,j} = log₂(dyadicFloorWeight)` recovers the floor weight (a power of two), using
`hsym`
to undo the endpoint ordering of `aFloor`'s `edgeEndpts`. -/
private lemma dyadicWeight_aFloor_pair {k : ℕ} (q : Fin k → Fin k → ℕ) (m : ℕ)
    (hsym : ∀ i j, q i j = q j i) {i j : Fin k} (hne : i ≠ j) :
    dyadicWeight (aFloor q m) i j = dyadicFloorWeight q m i j := by
  classical
  rw [dyadicWeight, dif_pos hne]
  unfold aFloor
  set ab := edgeEndpts (edgeOf i j hne) with hab
  have hset : ({ab.1, ab.2} : Finset (Fin k)) = ({i, j} : Finset (Fin k)) := by
    have heq' := (edgeEndpts_spec (edgeOf i j hne)).2
    have hval : (edgeOf i j hne).val = ({i, j} : Finset (Fin k)) := by
      unfold edgeOf; rfl
    rw [hab, ← heq', hval]
  have hdfw : dyadicFloorWeight q m ab.1 ab.2 = dyadicFloorWeight q m i j := by
    have hdfsym : ∀ x y, dyadicFloorWeight q m x y = dyadicFloorWeight q m y x := by
      intro x y; unfold dyadicFloorWeight; rw [hsym x y]
    have hab1 : ab.1 ∈ ({i, j} : Finset (Fin k)) := by
      rw [← hset]; exact Finset.mem_insert_self _ _
    have hab2 : ab.2 ∈ ({i, j} : Finset (Fin k)) := by
      rw [← hset]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have habne : ab.1 ≠ ab.2 := (edgeEndpts_spec (edgeOf i j hne)).1
    rw [Finset.mem_insert, Finset.mem_singleton] at hab1 hab2
    rcases hab1 with h1 | h1 <;> rcases hab2 with h2 | h2
    · exact absurd (h1.trans h2.symm) habne
    · rw [h1, h2]
    · rw [h1, h2]; exact hdfsym j i
    · exact absurd (h1.trans h2.symm) habne
  rw [hdfw, dyadicFloorWeight_isPow]

/-- **Step A** (genmamu tex:124-159, 232): GHZ on the dyadic-floor multigraph ∼ₜ the weighted
pair-unit fold with dyadic floor weights — the `aFloor` instance of the general multiplicity
identification `ghzH_mInc_equiv_pairUnitKronQ_dyadicWeight`, after rewriting
`dyadicWeight (aFloor q m) = dyadicFloorWeight q m` (`dyadicWeight_aFloor_pair`). -/
theorem ghzH_aFloor_equiv_pairUnitKronQ_dyadicFloorWeight {F : Type u} [Field F]
    (q : Fin k → Fin k → ℕ) (hk : 3 ≤ k)
    (hsym : ∀ i j, q i j = q j i) (m : ℕ) :
    ghzH_asKTensor (F := F) (mInc (aFloor q m)) (by norm_num : (1:ℕ) ≤ 2)
      ∼ₜ (pairUnitKronQ F (dyadicFloorWeight q m)).2 := by
  classical
  have hcore := ghzH_mInc_equiv_pairUnitKronQ_dyadicWeight (F := F) (aFloor q m) hk
  have hfold :
      pairUnitKronQ F (dyadicWeight (aFloor q m)) =
        pairUnitKronQ F (dyadicFloorWeight q m) := by
    unfold pairUnitKronQ
    congr 1
    apply List.map_congr_left
    intro p hp
    have hlt : p.1 < p.2 := by
      unfold cgPairsList at hp
      rw [Finset.mem_toList, Finset.mem_filter] at hp
      exact hp.2
    have hpne : p.1 ≠ p.2 := ne_of_lt hlt
    rw [dyadicWeight_aFloor_pair q m hsym hpne]
  rw [← hfold]
  exact hcore

/-- **Leg-wise pair-unit monotonicity folded over `cgPairsList`** (genmamu:159-199, 232).

For off-diagonal pairs, `dyadicFloorWeight q m i j ≤ (q i j)^m`; hence
`unitPairTensor_restricts_of_le` gives the per-pair restriction, and
`Restricts.kronFoldl` folds these restrictions through
`pairUnitKronQ F r = ⊠_{i<j}⟨r i j⟩`. -/
theorem pairUnitKronQ_dyadicFloorWeight_restricts_pow {F : Type u} [Field F]
    (q : Fin k → Fin k → ℕ) (hq : ∀ i j, i ≠ j → 1 ≤ q i j) (m : ℕ) (hm : 1 ≤ m) :
    TTRestricts (pairUnitKronQ F (dyadicFloorWeight q m))
      (pairUnitKronQ F (fun i j => (q i j)^m)) := by
  classical
  unfold pairUnitKronQ
  apply Restricts.kronFoldl (Restricts.refl _) ?_
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.mpr ?_
  intro p hp
  have hlt : p.1 < p.2 := by
    unfold cgPairsList at hp
    rw [Finset.mem_toList, Finset.mem_filter] at hp
    exact hp.2
  have hpne : p.1 ≠ p.2 := ne_of_lt hlt
  have hqpos : 1 ≤ q p.1 p.2 := hq p.1 p.2 hpne
  have hpowpos : 1 ≤ (q p.1 p.2) ^ m := Nat.one_le_pow m _ hqpos
  have hdfpos : 1 ≤ dyadicFloorWeight q m p.1 p.2 := by
    unfold dyadicFloorWeight
    by_cases hsmall : q p.1 p.2 ≤ 1
    · rw [if_pos hsmall]
    · rw [if_neg hsmall]
      exact Nat.one_le_pow _ _ (by norm_num : 1 ≤ 2)
  have hle : dyadicFloorWeight q m p.1 p.2 ≤ (q p.1 p.2) ^ m := by
    unfold dyadicFloorWeight
    by_cases hsmall : q p.1 p.2 ≤ 1
    · rw [if_pos hsmall]
      exact hpowpos
    · rw [if_neg hsmall]
      exact Nat.pow_log_le_self 2 (by positivity)
  unfold pairUnitTT
  rw [dif_pos ⟨hpne, hdfpos⟩, dif_pos ⟨hpne, hpowpos⟩]
  exact unitPairTensor_restricts_of_le (F := F) p.1 p.2 hpne hle

/-- **Weighted dyadic GHZ/pair-unit bridge** (genmamu:159-199, 232;
semicontinuity tex:987-990).

Given the finite min-cut/dyadic-floor arithmetic and
`multigraph_asympSubrank_ge`, which supplies
`2^λ(H_{aFloor}) ≤ asympSubrank(GHZ^{H_{aFloor}}_2)`, this tensor restriction is
assembled from the dyadic-floor multigraph GHZ / pair-unit identification,
`pairUnitKronQ_dyadicFloorWeight_restricts_pow`, and the Kronecker-power regrouping
for weighted pair-unit folds.

This is the varying-rank / incomplete analogue of `pairUnitKronAll_equiv_ghzH` (UniformVC):
each pair `e` carries `aFloor e` parallel rank-2 GHZ edges, which merge (GHZ↔pair-unit, one pair
at a time, `unitPairTensor_kron_equiv`) into a single rank-`2^{aFloor e} = dyadicFloorWeight q m`
pair-unit, then the powered pair-units regroup into `kronPowNat`. -/
theorem ghzH_aFloor_restricts_pairUnitKronQ_kronPow {F : Type u} [Field F]
    (q : Fin k → Fin k → ℕ) (hk : 3 ≤ k)
    (hsym : ∀ i j, q i j = q j i) (hq : ∀ i j, i ≠ j → 1 ≤ q i j)
    (m : ℕ) (hm : 1 ≤ m) :
    Restricts
      (ghzH_asKTensor (F := F) (mInc (aFloor q m)) (by norm_num : (1:ℕ) ≤ 2))
      (kronPowNat (pairUnitKronQ F q).2 (m - 1)) := by
  classical
  have hA := ghzH_aFloor_equiv_pairUnitKronQ_dyadicFloorWeight
    (F := F) q hk hsym m
  have hB := pairUnitKronQ_dyadicFloorWeight_restricts_pow
    (F := F) q hq m hm
  have hC := pairUnitKronQ_pow_equiv_kronPow
    (F := F) q hq m hm
  exact hA.1.trans (hB.trans hC.1)

/-- **Rank-one all-pairs tensor restricts to a positive weighted pair-unit fold**
(genmamu:152-156, 159-199).

This supplies the nonzero hypothesis for `asympSubrank_kronPowNat`: the rank-one complete
pair-unit tensor is equivalent to a nonzero rank-one complete GHZ tensor, and every off-diagonal
weight of `q` is at least `1`. -/
theorem pairUnitKronQ_mk_ne_zero {F : Type u} [Field F] [NeZero k]
    (q : Fin k → Fin k → ℕ) (hk : 3 ≤ k) (hq : ∀ i j, i ≠ j → 1 ≤ q i j) :
    TensorClass.mk (pairUnitKronQ F q) ≠ (0 : TensorClass F k) := by
  classical
  have hres : TTRestricts (pairUnitKronAll F k 1) (pairUnitKronQ F q) := by
    unfold pairUnitKronAll pairUnitKronQ
    apply Restricts.kronFoldl (Restricts.refl _) ?_
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr ?_
    intro p hp
    have hlt : p.1 < p.2 := by
      unfold cgPairsList at hp
      rw [Finset.mem_toList, Finset.mem_filter] at hp
      exact hp.2
    have hpne : p.1 ≠ p.2 := ne_of_lt hlt
    have hqpos : 1 ≤ q p.1 p.2 := hq p.1 p.2 hpne
    have hone : 1 ≤ (1 : ℕ) := by norm_num
    unfold pairUnitTT
    rw [dif_pos ⟨hpne, hone⟩, dif_pos ⟨hpne, hqpos⟩]
    exact unitPairTensor_restricts_of_le (F := F) p.1 p.2 hpne hqpos
  have hone_ne :
      TensorClass.mk (pairUnitKronAll F k 1) ≠ (0 : TensorClass F k) := by
    have heq :
        TensorClass.mk (pairUnitKronAll F k 1)
          = TensorClass.mk
              (⟨_, ghzH_asKTensor (F := F) (cgInc k)
                (by norm_num : (1 : ℕ) ≤ 1)⟩ : TT F k) := by
      exact TensorClass.mk_eq_of_equiv
        (pairUnitKronAll_equiv_ghzH (F := F) hk (by norm_num : (1 : ℕ) ≤ 1))
    rw [heq]
    exact ghzH_mk_ne_zero (F := F) hk (by norm_num : (1 : ℕ) ≤ 1)
  exact mk_ne_zero_of_restricts hres hone_ne

/-- **The dyadic pair-unit bridge plus folded monotonicity** (genmamu:159-199, 232).

This combines the tensor-equivalence statement with folded monotonicity to prove
the analytic inequality up to the powered weights `q^m`. -/
theorem ghzH_aFloor_asympSubrank_le_pow {F : Type u} [Field F] [Infinite F]
    (q : Fin k → Fin k → ℕ) (hk : 3 ≤ k)
    (hsym : ∀ i j, q i j = q j i) (hq : ∀ i j, i ≠ j → 1 ≤ q i j)
    (m : ℕ) (hm : 1 ≤ m) :
    asympSubrank (ghzH_asKTensor (F := F) (mInc (aFloor q m)) (by norm_num : (1:ℕ) ≤ 2))
      ≤ (asympSubrank (pairUnitKronQ F q).2) ^ m := by
  classical
  haveI : NeZero k := ⟨by omega⟩
  have hk2 : 2 ≤ k := by omega
  have hres := ghzH_aFloor_restricts_pairUnitKronQ_kronPow
    (F := F) q hk hsym hq m hm
  calc
    asympSubrank
        (ghzH_asKTensor (F := F) (mInc (aFloor q m)) (by norm_num : (1:ℕ) ≤ 2))
        ≤ asympSubrank (kronPowNat (pairUnitKronQ F q).2 (m - 1)) :=
      asympSubrank_mono_restricts hk2 hres
    _ = (asympSubrank (pairUnitKronQ F q).2) ^ ((m - 1) + 1) := by
      exact asympSubrank_kronPowNat hk2 (pairUnitKronQ F q).2
        (pairUnitKronQ_mk_ne_zero (F := F) q hk hq) (m - 1)
    _ = (asympSubrank (pairUnitKronQ F q).2) ^ m := by
      congr 1
      omega

/-- **`1 ≤ asympSubrank T` for nonzero `T`** (subrank `≥ 1` + `asympSubrank ≥ subrank`).
The `n = 0` term of the `asympSubrank` `sSup`-range is `subrank T ≥ 1` (the rank-`1` unit
restricts into any nonzero `T`).  Mirrors `BorderSubrank` lines 1563-1592. -/
theorem one_le_asympSubrank_of_ne_zero {F : Type u} [Field F] {k : ℕ} [NeZero k] (hk : 2 ≤ k)
    {d : Fin k → ℕ+} (T : KTensor F d)
    (hT : (TensorClass.mk ⟨d, T⟩ : TensorClass F k) ≠ 0) :
    (1 : ℝ) ≤ asympSubrank T := by
  classical
  have h0 : (0 : ℕ) < k := by omega
  have h1 : (1 : ℕ) < k := by omega
  have hne01 : (⟨1, h1⟩ : Fin k) ≠ ⟨0, h0⟩ := by simp [Fin.ext_iff]
  have hone_sub : 1 ≤ subrank T := by
    have hres : Restricts (unitTensor F (k := k) 1) T :=
      unitTensor_one_restricts_of_ne_zero T hT
    have hmem : (1 : ℕ) ∈ { r : ℕ | ∃ hr : 0 < r,
        Restricts (unitTensor F (k := k) ⟨r, hr⟩) T } := ⟨one_pos, by simpa using hres⟩
    exact le_csSup (subrank_set_bddAbove' ⟨0, h0⟩ ⟨1, h1⟩ hne01 T) hmem
  have hQeq : asympSubrank T = sSup (Set.range (fun n : ℕ =>
      (subrank (kronPowNat T n) : ℝ) ^ ((1 : ℝ) / ((n : ℝ) + 1)))) := rfl
  have hbddQ : BddAbove (Set.range (fun n : ℕ =>
      (subrank (kronPowNat T n) : ℝ) ^ ((1 : ℝ) / ((n : ℝ) + 1)))) :=
    concrete_asympSubrankSet_bddAbove hk T
  have hmem0 : (subrank (kronPowNat T 0) : ℝ) ^ ((1 : ℝ) / (((0 : ℕ) : ℝ) + 1))
      ∈ Set.range (fun n : ℕ =>
        (subrank (kronPowNat T n) : ℝ) ^ ((1 : ℝ) / ((n : ℝ) + 1))) := ⟨0, rfl⟩
  have hterm0 : (1 : ℝ) ≤ (subrank (kronPowNat T 0) : ℝ) ^ ((1 : ℝ) / (((0 : ℕ) : ℝ) + 1)) := by
    have hk0 : (subrank (kronPowNat T 0) : ℝ) = (subrank T : ℝ) := by simp [kronPowNat]
    rw [hk0]; simp only [Nat.cast_zero, zero_add, div_one, Real.rpow_one]
    exact_mod_cast hone_sub
  rw [hQeq]; exact le_trans hterm0 (le_csSup hbddQ hmem0)

theorem dyadicFloorWeight_minCut_le_asympSubrank_power {F : Type u} [Field F] [Infinite F]
    (q : Fin k → Fin k → ℕ) (hk : 3 ≤ k)
    (hsym : ∀ i j, q i j = q j i) (hq : ∀ i j, i ≠ j → 1 ≤ q i j)
    (m : ℕ) (hm : 1 ≤ m) :
    (MinCut.minCut (dyadicFloorWeight q m) (by omega : 2 ≤ k) : ℝ) ≤
      (asympSubrank (pairUnitKronQ F q).2) ^ m := by
  classical
  haveI : NeZero k := ⟨by omega⟩
  have hk2 : 2 ≤ k := by omega
  have hn1 : 1 ≤ (2 : ℕ) := by norm_num
  -- `minCut(dyadicFloorWeight q m) = minCut(dyadicWeight (aFloor q m)) = 2^(mLambda (aFloor q m))`.
  have hmincut_eq :
      MinCut.minCut (dyadicFloorWeight q m) hk2 = 2 ^ (mLambda (aFloor q m) hk2) := by
    rw [← dyadicWeight_aFloor_eq q m hsym hk2, ← two_pow_mLambda_eq_minCut_dyadicWeight]
  -- The GHZ↔pair-unit bridge.
  have hbridge := ghzH_aFloor_asympSubrank_le_pow (F := F) q hk hsym hq m hm
  -- `1 ≤ asympSubrank(GHZ^{H_aFloor}_2)` (GHZ multigraph tensor is nonzero, genmamu).
  have hGHZ1 : (1 : ℝ) ≤
      asympSubrank (ghzH_asKTensor (F := F) (mInc (aFloor q m)) hn1) :=
    one_le_asympSubrank_of_ne_zero hk2 _ (ghzH_m_mk_ne_zero (aFloor q m) hk hn1)
  have hcast :
      ((MinCut.minCut (dyadicFloorWeight q m) hk2 : ℕ) : ℝ) =
        (2 : ℝ) ^ (mLambda (aFloor q m) hk2) := by
    rw [hmincut_eq]; push_cast; ring
  rw [hcast]
  by_cases hlam : mLambda (aFloor q m) hk2 = 0
  · -- `mLambda = 0`: LHS = `2^0 = 1 ≤ asympSubrank(GHZ) ≤ asympSubrank(pairUnitKronQ)^m`.
    rw [hlam]; simp only [pow_zero]
    exact le_trans hGHZ1 hbridge
  · -- `mLambda ≥ 1`: the multigraph lower bound gives `2^λ ≤ asympSubrank(GHZ)`.
    have hpos : 1 ≤ mLambda (aFloor q m) hk2 := by omega
    have hB := multigraph_asympSubrank_ge (F := F) (aFloor q m) hk hpos
    exact le_trans hB hbridge

/-- **Weighted dyadic washout power bound** (semicontinuity tex:987-990).

For every positive power `m`, this is the exact dyadic-reduction estimate needed by
`washout_const_le`:
`minCut(q)^m ≤ 2^(k*k) * asympSubrank(⊠_{i<j} ⟨q_ij⟩)^m`.

The intended proof is the Vrana-Christandl dyadic floor argument at semicontinuity
paper tex:987-990 / MR3627407, combining:
* the all-2 multigraph identification
  `ghzH_asKTensor (mInc a) 2 ∼ₜ ⊠_e ⟨2 ^ a e⟩_e`,
* `2 ^ mLambda a = MinCut.minCut (fun i j => 2 ^ a_{ij})`,
* pair-unit monotonicity and Kronecker power merging,
* the floor-log dyadic approximation.

The remaining technical reconciliation is the mixed case where some off-diagonal
`q_ij = 1`: the honest dyadic floor exponent is `0`, while `mInc` currently indexes
parallel rank-2 edges by `ℕ+`.  Pairs with `q_ij = 1` contribute factor `1` to every
cut and should be omitted from the multigraph approximation without changing the
cut products; this omission is isolated in
`dyadicFloorWeight_minCut_le_asympSubrank_power`. -/
theorem weightedVC_dyadic_power_bound {F : Type u} [Field F] [Infinite F]
    (q : Fin k → Fin k → ℕ) (hk : 3 ≤ k)
    (hsym : ∀ i j, q i j = q j i) (hq : ∀ i j, i ≠ j → 1 ≤ q i j) :
    ∀ m : ℕ, 1 ≤ m →
      ((MinCut.minCut q (by omega : 2 ≤ k) : ℝ) ^ m) ≤
        (2 : ℝ) ^ (k * k) * (asympSubrank (pairUnitKronQ F q).2) ^ m := by
  classical
  intro m hm
  have hk2 : 2 ≤ k := by omega
  have hpow :
      (MinCut.minCut (fun i j => (q i j) ^ m) hk2 : ℝ) =
        (MinCut.minCut q hk2 : ℝ) ^ m := by
    rw [MinCut.minCut_pow q hk2 m]
    norm_num
  have hfloorNat :
      MinCut.minCut (fun i j => (q i j) ^ m) hk2 ≤
        2 ^ (k * k) * MinCut.minCut (dyadicFloorWeight q m) hk2 :=
    MinCut.minCut_le_const_mul_floor
      (fun i j => (q i j) ^ m) (dyadicFloorWeight q m) hk2
      (dyadicFloorWeight_loss q hm)
  have hfloor :
      (MinCut.minCut (fun i j => (q i j) ^ m) hk2 : ℝ) ≤
        (2 : ℝ) ^ (k * k) *
          (MinCut.minCut (dyadicFloorWeight q m) hk2 : ℝ) := by
    exact_mod_cast hfloorNat
  have hbridge :=
    dyadicFloorWeight_minCut_le_asympSubrank_power (F := F) q hk hsym hq m hm
  calc
    (MinCut.minCut q hk2 : ℝ) ^ m
        = (MinCut.minCut (fun i j => (q i j) ^ m) hk2 : ℝ) := hpow.symm
    _ ≤ (2 : ℝ) ^ (k * k) *
          (MinCut.minCut (dyadicFloorWeight q m) hk2 : ℝ) := hfloor
    _ ≤ (2 : ℝ) ^ (k * k) * (asympSubrank (pairUnitKronQ F q).2) ^ m := by
      exact mul_le_mul_of_nonneg_left hbridge (by positivity)

/-- **Weighted Vrana-Christandl dyadic reduction** (semicontinuity tex:987-990):
`minCut(q) ≤ asympSubrank(⊠_{i<j} ⟨q_ij⟩_{i,j})`.

The body is now the constant-overhead washout from the sharp per-power dyadic estimate
`weightedVC_dyadic_power_bound`. -/
theorem weightedVC_dyadic_reduction {F : Type u} [Field F] [Infinite F]
    (q : Fin k → Fin k → ℕ) (hk : 3 ≤ k)
    (hsym : ∀ i j, q i j = q j i) (hq : ∀ i j, i ≠ j → 1 ≤ q i j) :
    (MinCut.minCut q (by omega : 2 ≤ k) : ℝ) ≤
      asympSubrank (pairUnitKronQ F q).2 := by
  classical
  haveI : NeZero k := ⟨by omega⟩
  have hk2 : 2 ≤ k := by omega
  exact washout_const_le
    (s := (MinCut.minCut q (by omega : 2 ≤ k) : ℝ))
    (Q := asympSubrank (pairUnitKronQ F q).2)
    (K := (2 : ℝ) ^ (k * k))
    (by positivity)
    (asympSubrank_nonneg' hk2 _)
    (by positivity)
    (weightedVC_dyadic_power_bound (F := F) q hk hsym hq)

/-- **Weighted Vrana-Christandl achievability** (semicontinuity tex:987-990):

`minCut(q) ≤ asympSubrank(⊠_{i<j} ⟨q_ij⟩_{i,j})`.

The proof is by dyadic reduction from the proofn multigraph achievability theorem
`multigraph_asympSubrank_ge`. -/
theorem weightedVC {F : Type u} [Field F] [Infinite F]
    (q : Fin k → Fin k → ℕ) (hk : 3 ≤ k)
    (hsym : ∀ i j, q i j = q j i) (hq : ∀ i j, i ≠ j → 1 ≤ q i j) :
    (MinCut.minCut q (by omega : 2 ≤ k) : ℝ) ≤
      asympSubrank (pairUnitKronQ F q).2 :=
  weightedVC_dyadic_reduction (F := F) q hk hsym hq

end Semicontinuity
