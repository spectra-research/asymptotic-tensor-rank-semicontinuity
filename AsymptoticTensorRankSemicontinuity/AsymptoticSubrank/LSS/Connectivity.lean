/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# LSS vertex-connectivity and the cutset lemma

This file formalizes vertex-connectivity and the cutset lemma `lem:con` in the
Lovász–Saks–Schrijver / Gortler–Theran GOR argument.

Mathlib only provides EDGE-connectivity for `SimpleGraph`, so the
vertex-connectivity API below is built from scratch on top of
`SimpleGraph.induce` and `SimpleGraph.Reachable`.

Sources:
* Gortler–Theran, "A new proof of ... general position orthogonal
  representations", `references/GOR-LSS-2310.11565-gorProof.tex`,
  Lemma `lem:con` (tex:385-394):
    "If `G` is `(n−D)`-connected and `i ≥ D`, then `σ_i` and `σ_{i+1}`
     are connected by a path that visits only vertices in
     `{σ_1, …, σ_{i+1}}`.  Proof: If every path from `σ_i` to `σ_{i+1}`
     visits some `σ_j` with `j > i+1`, then `{σ_{i+2}, …, σ_n}` is a cut
     set.  Since `i ≥ D`, this would contradict `(n−D)`-connectivity."
* Lovász–Saks–Schrijver, "Orthogonal representations and connectivity of
  graphs", the original definition of `(n−d)`-connectivity = standard
  vertex-connectivity (no separator of fewer than `n−d` nodes); the easy
  direction uses "a set `A` of `n−d−1` nodes separating it into two
  components".  (The LSS `.tex` is not vendored in this repo; the
  definition below is the standard vertex-connectivity definition that
  GOR cites, matched to the "separator / cut set" language of both
  sources.)
-/
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open SimpleGraph

namespace LSS

variable {n : ℕ} (G : SimpleGraph (Fin n))

/-- **Reachability within a vertex set.**
    `u` and `v` are joined by a walk in `G` that visits only vertices of
    `T` — i.e. they are reachable in the induced subgraph `G.induce T`.
    (Both endpoints must lie in `T`.)

    This is the Lean encoding of "connected by a path that visits only
    vertices in `T`" from GOR `lem:con` (tex:387-388). -/
def ReachableWithin (T : Set (Fin n)) (u v : Fin n) : Prop :=
  ∃ (hu : u ∈ T) (hv : v ∈ T), (G.induce T).Reachable ⟨u, hu⟩ ⟨v, hv⟩

/-- **Separator.**
    `S` separates `u` from `v` if neither endpoint lies in `S` and there
    is no `u`–`v` walk in `G` avoiding `S`; equivalently `u` and `v` are
    not reachable in the graph `G.induce Sᶜ` obtained by deleting `S`.
    This is the "cut set" of GOR `lem:con` (tex:391-392) and the
    "separating set of nodes" of LSS. -/
def IsSeparator (S : Finset (Fin n)) (u v : Fin n) : Prop :=
  u ∉ S ∧ v ∉ S ∧ ¬ ReachableWithin G (↑S)ᶜ u v

/-- **`k`-vertex-connectivity.**
    `G` on `n` vertices is `k`-vertex-connected if `k < n` and deleting
    any set `S` of fewer than `k` vertices keeps every pair of remaining
    vertices reachable — i.e. no set of `< k` vertices is a separator.

    This is the standard vertex-connectivity definition GOR cites from
    LSS: "`G` is `(n−d)`-connected" means no set of `n−d−1` nodes
    separates it (LSS easy direction). -/
def IsKVertexConnected (k : ℕ) : Prop :=
  k < n ∧
    ∀ (S : Finset (Fin n)), S.card < k →
      ∀ (u v : Fin n), u ∉ S → v ∉ S → ReachableWithin G (↑S)ᶜ u v

variable {G}

/-- `ReachableWithin` is monotone in the vertex set: a walk staying inside
    `T` also stays inside any larger set `T'`.  Proved via the induced
    subgraph embedding `SimpleGraph.induceHomOfLE` and `Reachable.map`. -/
theorem ReachableWithin.mono {T T' : Set (Fin n)} (hT : T ⊆ T')
    {u v : Fin n} (h : ReachableWithin G T u v) : ReachableWithin G T' u v := by
  obtain ⟨hu, hv, hr⟩ := h
  refine ⟨hT hu, hT hv, ?_⟩
  -- `induceHomOfLE` is an embedding `G.induce T ↪g G.induce T'`; its map
  -- sends `⟨u, hu⟩ ↦ ⟨u, hT hu⟩`, so it transports reachability.
  have := hr.map (G.induceHomOfLE hT).toHom
  simpa using this

/-- A separator of size `< k` is forbidden in a `k`-vertex-connected
    graph: the connectivity hypothesis applied to the separator's vertex
    set yields the reachability the separator denies, a contradiction. -/
theorem IsKVertexConnected.not_isSeparator {k : ℕ} (hG : IsKVertexConnected G k)
    {S : Finset (Fin n)} (hS : S.card < k) {u v : Fin n}
    (hsep : IsSeparator G S u v) : False := by
  obtain ⟨hu, hv, hnr⟩ := hsep
  exact hnr (hG.2 S hS u v hu hv)

/-! ### The cutset lemma `lem:con` -/

/-- **Lemma `lem:con`** (Gortler–Theran, tex:385-394).

    If `G` on `Fin n` is `(n − D)`-vertex-connected and `D ≤ i + 1`, then
    the `i`-th and `(i+1)`-st vertices in the ordering `σ` are connected by
    a path visiting only the prefix `{σ₀, …, σ_{i+1}}` (the first `i+2`
    vertices, encoded as `{x | (σ.symm x).val ≤ i+1}`).

	    **0-based hypothesis.** The source
    (`lem:con`, tex:387, 1-based) states "if `i ≥ D`"; under 0-based Lean
    indexing the FIRST `lem:later` case is 1-based `i = D`, which is 0-based
    `i.val = D − 1`, i.e. `D ≤ i.val + 1`.  The cutset argument is unchanged:
    the only place the position bound enters is the size estimate
    `|S| = n − (i+2) < n − D ⟺ D < i + 2 ⟺ D ≤ i + 1`, so the lemma stays
    valid with the weaker hypothesis `D ≤ i.val + 1` (a strict strengthening
    of the lemma — existing callers passing `D ≤ i.val` still satisfy it).

    Proof (contrapositive, per the source): if no such within-prefix path
    exists, then the prefix-complement `S = {σ_{i+2}, …, σ_{n-1}}` is a
    cut set separating `σ i` from `σ (i+1)`.  Its size is
    `|S| = n − (i+2) = n − i − 2`.  Since `D ≤ i + 1` we get
    `n − i − 2 < n − D`, so `S` is a separator smaller than the
    connectivity, contradicting `(n−D)`-connectivity. -/
theorem lem_con (D : ℕ) (hconn : IsKVertexConnected G (n - D))
    (σ : Equiv.Perm (Fin n)) (i : Fin n) (hi : D ≤ i.val + 1)
    (hi' : i.val + 1 < n) :
    ReachableWithin G {x | (σ.symm x).val ≤ i.val + 1} (σ i) (σ ⟨i.val + 1, hi'⟩) := by
  classical
  -- The prefix set `P = {x | (σ.symm x).val ≤ i+1}` (first `i+2` vertices).
  set P : Set (Fin n) := {x | (σ.symm x).val ≤ i.val + 1} with hP
  -- The cut set `S = Pᶜ = {x | (σ.symm x).val ≥ i+2}` as a `Finset`.
  set S : Finset (Fin n) := Finset.univ.filter (fun x => i.val + 1 < (σ.symm x).val)
    with hSdef
  -- Endpoints.
  set u : Fin n := σ i with hu
  set v : Fin n := σ ⟨i.val + 1, hi'⟩ with hv
  by_contra hnr
  -- Step 1: `S` is exactly the complement of `P` (as sets).
  have hScompl : (↑S : Set (Fin n)) = Pᶜ := by
    ext x
    simp only [hSdef, hP, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  -- Step 2: endpoints lie in `P`, hence not in `S`.
  have huP : u ∈ P := by
    simp only [hP, hu, Set.mem_setOf_eq, Equiv.symm_apply_apply]; omega
  have hvP : v ∈ P := by
    simp only [hP, hv, Set.mem_setOf_eq, Equiv.symm_apply_apply]; omega
  have huS : u ∉ S := by rw [← Finset.mem_coe, hScompl]; exact fun h => h huP
  have hvS : v ∉ S := by rw [← Finset.mem_coe, hScompl]; exact fun h => h hvP
  -- Step 3: not reachable in `G.induce Sᶜ` (= `G.induce P`).
  have hnr' : ¬ ReachableWithin G (↑S : Set (Fin n))ᶜ u v := by
    rw [hScompl, compl_compl]; exact hnr
  -- So `S` is a separator of `u` from `v`.
  have hsep : IsSeparator G S u v := ⟨huS, hvS, hnr'⟩
  -- Step 4: bound `|S| = n - (i+2) < n - D`.
  -- `S = Pᶜ`, and `|P| = i + 2` (the first `i+2` vertices of the ordering).
  -- Hence `|S| = n - (i+2)`.
  have hcardP : (Finset.univ.filter (fun x => (σ.symm x).val ≤ i.val + 1)).card
      = i.val + 2 := by
    -- `σ.symm` is a bijection, so the number of `x` with `(σ.symm x).val ≤ i+1`
    -- equals the number of `y : Fin n` with `y.val ≤ i+1`.
    have hbij : (Finset.univ.filter (fun x => (σ.symm x).val ≤ i.val + 1)).card
        = (Finset.univ.filter (fun y : Fin n => y.val ≤ i.val + 1)).card := by
      apply Finset.card_bij (fun x _ => σ.symm x)
      · intro x hx
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
          (Finset.mem_filter.mp hx).2
      · intro x₁ _ x₂ _ h; exact σ.symm.injective h
      · intro y hy
        refine ⟨σ y, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Equiv.symm_apply_apply]
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hy
        · simp [Equiv.symm_apply_apply]
    rw [hbij]
    -- Count `y : Fin n` with `y.val ≤ i+1`: biject onto `Finset.range (i+2)`
    -- via `y ↦ y.val` (well-defined since `i+1 < n`).
    have hrange : (Finset.univ.filter (fun y : Fin n => y.val ≤ i.val + 1)).card
        = (Finset.range (i.val + 2)).card := by
      apply Finset.card_bij (fun y _ => y.val)
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        simp only [Finset.mem_range]; omega
      · intro y₁ _ y₂ _ h; exact Fin.val_injective h
      · intro b hb
        simp only [Finset.mem_range] at hb
        refine ⟨⟨b, by omega⟩, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
    rw [hrange, Finset.card_range]
  -- Card of `S`.
  have hcardS : S.card = n - (i.val + 2) := by
    have hPS : S = Finset.univ.filter (fun x => i.val + 1 < (σ.symm x).val) := hSdef
    have : S = Finset.univ \ (Finset.univ.filter (fun x => (σ.symm x).val ≤ i.val + 1)) := by
      rw [hPS]; ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_sdiff, not_le]
    rw [this, Finset.card_sdiff, Finset.card_univ, Fintype.card_fin]
    rw [Finset.inter_univ, hcardP]
  have hSlt : S.card < n - D := by
    rw [hcardS]; omega
  exact hconn.not_isSeparator hSlt hsep

end LSS
