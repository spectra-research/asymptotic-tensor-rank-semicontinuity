/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.LSS.Connectivity
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.LSS.Descent

/-!
# LSS — connectivity supplies the `hindep` hypothesis of the ℚ-descent

This bridge file closes the gap between the **connectivity** hypothesis of the
Lovász–Saks–Schrijver / Gortler–Theran theorem and the explicit `hindep`
hypothesis demanded by the rational descent (`Descent.lean`,
`exists_rat_gor_of_exists_real_gor` / `continuousAt_orthoRetract_of_isGOR`).

## The argument (Vrana–Christandl genmamu tex:215; Gortler–Theran gorProof tex:385-394)

genmamu tex:215 obtains linear independence of the preceding-non-neighbor families
`(f(v))_{v ∈ A_i}` from the bound `|A_i| ≤ d` together with general position. The
bound `|A_i| ≤ d` is exactly where `(n−D)`-vertex-connectivity enters: the standard
graph-theory fact `κ(G) ≤ δ(G)` (vertex-connectivity ≤ minimum degree) gives every
vertex degree `≥ n − D`, hence at most `D − 1` non-neighbors (excluding itself), hence
`|A_i| ≤ D − 1 < D`. A family of `< D` vectors that sits inside general position is
linearly independent (extend to a `D`-subset, apply `IsGP`, restrict).

## Main declaration

* `min_degree_of_isKVertexConnected` — `κ(G) ≤ δ(G)`: an `(n−D)`-vertex-connected graph
  has every vertex of degree `≥ n − D`. (The one genuine graph-theory step.)
* `isKVertexConnected_isGOR_hindep` — the bridge: an `(n−D)`-vertex-connected GOR has
  linearly independent preceding-non-neighbor families — i.e. the exact `hindep`
  hypothesis of `exists_rat_gor_of_exists_real_gor`.
-/

open scoped InnerProductSpace
open RealInnerProductSpace
open SimpleGraph

namespace LSS

variable {n D : ℕ}

/-! ### `κ(G) ≤ δ(G)`: connectivity bounds the minimum degree (genmamu tex:215) -/

/-- **Minimum degree from vertex-connectivity** (standard fact `κ(G) ≤ δ(G)`).
If `G` on `Fin n` is `(n − D)`-vertex-connected, then every vertex has degree `≥ n − D`.

Proof (contrapositive). Suppose some vertex `v` has degree `< n − D`. Then
`S = N(v) = G.neighborFinset v` has `|S| = deg v < n − D`. Since `v ∉ S`, deleting `S`
*isolates* `v`: any `G`-neighbor of `v` lies in `S`, so in `G.induce Sᶜ` the vertex `v`
has no neighbor at all. Hence `v` cannot reach any other vertex `w ∈ Sᶜ`, `w ≠ v`. Such a
`w` exists because `deg v < n − D ≤ n − 1` (using `D ≥ 1`, which follows from
`n − D < n`), so `v` has a genuine non-neighbor. Then `S` separates `v` from `w`,
contradicting `(n − D)`-connectivity via `IsKVertexConnected.not_isSeparator`. -/
theorem min_degree_of_isKVertexConnected {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hconn : IsKVertexConnected G (n - D)) (v : Fin n) :
    n - D ≤ (G.neighborFinset v).card := by
  classical
  by_contra hlt
  push_neg at hlt
  -- `D ≥ 1` and `0 < n` from `n - D < n`.
  have hnD_lt : n - D < n := hconn.1
  have hD1 : 1 ≤ D := by omega
  -- The separator candidate `S = N(v)`, of size `< n - D`.
  set S : Finset (Fin n) := G.neighborFinset v with hSdef
  have hScard : S.card < n - D := hlt
  have hvS : v ∉ S := by rw [hSdef]; exact G.notMem_neighborFinset_self v
  -- There exists a non-neighbor `w ≠ v`: otherwise `S ∪ {v} = univ`, giving
  -- `n ≤ S.card + 1 ≤ (n - D - 1) + 1 = n - D < n`, impossible.
  have hwexists : ∃ w : Fin n, w ≠ v ∧ w ∉ S := by
    by_contra hno
    push_neg at hno
    -- every vertex is `v` or in `S`, so `univ ⊆ insert v S`.
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ insert v S := by
      intro x _
      by_cases hxv : x = v
      · simp [hxv]
      · exact Finset.mem_insert_of_mem (hno x hxv)
    have hcard : n ≤ S.card + 1 := by
      have := Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_fin] at this
      calc n ≤ (insert v S).card := this
        _ ≤ S.card + 1 := Finset.card_insert_le v S
    omega
  obtain ⟨w, hwv, hwS⟩ := hwexists
  -- `S` separates `v` from `w`: in `G.induce Sᶜ` the vertex `v` is isolated.
  have hsep : IsSeparator G S v w := by
    refine ⟨hvS, hwS, ?_⟩
    rintro ⟨hvc, hwc, hreach⟩
    -- `hreach : (G.induce (↑S)ᶜ).Reachable ⟨v, hvc⟩ ⟨w, hwc⟩`, with `v ≠ w`.
    refine hreach.elim_path (fun p => ?_)
    -- The path `p` is non-nil since its endpoints differ.
    have hne : (⟨v, hvc⟩ : ((↑S : Set (Fin n))ᶜ : Set (Fin n))) ≠ ⟨w, hwc⟩ := by
      intro h; exact hwv (congrArg Subtype.val h).symm
    have hnotnil : ¬ p.1.Nil := SimpleGraph.Walk.not_nil_of_ne hne
    -- First dart: `(G.induce Sᶜ).Adj ⟨v,_⟩ p.1.snd`, so `G.Adj v p.1.snd.val`.
    have hadj := SimpleGraph.Walk.adj_snd hnotnil
    rw [SimpleGraph.induce_adj] at hadj
    -- Hence `p.1.snd.val ∈ N(v) = S`; but `p.1.snd.val ∈ Sᶜ`. Contradiction.
    have hmemS : p.1.snd.val ∈ S :=
      (SimpleGraph.mem_neighborFinset G v _).2 hadj
    have hmemSc : p.1.snd.val ∈ (↑S : Set (Fin n))ᶜ := p.1.snd.2
    exact hmemSc hmemS
  exact hconn.not_isSeparator hScard hsep

/-! ### Few non-neighbors, hence small independent families (genmamu tex:215) -/

/-- **Few preceding non-neighbors.** If `G` is `(n − D)`-vertex-connected and `D ≤ n`,
then every vertex has at most `D − 1` preceding non-neighbors, in particular
`(precNonNbr G i).card < D`.

Proof: `precNonNbr G i ⊆ univ \ insert i (N i)` (a preceding non-neighbor is `≠ i` and
non-adjacent to `i`). The right-hand side has card `n − (deg i + 1)`; with
`deg i ≥ n − D` (`min_degree_of_isKVertexConnected`) and `D ≤ n` this is `≤ D − 1 < D`. -/
theorem precNonNbr_card_lt {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hconn : IsKVertexConnected G (n - D)) (hDn : D ≤ n) (i : Fin n) :
    (precNonNbr G i).card < D := by
  classical
  have hdeg : n - D ≤ (G.neighborFinset i).card := min_degree_of_isKVertexConnected hconn i
  -- `precNonNbr G i ⊆ univ \ insert i (N i)`.
  have hsub : precNonNbr G i ⊆ Finset.univ \ insert i (G.neighborFinset i) := by
    intro j hj
    rw [mem_precNonNbr] at hj
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ j, ?_⟩
    rw [Finset.mem_insert, not_or]
    refine ⟨?_, ?_⟩
    · intro h; rw [h] at hj; exact (lt_irrefl _ hj.1)
    · rw [SimpleGraph.mem_neighborFinset]; exact hj.2
  -- Card of the right-hand side.
  have hi_notin : i ∉ G.neighborFinset i := G.notMem_neighborFinset_self i
  have hcard_insert : (insert i (G.neighborFinset i)).card = (G.neighborFinset i).card + 1 :=
    Finset.card_insert_of_notMem hi_notin
  have hcard_sdiff : (Finset.univ \ insert i (G.neighborFinset i)).card
      = n - ((G.neighborFinset i).card + 1) := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      hcard_insert]
  have hle := Finset.card_le_card hsub
  rw [hcard_sdiff] at hle
  -- `s.card ≤ n - (deg + 1)`, `deg ≥ n - D`, `D ≤ n` ⟹ `s.card < D`.
  have hdeg' : (G.neighborFinset i).card + 1 ≤ n := by
    -- `insert i (N i) ⊆ univ`, so its card `= deg + 1 ≤ n`.
    have hins := (insert i (G.neighborFinset i)).card_le_univ
    rw [Fintype.card_fin, hcard_insert] at hins
    exact hins
  omega

/-! ### The bridge: connectivity ⟹ `hindep` (genmamu tex:215) -/

/-- **Bridge lemma — genmamu tex:215.** For an `(n − D)`-vertex-connected graph `G` and a
general-position orthogonal representation `f`, every preceding-non-neighbor family is
linearly independent. This is *exactly* the `hindep` hypothesis consumed by
`continuousAt_orthoRetract_of_isGOR` and `exists_rat_gor_of_exists_real_gor`
(`Descent.lean`). (genmamu tex:215: each family `(f(v))_{v ∈ A_i}` is independent
because `|A_i| ≤ d`.)

Proof: `κ(G) ≤ δ(G)` (`min_degree_of_isKVertexConnected`) forces each vertex to have at
most `D − 1` preceding non-neighbors (`precNonNbr_card_lt`), so `s := precNonNbr G i` has
`|s| < D ≤ n`. Extend `s` to a `D`-subset `t ⊇ s` (`Finset.exists_subsuperset_card_eq`).
General position (`hf.isGP`) makes `(f j)_{j ∈ t}` linearly independent; restricting along
the inclusion `s ⊆ t` (`LinearIndependent.comp` with `Set.inclusion`, as in
`Descent.continuousAt_starProjection_span`) yields independence of `(f j)_{j ∈ s}`.

`D ≤ n` is genuinely required: when `D > n` no `D`-subset of `Fin n` exists, `IsGP` is
vacuous, and the family cannot be extracted. (`D ≥ 1` is automatic from connectivity's
`n − D < n`, but `D ≤ n` is an independent constraint.) -/
theorem isKVertexConnected_isGOR_hindep {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hconn : IsKVertexConnected G (n - D)) (hDn : D ≤ n)
    (f : Fin n → EuclideanSpace ℝ (Fin D)) (hf : IsGOR G f) :
    ∀ i : Fin n,
      LinearIndependent ℝ (fun j : (precNonNbr G i : Set (Fin n)) => f j.val) := by
  classical
  intro i
  -- `s := precNonNbr G i` has card `< D ≤ n`.
  set s : Finset (Fin n) := precNonNbr G i with hsdef
  have hscard : s.card < D := precNonNbr_card_lt hconn hDn i
  -- Extend `s` to a `D`-subset `t`.
  obtain ⟨t, hst, _htuniv, htcard⟩ :=
    Finset.exists_subsuperset_card_eq (s.subset_univ)
      (le_of_lt hscard) (by rw [Finset.card_univ, Fintype.card_fin]; exact hDn)
  -- General position: `(f j)_{j ∈ t}` is linearly independent.
  have htindep : LinearIndependent ℝ (fun j : (t : Set (Fin n)) => f j.val) :=
    hf.isGP t htcard
  -- Restrict along the inclusion `s ⊆ t`.
  have hsub : (s : Set (Fin n)) ⊆ (t : Set (Fin n)) := by
    intro j hj; exact hst hj
  exact htindep.comp (Set.inclusion hsub) (Set.inclusion_injective hsub)

end LSS
