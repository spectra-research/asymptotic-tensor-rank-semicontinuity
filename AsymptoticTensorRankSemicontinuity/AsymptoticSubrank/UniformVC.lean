/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.Degeneration.GenPos
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.Degeneration.SubstrateBridge
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.LSS.CompleteLineGraph
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.BorderSubrank
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.PairUnitKron

/-!
# Corollary 3.5 — uniform Vrana–Christandl achievability for `K_k`

Source:
* Paper Cor 3.5: tex:982-996.
* Vrana–Christandl (arXiv:1603.03964) main theorem + `K_k` instantiation:
  genmamu tex:112-199
  (rate `1/(l-d)`, `d = |E|-λ(H)`, `λ(K_k)=k-1`, `l = |E| = k(k-1)/2`).

The uniform-weights Vrana–Christandl achievability statement is:

  `uniformVC : [Infinite F] → (hk : 3 ≤ k) → (n : ℕ) → (2 ≤ n) →`
  `              (n:ℝ)^(k-1) ≤ asympSubrank (pairUnitKronAll F k n)`

where `pairUnitKronAll F k n := ⊠_{i<j} ⟨n⟩_{i,j}`, the Kronecker product over all
pairs of legs of the rank-`n` pair-unit.  This is the genmamu main theorem
specialized to `H = K_k`: `asympSubrank(GHZ^{K_k}_n) ≥ n^{λ(K_k)} = n^{k-1}`.

## The chain (each step = a lemma)

1. **Identification** `ghzH_eq_pairUnitKron`: the Assembly's `ghzHTensor` for the
   complete-graph incidence equals (or mutually `Restricts` with)
   `pairUnitKronAll F k n`.
2. **GOR wiring** `cgGorData`: package the LSS `L(K_k)` GOR into the integer data
   `c : cgEdge → Fin D → ℤ` the Assembly needs (orthogonality + general position).
3. **Uniform achievability** via `borderSubrankK_ghzH_ge_optimal` /
   `solCount_le_borderSubrank_ghzH` + `borderSubrank_le_asympSubrank`.
4. **Constant washout** via pair-unit Kronecker powers + `asympSubrank_kronPowNat`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset BigOperators Polynomial

namespace Semicontinuity

universe u

open VC.Degeneration LSS

/-! ## The complete-graph incidence instance.

The edge type of `K_k` is the `2`-subsets of `Fin k`; incidence `inc v e := v ∈ e`. -/

/-- The edge type of the complete graph `K_k`: the `2`-subsets of `Fin k`. -/
abbrev cgEdge (k : ℕ) : Type := {s : Finset (Fin k) // s.card = 2}

/-- Incidence for `K_k`: vertex `v` is incident with edge `e = {a,b}` iff `v ∈ e`. -/
def cgInc (k : ℕ) : Fin k → cgEdge k → Prop := fun v e => v ∈ e.val

instance (k : ℕ) (v : Fin k) (e : cgEdge k) : Decidable (cgInc k v e) := by
  unfold cgInc; infer_instance

/-- `Fintype.card (cgEdge k) = k*(k-1)/2` (genmamu `l = |E|`). -/
theorem card_cgEdge (k : ℕ) : Fintype.card (cgEdge k) = k * (k - 1) / 2 :=
  card_pairSubtype k

/-- The edge↔line-graph-vertex bijection `cgEdge k ≃ Fin (k*(k-1)/2)`
    (genmamu:158, the identification of `E` with the line-graph vertices). -/
noncomputable def cgEdgeEquiv (k : ℕ) : cgEdge k ≃ Fin (k * (k - 1) / 2) :=
  (pairEquiv k).symm

@[simp] theorem pairOf_cgEdgeEquiv (k : ℕ) (e : cgEdge k) :
    pairOf k (cgEdgeEquiv k e) = e.val := by
  simp only [cgEdgeEquiv, pairOf, Equiv.apply_symm_apply]

/-! ## Step 2a — general position is preserved by per-vector nonzero scaling.

`LinearIndependent.units_smul`: scaling each vector of an independent family by a
unit preserves independence.  For `IsGP` (real GOR) the scalars are nonzero reals,
i.e. `ℝˣ`. -/

/-- `IsGP` is preserved under per-vector scaling by nonzero reals (genmamu:197,
    "multiplying each vector by the least common denominator … preserves general
    position" — scaling is by units, so linear independence is unchanged). -/
theorem isGP_smul {N D : ℕ} {f : Fin N → EuclideanSpace ℝ (Fin D)}
    (hf : IsGP f) {a : Fin N → ℝ} (ha : ∀ i, a i ≠ 0) :
    IsGP (fun i => a i • f i) := by
  intro s hscard
  -- The restricted family `(a i • f i)_{i ∈ s}` is `(units) • (f i)_{i ∈ s}`.
  have hind : LinearIndependent ℝ (fun i : (s : Set (Fin N)) => f i.val) := hf s hscard
  have h := hind.units_smul (fun i : (s : Set (Fin N)) => (Units.mk0 (a i.val) (ha i.val)))
  convert h using 2

/-! ## Step 2b — the incidence ↔ line-graph-adjacency bridge.

Two distinct `K_k` edges are `edgesIncident` (share a vertex) iff their indices are
adjacent in `L(K_k)` (their pairs intersect).  Hence NON-incident distinct edges map
to NON-adjacent line-graph vertices, where the GOR is orthogonal. -/

/-- `edgesIncident (cgInc k) e f ↔ ¬ Disjoint e.val f.val` (they share a vertex). -/
theorem edgesIncident_iff (k : ℕ) (e f : cgEdge k) :
    edgesIncident (cgInc k) e f ↔ ¬ Disjoint e.val f.val := by
  unfold edgesIncident cgInc
  rw [Finset.not_disjoint_iff]

/-- Every `K_k` edge is incident with itself (its pair is nonempty). -/
theorem edgesIncident_self (k : ℕ) (e : cgEdge k) : edgesIncident (cgInc k) e e := by
  rw [edgesIncident_iff]
  intro hdisj
  have hne : (e.val).Nonempty := by
    rw [← Finset.card_pos, e.2]; norm_num
  obtain ⟨x, hx⟩ := hne
  exact (Finset.disjoint_left.mp hdisj) hx hx

/-- For distinct non-incident edges, the line-graph vertices are non-adjacent. -/
theorem not_adj_of_not_incident (k : ℕ) {e f : cgEdge k} (hef : e ≠ f)
    (hni : ¬ edgesIncident (cgInc k) e f) :
    ¬ (lineCompleteGraph k).Adj (cgEdgeEquiv k e) (cgEdgeEquiv k f) := by
  rw [lineCompleteGraph_adj]
  rintro ⟨_, hnd⟩
  apply hni
  rw [edgesIncident_iff]
  rw [pairOf_cgEdgeEquiv, pairOf_cgEdgeEquiv] at hnd
  exact hnd

/-! ## Step 2c — LCM-clearing the rational GOR to an integer representation.

genmamu:197: "after multiplying each vector by the least common denominator of its
entries, it becomes one in `ℤ^{|E|−λ(H)}`."  We scale each vector `f i` by the
product `den i := ∏_r (qOf i r).den` of the denominators of its rational
coordinates, giving an integer representation `c` and a scaled real GOR `f'` with
`f' (eqv e) r = (c e r : ℝ)`, used to invoke `generalPosition_of_isGP`. -/

variable {k : ℕ}

/-- Chosen rational coordinate of the GOR `f` (from `hrat : (f i) r ∈ range (↑:ℚ→ℝ)`). -/
noncomputable def qCoord {N D : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin D))
    (hrat : ∀ i r, (f i) r ∈ Set.range ((↑) : ℚ → ℝ)) (i : Fin N) (r : Fin D) : ℚ :=
  (hrat i r).choose

theorem qCoord_spec {N D : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin D))
    (hrat : ∀ i r, (f i) r ∈ Set.range ((↑) : ℚ → ℝ)) (i : Fin N) (r : Fin D) :
    ((qCoord f hrat i r : ℚ) : ℝ) = (f i) r :=
  (hrat i r).choose_spec

/-- The per-vector denominator-clearing scalar `den i := ∏_r (qCoord i r).den`. -/
noncomputable def cgDen {N D : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin D))
    (hrat : ∀ i r, (f i) r ∈ Set.range ((↑) : ℚ → ℝ)) (i : Fin N) : ℕ :=
  Finset.univ.prod (fun r => (qCoord f hrat i r).den)

theorem cgDen_pos {N D : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin D))
    (hrat : ∀ i r, (f i) r ∈ Set.range ((↑) : ℚ → ℝ)) (i : Fin N) :
    0 < cgDen f hrat i :=
  Finset.prod_pos (fun r _ => (qCoord f hrat i r).pos)

/-- Cleared rational: `qCoord i r * den i` is an integer (its denominator divides
    `den i`). -/
theorem cgDen_dvd {N D : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin D))
    (hrat : ∀ i r, (f i) r ∈ Set.range ((↑) : ℚ → ℝ)) (i : Fin N) (r : Fin D) :
    (qCoord f hrat i r).den ∣ cgDen f hrat i :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ r)

/-- The integer representation: `c e r := q.num · (den / q.den)`, the LCM-cleared
    coordinate of the line-graph vertex `cgEdgeEquiv k e`.  Since `q.den ∣ den`, this
    integer equals `q · den` as a rational (`cgIntRep_cast`). -/
noncomputable def cgIntRep {N D : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin D))
    (hrat : ∀ i r, (f i) r ∈ Set.range ((↑) : ℚ → ℝ))
    (eqv : cgEdge k ≃ Fin N) (e : cgEdge k) (r : Fin D) : ℤ :=
  (qCoord f hrat (eqv e) r).num *
    ((cgDen f hrat (eqv e) : ℤ) / ((qCoord f hrat (eqv e) r).den : ℤ))

/-- The cleared rational equals its integer numerator: `(c e r : ℚ) = q · den`. -/
theorem cgIntRep_cast {N D : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin D))
    (hrat : ∀ i r, (f i) r ∈ Set.range ((↑) : ℚ → ℝ))
    (eqv : cgEdge k ≃ Fin N) (e : cgEdge k) (r : Fin D) :
    ((cgIntRep f hrat eqv e r : ℤ) : ℚ)
      = qCoord f hrat (eqv e) r * (cgDen f hrat (eqv e) : ℚ) := by
  -- abbreviations
  obtain ⟨t, ht⟩ := cgDen_dvd f hrat (eqv e) r
  set q := qCoord f hrat (eqv e) r with hq
  set m := cgDen f hrat (eqv e) with hm
  -- now `ht : m = q.den * t`
  have hqden : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_nz
  unfold cgIntRep
  rw [← hq, ← hm]
  -- `(m : ℤ) / (q.den : ℤ) = t` since `m = q.den * t`.
  have hdivt : (m : ℤ) / (q.den : ℤ) = (t : ℤ) := by
    rw [ht]; push_cast; rw [Int.mul_ediv_cancel_left _ hqden]
  rw [hdivt]
  -- `(q.num * t : ℚ) = q * m` and `q * q.den = q.num`.
  rw [ht]; push_cast
  have hqq : (q.num : ℚ) = q * (q.den : ℚ) := by
    have hd := Rat.num_div_den q
    have hqden' : ((q.den : ℚ)) ≠ 0 := by exact_mod_cast q.den_nz
    field_simp at hd
    linarith [hd]
  rw [hqq]; ring

/-- The scaled real GOR `f' i := (den i : ℝ) • f i`, whose coordinates are the
    integer representation (`f' (eqv e) r = (c e r : ℝ)`). -/
noncomputable def cgRealRep {N D : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin D))
    (hrat : ∀ i r, (f i) r ∈ Set.range ((↑) : ℚ → ℝ)) (i : Fin N) :
    EuclideanSpace ℝ (Fin D) :=
  (cgDen f hrat i : ℝ) • f i

/-- `cgRealRep f hrat i r = (f i) r · den i`. -/
theorem cgRealRep_apply {N D : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin D))
    (hrat : ∀ i r, (f i) r ∈ Set.range ((↑) : ℚ → ℝ)) (i : Fin N) (r : Fin D) :
    (cgRealRep f hrat i) r = (cgDen f hrat i : ℝ) * (f i) r := by
  unfold cgRealRep
  simp [EuclideanSpace, PiLp]

/-- **Cast compatibility**: `cgRealRep f hrat (eqv e) r = (cgIntRep f hrat eqv e r : ℝ)`.
    The scaled real coordinate equals the integer-cleared coordinate. -/
theorem cgRealRep_eq_cgIntRep {N D : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin D))
    (hrat : ∀ i r, (f i) r ∈ Set.range ((↑) : ℚ → ℝ))
    (eqv : cgEdge k ≃ Fin N) (e : cgEdge k) (r : Fin D) :
    (cgRealRep f hrat (eqv e)) r = ((cgIntRep f hrat eqv e r : ℤ) : ℝ) := by
  rw [cgRealRep_apply]
  have hq : ((cgIntRep f hrat eqv e r : ℤ) : ℚ)
      = qCoord f hrat (eqv e) r * (cgDen f hrat (eqv e) : ℚ) :=
    cgIntRep_cast f hrat eqv e r
  have := congrArg (fun q : ℚ => (q : ℝ)) hq
  push_cast at this
  rw [this, ← qCoord_spec f hrat (eqv e) r]
  push_cast
  ring

/-- `cgIntRep` yields a general-position representation (genmamu:197).  The scaled
    real GOR `cgRealRep` is `IsGP` (scaling preserves general position), and its
    coordinates are the integer cleared values, so `generalPosition_of_isGP`
    transfers to `GeneralPosition (cgIntRep …)`. -/
theorem generalPosition_cgIntRep {N D : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin D))
    (hf : IsGP f) (hrat : ∀ i r, (f i) r ∈ Set.range ((↑) : ℚ → ℝ))
    (eqv : cgEdge k ≃ Fin N) :
    GeneralPosition (cgIntRep f hrat eqv) := by
  have hgp' : IsGP (cgRealRep f hrat) :=
    isGP_smul hf (fun i => by
      have := cgDen_pos f hrat i; positivity)
  exact generalPosition_of_isGP (c := cgIntRep f hrat eqv) (f := cgRealRep f hrat) eqv hgp'
    (fun e r => cgRealRep_eq_cgIntRep f hrat eqv e r)

/-! ## Step 2d — orthogonality of the integer representation.

Non-incident distinct `K_k` edges map to non-adjacent line-graph vertices, where the
GOR `f` (hence the scaled `cgRealRep`) is orthogonal; the dot product of the cleared
integer vectors is therefore zero. -/

/-- `(idot (c e) (c f) : ℝ) = ⟪cgRealRep (eqv e), cgRealRep (eqv f)⟫_ℝ` for the
    integer representation `c = cgIntRep f hrat eqv`. -/
theorem idot_cgIntRep_eq_inner {N D : ℕ} (f : Fin (N) → EuclideanSpace ℝ (Fin D))
    (hrat : ∀ i r, (f i) r ∈ Set.range ((↑) : ℚ → ℝ))
    (eqv : cgEdge k ≃ Fin N) (e e' : cgEdge k) :
    ((idot (cgIntRep f hrat eqv e) (cgIntRep f hrat eqv e') : ℤ) : ℝ)
      = inner ℝ (cgRealRep f hrat (eqv e)) (cgRealRep f hrat (eqv e')) := by
  rw [PiLp.inner_apply]
  unfold idot
  push_cast
  apply Finset.sum_congr rfl
  intro r _
  rw [RCLike.inner_apply, conj_trivial]
  rw [cgRealRep_eq_cgIntRep, cgRealRep_eq_cgIntRep]
  ring

/-- **Orthogonality** of the integer representation (genmamu:150): non-incident
    distinct edges have `⟨c_e, c_f⟩ = 0`. -/
theorem horth_cgIntRep {D : ℕ} (f : Fin (k * (k - 1) / 2) → EuclideanSpace ℝ (Fin D))
    (hf : IsGOR (lineCompleteGraph k) f)
    (hrat : ∀ i r, (f i) r ∈ Set.range ((↑) : ℚ → ℝ)) :
    ∀ e e' : cgEdge k, ¬ edgesIncident (cgInc k) e e' →
      idot (cgIntRep f hrat (cgEdgeEquiv k) e) (cgIntRep f hrat (cgEdgeEquiv k) e') = 0 := by
  intro e e' hni
  -- distinct (a pair is incident with itself)
  have hne : e ≠ e' := by
    rintro rfl; exact hni (edgesIncident_self k e)
  have hvne : cgEdgeEquiv k e ≠ cgEdgeEquiv k e' := fun h => hne ((cgEdgeEquiv k).injective h)
  have hnadj := not_adj_of_not_incident k hne hni
  -- inner product of the (unscaled) GOR vanishes
  have hor : inner ℝ (f (cgEdgeEquiv k e)) (f (cgEdgeEquiv k e')) = (0 : ℝ) :=
    hf.isOR (cgEdgeEquiv k e) (cgEdgeEquiv k e') hvne hnadj
  -- scaled inner product also vanishes
  have hscaled : inner ℝ (cgRealRep f hrat (cgEdgeEquiv k e))
      (cgRealRep f hrat (cgEdgeEquiv k e')) = (0 : ℝ) := by
    unfold cgRealRep
    rw [inner_smul_left, inner_smul_right, hor]
    simp
  have hreal := idot_cgIntRep_eq_inner f hrat (cgEdgeEquiv k) e e'
  rw [hscaled] at hreal
  exact_mod_cast hreal

/-! ## Step 2e — the index-arithmetic side conditions (genmamu:159).

`D = (k-1)(k-2)/2`, `|E| = k(k-1)/2`.  `hDcard : D ≤ |E|` is `dim_le_card`.  The
deficiency bound `hdef v : |{e | ¬ v ∈ e}| ≤ D` is an equality: the 2-subsets not
containing `v` are exactly the 2-subsets of the `(k-1)`-element complement,
numbering `C(k-1,2) = (k-1)(k-2)/2 = D`. -/

/-- The 2-subsets not containing `v` number `C(k-1,2) = (k-1)(k-2)/2`. -/
theorem card_nonInc_cgEdge (k : ℕ) (v : Fin k) :
    (Finset.univ.filter (fun e : cgEdge k => ¬ cgInc k v e)).card
      = (k - 1) * (k - 2) / 2 := by
  classical
  -- Map each non-incident edge `e` to its 2-subset `e.val ⊆ univ \ {v}`.
  have hbij : (Finset.univ.filter (fun e : cgEdge k => ¬ cgInc k v e)).card
      = ((Finset.univ \ {v}).powersetCard 2).card := by
    apply Finset.card_bij (fun e _ => e.val)
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, cgInc] at he
      rw [Finset.mem_powersetCard]
      refine ⟨?_, e.2⟩
      intro x hx
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, fun hxv => he ?_⟩
      rw [Finset.mem_singleton] at hxv
      rwa [hxv] at hx
    · intro a _ b _ hab; exact Subtype.ext hab
    · intro s hs
      rw [Finset.mem_powersetCard] at hs
      obtain ⟨hsub, hcard⟩ := hs
      refine ⟨⟨s, hcard⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, cgInc]
      intro hv
      have := hsub hv
      rw [Finset.mem_sdiff, Finset.mem_singleton] at this
      exact this.2 rfl
  rw [hbij, Finset.card_powersetCard]
  have hcompl : (Finset.univ \ {v} : Finset (Fin k)).card = k - 1 := by
    rw [Finset.card_univ_diff, Fintype.card_fin, Finset.card_singleton]
  rw [hcompl, Nat.choose_two_right]
  congr 2

/-! ## Step 2f — the two `BddAbove` side conditions.

The Assembly headline and the substrate bridge require the `borderSubrankK` /
`borderSubrank` defining sets to be bounded above.  Both follow from the flattening
bound `borderRestricts_le_flatRank` (`BorderSubrank.lean:296`): any border restriction
`s` is `≤ flatRank` of the (reindexed) GHZ tensor along a 2-leg cut, which exists for
`k ≥ 2`. -/

open VC.Degeneration in
/-- `BddAbove` of the `KTensor`-side `BorderRestricts` set for `ghzH_asKTensor`
    (`hbddK`).  Bounded by `flatRank (ghzH_asKTensor) {i₀}` for a fixed leg `i₀`. -/
theorem bddAbove_borderRestricts_ghzH {F : Type u} [Field F]
    {E : Type*} [Fintype E] [DecidableEq E]
    (inc : Fin k → E → Prop) [∀ v e, Decidable (inc v e)] {n : ℕ} (hn : 1 ≤ n)
    (hk : 2 ≤ k) :
    BddAbove { s : ℕ | ∃ hs : 0 < s,
      BorderRestricts (F := F) s hs (ghzH_asKTensor inc hn) } := by
  classical
  have hk0 : 0 < k := by omega
  have hk1 : 1 < k := by omega
  refine ⟨flatRank (ghzH_asKTensor (F := F) inc hn) {⟨0, hk0⟩}, ?_⟩
  rintro s ⟨hs, hBR⟩
  refine borderRestricts_le_flatRank hs {⟨0, hk0⟩} (i₁ := ⟨1, hk1⟩)
    (Finset.mem_singleton_self _) ?_ hBR
  rw [Finset.mem_singleton]
  intro h
  have h2 := congrArg Fin.val h
  simp at h2

/-! ## Step 2g — incident owner functions for `K_k` (genmamu:150).

`absLocalWeight` needs, for each edge `e`, an incident vertex `edgeOwner e`, and for
each pair `e,f` with `⟨c_e,c_f⟩ ≠ 0` a common incident vertex `pairOwner e f`.  For
`K_k` we pick `edgeOwner e :=` the minimal vertex of `e`, and `pairOwner e f :=` a
common vertex (exists since `⟨c_e,c_f⟩ ≠ 0 ⟹ e,f` incident by `horth`). -/

/-- A chosen vertex of the (nonempty) edge `e`. -/
noncomputable def cgEdgeOwner (k : ℕ) (e : cgEdge k) : Fin k :=
  (by
    have : (e.val).Nonempty := by rw [← Finset.card_pos, e.2]; norm_num
    exact this.choose)

theorem cgEdgeOwner_inc (k : ℕ) (e : cgEdge k) : cgInc k (cgEdgeOwner k e) e := by
  unfold cgEdgeOwner cgInc
  exact (by
    have h : (e.val).Nonempty := by rw [← Finset.card_pos, e.2]; norm_num
    exact h.choose_spec)

/-- A chosen common vertex of `e` and `f` when they are incident; junk (`cgEdgeOwner e`)
    otherwise. -/
noncomputable def cgPairOwner (k : ℕ) (e f : cgEdge k) : Fin k := by
  classical
  exact if h : edgesIncident (cgInc k) e f then h.choose else cgEdgeOwner k e

theorem cgPairOwner_inc (k : ℕ) {e f : cgEdge k}
    (h : edgesIncident (cgInc k) e f) :
    cgInc k (cgPairOwner k e f) e ∧ cgInc k (cgPairOwner k e f) f := by
  classical
  unfold cgPairOwner
  rw [dif_pos h]
  exact h.choose_spec

open VC.Degeneration in
/-- `BddAbove` of the `TensorK`-side `borderSubrankK` body set (`hbddT`).  Each member
    `s > 0` transports (via `borderRestricts_of_TensorK`) to a `KTensor`-side
    `BorderRestricts (ghzH_asKTensor)`, bounded by `bddAbove_borderRestricts_ghzH`. -/
theorem bddAbove_borderSubrankK_ghzH {F : Type u} [Field F]
    {E : Type*} [Fintype E] [DecidableEq E]
    (inc : Fin k → E → Prop) [∀ v e, Decidable (inc v e)] {n : ℕ} (hn : 1 ≤ n)
    (hk : 2 ≤ k) :
    BddAbove {s : ℕ | ∃ (N : ℕ)
      (A : (v : Fin k) → Fin s → localIdx inc n v → Polynomial F),
      (∀ ρ : Fin k → Fin s, ∀ l : ℕ, l < N →
        (∑ f : (v : Fin k) → localIdx inc n v,
          (∏ v, A v (ρ v) (f v)) *
            Polynomial.C (ghzHTensor (F := F) inc n f)).coeff l = 0) ∧
      (∀ ρ : Fin k → Fin s,
        (∑ f : (v : Fin k) → localIdx inc n v,
          (∏ v, A v (ρ v) (f v)) *
            Polynomial.C (ghzHTensor (F := F) inc n f)).coeff N =
        TensorK.identityK F k s ρ)} := by
  classical
  obtain ⟨B, hB⟩ := bddAbove_borderRestricts_ghzH (F := F) inc hn hk
  refine ⟨B, ?_⟩
  rintro s ⟨N, A, hvanish, hident⟩
  rcases Nat.eq_zero_or_pos s with hs0 | hs
  · subst hs0; exact Nat.zero_le _
  · -- transport to a K-side BorderRestricts witness
    have hBR : BorderRestricts (F := F) s hs (ghzH_asKTensor inc hn) :=
      borderRestricts_of_TensorK (ghzHEquiv inc hn) (ghzHTensor (F := F) inc n)
        hs A hvanish hident
    exact hB ⟨hs, hBR⟩

/-! ## Step 3 — the per-`n` achievability border bound for `K_k` (genmamu:150-189).

Combining the above at the `K_k` instance: the LSS `L(K_k)` GOR
(`exists_rat_gor_lineCompleteGraph`) gives the integer representation `c` (step 2),
which proves the Assembly's orthogonality + general-position hypotheses; then
`solCount_le_borderSubrank_ghzH` + `exists_g_solCount_ge` yield

  `n^|E| ≤ (2·C·n)^D · borderSubrank (ghzH_asKTensor cgInc hn)`,

with `|E| = k(k-1)/2`, `D = (k-1)(k-2)/2` (genmamu:181).  `borderSubrank_le_asympSubrank`
lifts the RHS to `asympSubrank`. -/

/-- **The complete-graph integer GOR data**: the integer representation `c`, its
    orthogonality and general position, packaged from the LSS `L(K_k)` rational GOR. -/
theorem exists_cgGorData (hk : 3 ≤ k) :
    ∃ (c : cgEdge k → Fin ((k - 1) * (k - 2) / 2) → ℤ),
      (∀ e f : cgEdge k, ¬ edgesIncident (cgInc k) e f → idot (c e) (c f) = 0) ∧
      (∀ (n : ℕ) (g : Fin ((k - 1) * (k - 2) / 2) → ℤ),
        GeneralPositionInjective (k := k) (cgInc k) c n g) := by
  classical
  obtain ⟨f, hgor, hrat⟩ := exists_rat_gor_lineCompleteGraph k hk
  refine ⟨cgIntRep f hrat (cgEdgeEquiv k), ?_, ?_⟩
  · exact horth_cgIntRep f hgor hrat
  · intro n g
    have hgp : GeneralPosition (cgIntRep f hrat (cgEdgeEquiv k)) :=
      generalPosition_cgIntRep f hgor.isGP hrat (cgEdgeEquiv k)
    have hDcard : (k - 1) * (k - 2) / 2 ≤ Fintype.card (cgEdge k) := by
      rw [card_cgEdge]; exact dim_le_card k
    have hdef : ∀ v₀ : Fin k,
        (Finset.univ.filter (fun e => ¬ cgInc k v₀ e)).card ≤ (k - 1) * (k - 2) / 2 := by
      intro v₀; rw [card_nonInc_cgEdge]
    exact generalPositionInjective_of_generalPosition (cgInc k) hgp hDcard hdef n g

/-! ## `pairUnitKronAll` — the Kronecker product over all pairs of rank-`n` pair-units.

`pairUnitKronAll F k n := ⊠_{i<j} ⟨n⟩_{i,j}` (the paper's RHS of tex:984 with all
`q_{i,j} = n`).  Built with the `kronFoldl` / `TT.of` machinery of `PairUnitKron.lean`,
over the list of ordered pairs `i < j` of `Fin k`.  For `k ≥ 2` this list is nonempty,
so we fold over `p₀ :: ps`. -/

/-- The list of ordered pairs `(i,j)` with `i < j` in `Fin k`. -/
noncomputable def cgPairsList (k : ℕ) : List (Fin k × Fin k) :=
  (Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2)).toList

/-- The bundled pair-unit `⟨n⟩_{p.1,p.2}` (junk rank-`1` unit if `p.1 = p.2` or
    `n = 0`), used as the per-pair Kronecker factor. -/
noncomputable def pairUnitTT {F : Type u} [Field F] {k : ℕ} (n : ℕ)
    (p : Fin k × Fin k) : TT F k := by
  classical
  exact if h : p.1 ≠ p.2 ∧ 1 ≤ n then
    TT.of (unitPairTensor (F := F) ⟨n, h.2⟩ p.1 p.2 h.1)
  else TT.of (unitTensor F (k := k) (1 : ℕ+))

/-- **`pairUnitKronAll`** `:= ⊠_{i<j} ⟨n⟩_{i,j}`, the Kronecker product over all pairs
    of legs of the rank-`n` pair-unit (paper tex:984 with all `q_{i,j} = n`).

    Total `TT F k`-valued definition: the left-nested `kronFoldl` over the pairs list
    `cgPairsList k`, with a rank-`1` unit base (so the fold is well-defined for the
    empty list); for `k ≥ 2`, `n ≥ 1` this is the genuine `⊠_{i<j} ⟨n⟩_{i,j}` up to the
    extra `⟨1⟩` base factor (which is the Kronecker identity).  Its `KTensor` is the
    second projection. -/
noncomputable def pairUnitKronAll (F : Type u) [Field F] (k n : ℕ) : TT F k :=
  kronFoldl (TT.of (unitTensor F (k := k) (1 : ℕ+)))
    ((cgPairsList k).map (pairUnitTT n))

/-! ## Step 4a — the constant-overhead washout.

The amplified achievability bound has a *constant* overhead `(2C)^D` independent of
the power `m` (the `n^D` factors cancel `|E| − D = k−1`).  So the washout is the
clean `s^m ≤ K · Q^m ⟹ s ≤ Q` (take `m`-th roots; `K^{1/m} → 1`). -/

/-- **Constant-overhead washout**: if `s^m ≤ K · Q^m` for all `m ≥ 1` (with `s, Q ≥ 0`
    reals and `K` a fixed positive real), then `s ≤ Q`.  Take `m`-th roots:
    `s ≤ K^{1/m} · Q → Q` since `K^{1/m} → 1`. -/
theorem washout_const_le {s Q K : ℝ} (hs : 0 ≤ s) (hQ : 0 ≤ Q) (hK : 0 < K)
    (hbound : ∀ m : ℕ, 1 ≤ m → s ^ m ≤ K * Q ^ m) :
    s ≤ Q := by
  -- `K^{1/m} → 1` via `K^{1/m} = exp(log K / m)` and `log K / m → 0`.
  have htendK : Filter.Tendsto (fun m : ℕ => K ^ ((1 : ℝ) / (m : ℝ)))
      Filter.atTop (nhds 1) := by
    have hlog : Filter.Tendsto (fun m : ℕ => Real.log K * ((1 : ℝ) / (m : ℝ)))
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun m : ℕ => (1 : ℝ) / (m : ℝ))
          Filter.atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
      have := h1.const_mul (Real.log K)
      simpa using this
    have hexp := (Real.continuous_exp.tendsto 0).comp hlog
    rw [Real.exp_zero] at hexp
    have hrw : (Real.exp ∘ fun m : ℕ => Real.log K * ((1 : ℝ) / (m : ℝ)))
        =ᶠ[Filter.atTop] (fun m : ℕ => K ^ ((1 : ℝ) / (m : ℝ))) := by
      filter_upwards with m
      simp only [Function.comp_apply]
      rw [Real.rpow_def_of_pos hK, mul_comm]
    rw [Filter.tendsto_congr' hrw] at hexp
    exact hexp
  -- The comparison sequence `K^{1/m} · Q → Q`.
  have htend : Filter.Tendsto (fun m : ℕ => K ^ ((1 : ℝ) / (m : ℝ)) * Q)
      Filter.atTop (nhds Q) := by
    have := htendK.mul_const Q; simpa using this
  refine ge_of_tendsto htend ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with m hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hexp_nonneg : (0 : ℝ) ≤ (1 : ℝ) / (m : ℝ) := by positivity
  have hb := hbound m hm
  have hmono := Real.rpow_le_rpow (by positivity) hb hexp_nonneg
  have hlhs : (s ^ m) ^ ((1 : ℝ) / (m : ℝ)) = s := by
    rw [← Real.rpow_natCast s m, ← Real.rpow_mul hs, mul_one_div,
      div_self (ne_of_gt hmpos), Real.rpow_one]
  have hrhs : (K * Q ^ m) ^ ((1 : ℝ) / (m : ℝ))
      = K ^ ((1 : ℝ) / (m : ℝ)) * Q := by
    rw [Real.mul_rpow hK.le (by positivity)]
    congr 1
    rw [← Real.rpow_natCast Q m, ← Real.rpow_mul hQ, mul_one_div,
      div_self (ne_of_gt hmpos), Real.rpow_one]
  rw [hlhs, hrhs] at hmono
  exact hmono

/-- **`asympSubrank` is a `∼ₜ`-invariant**: equivalent tensors have equal asymptotic
    subrank.  Via `asympSubrank_eq_abstract` (both equal the abstract `asympSubrank` of
    `TensorClass.mk`, which is `∼ₜ`-invariant by `TensorClass.mk_eq_of_equiv`). -/
theorem asympSubrank_congr {F : Type u} [Field F] [NeZero k] (hk : 2 ≤ k)
    {d d' : Fin k → ℕ+} {S : KTensor F d} {T : KTensor F d'}
    (h : (⟨d, S⟩ : TT F k).2 ∼ₜ (⟨d', T⟩ : TT F k).2) :
    asympSubrank S = asympSubrank T := by
  rw [asympSubrank_eq_abstract hk S, asympSubrank_eq_abstract hk T]
  congr 1
  exact TensorClass.mk_eq_of_equiv h

/-- **Per-leg-equiv restriction**: given per-leg bijections `e ℓ : Fin (dS ℓ) ≃ Fin (dT ℓ)`
    under which the entries match (`S idx = T (fun ℓ => e ℓ (idx ℓ))`), the tensor `S`
    restricts to `T`.  The restriction matrix for leg `ℓ` is the permutation matrix
    `if e ℓ row = col then 1 else 0`; the contraction collapses by `Finset.sum_eq_single`
    at `fun ℓ => e ℓ (jdx ℓ)` (the analogue of `Restricts.of_eq_cast` with arbitrary
    leg-equivs in place of `Fin.cast`). -/
theorem restricts_of_forall_legEquiv {F : Type u} [Field F] {k : ℕ} {dS dT : Fin k → ℕ+}
    {S : KTensor F dS} {T : KTensor F dT}
    (e : ∀ ℓ : Fin k, Fin (dS ℓ) ≃ Fin (dT ℓ))
    (hval : ∀ idx : (∀ ℓ : Fin k, Fin (dS ℓ)), S idx = T (fun ℓ => e ℓ (idx ℓ))) :
    Restricts S T := by
  classical
  refine ⟨fun ℓ row col => if e ℓ row = col then (1 : F) else 0, ?_⟩
  intro jdx
  let idx0 : ∀ ℓ : Fin k, Fin (dT ℓ) := fun ℓ => e ℓ (jdx ℓ)
  rw [Finset.sum_eq_single idx0]
  · rw [hval jdx]
    have hprod : (∏ ℓ : Fin k, (if e ℓ (jdx ℓ) = idx0 ℓ then (1 : F) else 0)) = 1 := by
      apply Finset.prod_eq_one
      intro ℓ _
      simp [idx0]
    rw [hprod, one_mul]
  · intro idx _ hidx
    have hne : ∃ ℓ : Fin k, e ℓ (jdx ℓ) ≠ idx ℓ := by
      by_contra h
      push_neg at h
      exact hidx (funext fun ℓ => (h ℓ).symm)
    obtain ⟨ℓ, hℓ⟩ := hne
    have hzero : (if e ℓ (jdx ℓ) = idx ℓ then (1 : F) else 0) = 0 := by simp [hℓ]
    have hprod_zero :
        (∏ j : Fin k, (if e j (jdx j) = idx j then (1 : F) else 0)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ ℓ) hzero
    rw [hprod_zero, zero_mul]
  · intro hnot; exact (hnot (Finset.mem_univ _)).elim

/-- **Per-leg-equiv tensor-equivalence**: per-leg bijections matching entries give
    `S ∼ₜ T` (mutual `Restricts` via `restricts_of_forall_legEquiv` and its inverse). -/
theorem restrictsEquiv_of_forall_legEquiv {F : Type u} [Field F] {k : ℕ} {dS dT : Fin k → ℕ+}
    {S : KTensor F dS} {T : KTensor F dT}
    (e : ∀ ℓ : Fin k, Fin (dS ℓ) ≃ Fin (dT ℓ))
    (hval : ∀ idx : (∀ ℓ : Fin k, Fin (dS ℓ)), S idx = T (fun ℓ => e ℓ (idx ℓ))) :
    S ∼ₜ T := by
  refine ⟨restricts_of_forall_legEquiv e hval, ?_⟩
  refine restricts_of_forall_legEquiv (fun ℓ => (e ℓ).symm) ?_
  intro idx
  rw [hval (fun ℓ => (e ℓ).symm (idx ℓ))]
  simp

/-! ### Local finite reindexing for GHZ Kronecker products. -/

open VC.Degeneration in
/-- A local `Fin (n*N)` assignment is the same as a pair of local assignments,
coordinatewise through `finProdFinEquiv`. -/
noncomputable def localIdxProdEquiv {E : Type*} [Fintype E] [DecidableEq E] {k : ℕ}
    (inc : Fin k → E → Prop) [∀ v e, Decidable (inc v e)]
    (n N : ℕ) (v : Fin k) :
    localIdx inc (n * N) v ≃ localIdx inc n v × localIdx inc N v :=
  (Equiv.piCongrRight (fun _ : {e : E // inc v e} => finProdFinEquiv.symm)).trans
    (Equiv.arrowProdEquivProdArrow _ _ _)

open VC.Degeneration in
theorem ghzHTensor_prod_iff {E : Type*} [Fintype E] [DecidableEq E] {k : ℕ}
    (inc : Fin k → E → Prop) [∀ v e, Decidable (inc v e)]
    (n N : ℕ) (f : (v : Fin k) → localIdx inc n v)
    (g : (v : Fin k) → localIdx inc N v) :
    (∃ h : E → Fin (n * N), ∀ v : Fin k, ∀ e : {e : E // inc v e},
        (localIdxProdEquiv inc n N v).symm (f v, g v) e = h e.1)
      ↔
    (∃ i : E → Fin n, ∀ v : Fin k, ∀ e : {e : E // inc v e}, f v e = i e.1) ∧
      (∃ j : E → Fin N, ∀ v : Fin k, ∀ e : {e : E // inc v e}, g v e = j e.1) := by
  classical
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨?_, ?_⟩
    · refine ⟨fun e => (finProdFinEquiv.symm (h e)).1, ?_⟩
      intro v e
      have heq := congrArg (fun x => (finProdFinEquiv.symm x).1) (hh v e)
      simpa [localIdxProdEquiv] using heq
    · refine ⟨fun e => (finProdFinEquiv.symm (h e)).2, ?_⟩
      intro v e
      have heq := congrArg (fun x => (finProdFinEquiv.symm x).2) (hh v e)
      simpa [localIdxProdEquiv] using heq
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    refine ⟨fun e => finProdFinEquiv (i e, j e), ?_⟩
    intro v e
    simp [localIdxProdEquiv, hi v e, hj v e]

open VC.Degeneration in
/-- One GHZ Kronecker step: `GHZ_n ⊠ GHZ_N` is `GHZ_{n*N}` after the coordinatewise
product reindex on every incident edge. -/
theorem ghzH_kron_step_equiv {F : Type u} [Field F] {E : Type*} [Fintype E]
    [DecidableEq E] {k : ℕ} (inc : Fin k → E → Prop) [∀ v e, Decidable (inc v e)]
    {n N : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N) (hprod : 1 ≤ n * N) :
    (ghzH_asKTensor (F := F) inc hn ⊠ ghzH_asKTensor (F := F) inc hN)
      ∼ₜ ghzH_asKTensor (F := F) inc hprod := by
  classical
  refine restrictsEquiv_of_forall_legEquiv ?e ?hval
  · intro v
    exact (kronDecodeEquiv.trans
      ((ghzHEquiv inc hn v).symm.prodCongr (ghzHEquiv inc hN v).symm)).trans
        ((localIdxProdEquiv inc n N v).symm.trans (ghzHEquiv inc hprod v))
  · intro idx
    unfold ghzH_asKTensor reindexKTensor
    rw [kron_apply]
    let f : (v : Fin k) → localIdx inc n v :=
      fun v => (ghzHEquiv inc hn v).symm (kronDecodeL (idx v))
    let g : (v : Fin k) → localIdx inc N v :=
      fun v => (ghzHEquiv inc hN v).symm (kronDecodeR (idx v))
    have harg : (fun v : Fin k =>
        (ghzHEquiv inc hprod v).symm
          ((((kronDecodeEquiv.trans
            ((ghzHEquiv inc hn v).symm.prodCongr (ghzHEquiv inc hN v).symm)).trans
              ((localIdxProdEquiv inc n N v).symm.trans (ghzHEquiv inc hprod v)))
            (idx v)))) =
        fun v => (localIdxProdEquiv inc n N v).symm (f v, g v) := by
      funext v
      simp only [Equiv.trans_apply, Equiv.prodCongr_apply, kronDecodeEquiv_apply]
      rw [Equiv.symm_apply_apply]
      rfl
    rw [harg]
    unfold ghzHTensor
    have hpiff := ghzHTensor_prod_iff inc n N f g
    by_cases hp : ∃ i : E → Fin n, ∀ v : Fin k, ∀ e : {e : E // inc v e}, f v e = i e.1
    · by_cases hq : ∃ j : E → Fin N, ∀ v : Fin k, ∀ e : {e : E // inc v e}, g v e = j e.1
      · rw [if_pos hp, if_pos hq, if_pos (hpiff.mpr ⟨hp, hq⟩)]
        simp
      · rw [if_pos hp, if_neg hq]
        have hr : ¬ ∃ h : E → Fin (n * N), ∀ v : Fin k, ∀ e : {e : E // inc v e},
            (localIdxProdEquiv inc n N v).symm (f v, g v) e = h e.1 := by
          intro hr
          exact hq (hpiff.mp hr).2
        rw [if_neg hr]
        simp
    · have hr : ¬ ∃ h : E → Fin (n * N), ∀ v : Fin k, ∀ e : {e : E // inc v e},
          (localIdxProdEquiv inc n N v).symm (f v, g v) e = h e.1 := by
        intro hr
        exact hp (hpiff.mp hr).1
      rw [if_neg hp, if_neg hr]
      simp

/-! ## Step 4 + Step 1 — the final uniform achievability.

The two Kronecker-reindex facts are pure finite identities (genmamu:152-156, the
`GHZ^H_n` multiple-sum form), each an honest finite computation:

* **`ghzH_kronPow_equiv`** (step 4, washout power identity): the `(m+1)`-fold Kronecker
  power of `ghzH^{K_k}_n` is `∼ₜ`-equivalent to `ghzH^{K_k}_{n^{m+1}}`.  This is the
  per-leg reindex `(({e//v∈e} → Fin n) → ...)^{×(m+1)} ≃ ({e//v∈e} → Fin n^{m+1})`
  (`Fin n × ⋯ × Fin n ≃ Fin n^{m+1}` on each incident-edge coordinate), under which the
  diagonal-consistency entry is preserved.  Combined with `asympSubrank_kronPowNat`
  (T2, proved) it gives the power law `asympSubrank(ghzH_n)^{m+1} =
  asympSubrank(ghzH_{n^{m+1}})`.

* **`pairUnitKronAll_equiv_ghzH`** (step 1, identification): the all-pairs pair-unit
  Kronecker product `⊠_{i<j} ⟨n⟩_{i,j}` is `∼ₜ`-equivalent to `ghzH^{K_k}_n` (both have
  leg `v` of dimension `n^{k-1}` indexed by the pairs incident with `v`, entry =
  per-pair agreement / global consistency); a leg-index reindex via
  `{e // v ∈ e} ≃ (incident pairs)`.

Given these two, the genmamu achievability `asympSubrank(ghzH_n) ≥ n^{k-1}` (washout of
`asympSubrank_ghzH_achievability` with the constant overhead `(2C)^D`,
`washout_const_le`) transfers to `pairUnitKronAll` via `asympSubrank_congr`. -/

/-- **Step 4 power identity (genmamu:152-156)**: the `(m+1)`-fold Kronecker
    power of `ghzH^{K_k}_n` equals `ghzH^{K_k}_{n^{m+1}}` up to `∼ₜ`.  A per-leg
    `Fin n^{m+1} ≃ (Fin n)^{m+1}` reindex on each incident-edge coordinate; the
    diagonal-consistency entry is preserved. -/
theorem ghzH_kronPow_equiv {F : Type u} [Field F] (hk : 3 ≤ k) {n : ℕ} (hn : 1 ≤ n)
    (m : ℕ) (hnm : 1 ≤ n ^ (m + 1)) :
    (⟨_, kronPowNat (ghzH_asKTensor (F := F) (cgInc k) hn) m⟩ : TT F k).2
      ∼ₜ (⟨_, ghzH_asKTensor (F := F) (cgInc k) hnm⟩ : TT F k).2 := by
  classical
  induction m with
  | zero =>
      have hnm' : 1 ≤ n := by simpa using hnm
      have hproof : hnm' = hn := Subsingleton.elim _ _
      convert (RestrictsEquiv.refl (ghzH_asKTensor (F := F) (cgInc k) hn)) using 2
      · simp
      · simp
  | succ m ih =>
      let T := ghzH_asKTensor (F := F) (cgInc k) hn
      have hNm : 1 ≤ n ^ (m + 1) := Nat.one_le_pow (m + 1) n hn
      have hprod : 1 ≤ n ^ (m + 1) * n := by
        simpa [pow_succ] using hnm
      have hcongr :
          (kronPowNat T m ⊠ T)
            ∼ₜ (ghzH_asKTensor (F := F) (cgInc k) hNm ⊠ T) :=
        RestrictsEquiv.kron_congr (ih hNm) (RestrictsEquiv.refl T)
      have hstep :
          (ghzH_asKTensor (F := F) (cgInc k) hNm ⊠ T)
            ∼ₜ ghzH_asKTensor (F := F) (cgInc k) hprod :=
        ghzH_kron_step_equiv (F := F) (cgInc k) hNm hn hprod
      simpa [T, kronPowNat, pow_succ] using hcongr.trans hstep

/-! ### Partial complete-graph GHZ over an edge subset (for the single-edge induction).

`pairUnitKronAll = ⊠_{i<j} ⟨n⟩_{i,j}` is built up one pair-unit at a time.  To match it
to `ghzH`, we induct on the set of pairs (= edges) already multiplied in, tracking the
*partial* GHZ `ghzH_asKTensor (cgIncOn S)`, whose incidence sees only the edges in `S`.
Adding one disjoint edge `e₀ = {i,j}` multiplies by the pair-unit `⟨n⟩_{i,j}`; both factors
are then GHZ-shaped and the merge is the disjoint-edge GHZ-union (same logic as
`ghzH_kron_step_equiv`, now over disjoint edge sets at fixed `n`). -/

/-- Incidence restricted to a subset `S ⊆ cgEdge k` of edges. -/
def cgIncOn {k : ℕ} (S : Finset (cgEdge k)) : Fin k → cgEdge k → Prop :=
  fun v e => e ∈ S ∧ v ∈ e.val

instance {k : ℕ} (S : Finset (cgEdge k)) (v : Fin k) (e : cgEdge k) :
    Decidable (cgIncOn S v e) := by unfold cgIncOn; infer_instance

open VC.Degeneration in
/-- Dropping the vacuous `e ∈ univ` conjunct in the partial complete-graph GHZ gives
    the unrestricted complete-graph GHZ. -/
theorem ghzH_cgIncOn_univ_equiv_cgInc {F : Type u} [Field F] {k n : ℕ} (hn : 1 ≤ n) :
    ghzH_asKTensor (F := F) (cgIncOn (Finset.univ : Finset (cgEdge k))) hn
      ∼ₜ ghzH_asKTensor (F := F) (cgInc k) hn := by
  classical
  let edgeDrop (v : Fin k) :
      {e : cgEdge k // cgIncOn (Finset.univ : Finset (cgEdge k)) v e}
        ≃ {e : cgEdge k // cgInc k v e} :=
    Equiv.subtypeEquivRight (fun e : cgEdge k => by
      simp [cgIncOn, cgInc])
  let localDrop (v : Fin k) :
      localIdx (cgIncOn (Finset.univ : Finset (cgEdge k))) n v
        ≃ localIdx (cgInc k) n v :=
    Equiv.arrowCongr (edgeDrop v) (Equiv.refl (Fin n))
  refine restrictsEquiv_of_forall_legEquiv ?e ?hval
  · intro v
    exact (ghzHEquiv (cgIncOn (Finset.univ : Finset (cgEdge k))) hn v).symm.trans
      ((localDrop v).trans (ghzHEquiv (cgInc k) hn v))
  · intro idx
    unfold ghzH_asKTensor reindexKTensor ghzHTensor
    let fOn : (v : Fin k) → localIdx (cgIncOn (Finset.univ : Finset (cgEdge k))) n v :=
      fun v => (ghzHEquiv (cgIncOn (Finset.univ : Finset (cgEdge k))) hn v).symm (idx v)
    let f : (v : Fin k) → localIdx (cgInc k) n v :=
      fun v => localDrop v (fOn v)
    have harg :
        (fun v : Fin k =>
          (ghzHEquiv (cgInc k) hn v).symm
            (((ghzHEquiv (cgIncOn (Finset.univ : Finset (cgEdge k))) hn v).symm.trans
              ((localDrop v).trans (ghzHEquiv (cgInc k) hn v))) (idx v))) = f := by
      funext v
      simp [f, fOn, localDrop]
    rw [harg]
    have hiff :
        (∃ i : cgEdge k → Fin n,
          ∀ v : Fin k, ∀ e : {e : cgEdge k // cgIncOn (Finset.univ : Finset (cgEdge k)) v e},
            fOn v e = i e.1)
        ↔
        (∃ i : cgEdge k → Fin n,
          ∀ v : Fin k, ∀ e : {e : cgEdge k // cgInc k v e}, f v e = i e.1) := by
      constructor
      · rintro ⟨i, hi⟩
        refine ⟨i, ?_⟩
        intro v e
        have heOn : cgIncOn (Finset.univ : Finset (cgEdge k)) v e.1 := by
          exact ⟨Finset.mem_univ _, e.2⟩
        simpa [f, localDrop, edgeDrop] using hi v ⟨e.1, heOn⟩
      · rintro ⟨i, hi⟩
        refine ⟨i, ?_⟩
        intro v e
        have he : cgInc k v e.1 := e.2.2
        have := hi v ⟨e.1, he⟩
        simpa [f, localDrop, edgeDrop] using this
    by_cases hOn :
        ∃ i : cgEdge k → Fin n,
          ∀ v : Fin k, ∀ e : {e : cgEdge k // cgIncOn (Finset.univ : Finset (cgEdge k)) v e},
            fOn v e = i e.1
    · rw [if_pos hOn, if_pos (hiff.mp hOn)]
    · rw [if_neg hOn, if_neg (fun h => hOn (hiff.mpr h))]

open VC.Degeneration in
/-- For disjoint edge sets `S, T`, the leg-`v` local index of the union splits as a
    product: `localIdx (cgIncOn (S∪T)) n v ≃ localIdx (cgIncOn S) n v × localIdx (cgIncOn T) n v`,
    via the disjoint-subtype sum split (`subtypeOrEquiv`) and `Equiv.sumArrowEquivProdArrow`. -/
noncomputable def localIdxUnionEquiv {k : ℕ} {S T : Finset (cgEdge k)} (hST : Disjoint S T)
    (n : ℕ) (v : Fin k) :
    localIdx (cgIncOn (S ∪ T)) n v
      ≃ localIdx (cgIncOn S) n v × localIdx (cgIncOn T) n v := by
  classical
  -- `{e // cgIncOn (S∪T) v e} ≃ {e // cgIncOn S v e} ⊕ {e // cgIncOn T v e}`.
  have hpred : ∀ e : cgEdge k, cgIncOn (S ∪ T) v e ↔ (cgIncOn S v e ∨ cgIncOn T v e) := by
    intro e; unfold cgIncOn
    rw [Finset.mem_union]; tauto
  have hdisj : Disjoint (cgIncOn S v) (cgIncOn T v) := by
    intro p hpS hpT e hpe
    have hS := (hpS e hpe).1
    have hT := (hpT e hpe).1
    exact absurd hT (Finset.disjoint_left.mp hST hS)
  let eSplit : {e : cgEdge k // cgIncOn (S ∪ T) v e}
      ≃ {e : cgEdge k // cgIncOn S v e} ⊕ {e : cgEdge k // cgIncOn T v e} :=
    (Equiv.subtypeEquivRight hpred).trans (subtypeOrEquiv _ _ hdisj)
  exact (Equiv.arrowCongr eSplit (Equiv.refl (Fin n))).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

open VC.Degeneration in
/-- Global consistency over `S ∪ T` (disjoint) factors as consistency over `S` and over `T`.
    Mirrors `ghzHTensor_prod_iff`, with the disjoint-edge split replacing the `Fin (n*N)`
    split. -/
theorem ghzHTensor_union_iff {k : ℕ} {S T : Finset (cgEdge k)} (hST : Disjoint S T)
    (n : ℕ) (f : (v : Fin k) → localIdx (cgIncOn S) n v)
    (g : (v : Fin k) → localIdx (cgIncOn T) n v) :
    (∃ h : cgEdge k → Fin n, ∀ v : Fin k, ∀ e : {e : cgEdge k // cgIncOn (S ∪ T) v e},
        (localIdxUnionEquiv hST n v).symm (f v, g v) e = h e.1)
      ↔
    (∃ i : cgEdge k → Fin n, ∀ v : Fin k, ∀ e : {e // cgIncOn S v e}, f v e = i e.1) ∧
      (∃ j : cgEdge k → Fin n, ∀ v : Fin k, ∀ e : {e // cgIncOn T v e}, g v e = j e.1) := by
  classical
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨⟨h, ?_⟩, ⟨h, ?_⟩⟩
    · intro v e
      have heU : cgIncOn (S ∪ T) v e.1 := by
        obtain ⟨hS, hv⟩ := e.2; exact ⟨Finset.mem_union_left _ hS, hv⟩
      have hsy := hh v ⟨e.1, heU⟩
      -- decode: `(localIdxUnionEquiv …).symm (f v,g v)` on an `S`-incident edge returns `f v e`.
      rw [← hsy]
      simp only [localIdxUnionEquiv, Equiv.symm_trans_apply, Equiv.arrowCongr_symm,
        Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.refl_apply, Function.comp_apply,
        Equiv.symm_symm]
      simp [subtypeOrEquiv, subtypeOrLeftEmbedding, Equiv.subtypeEquivRight, dif_pos e.2]
    · intro v e
      have heU : cgIncOn (S ∪ T) v e.1 := by
        obtain ⟨hT, hv⟩ := e.2; exact ⟨Finset.mem_union_right _ hT, hv⟩
      have hnotS : ¬ cgIncOn S v e.1 := fun hSe => (Finset.disjoint_left.mp hST hSe.1) e.2.1
      have hsy := hh v ⟨e.1, heU⟩
      rw [← hsy]
      simp only [localIdxUnionEquiv, Equiv.symm_trans_apply, Equiv.arrowCongr_symm,
        Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.refl_apply, Function.comp_apply,
        Equiv.symm_symm]
      simp [subtypeOrEquiv, subtypeOrLeftEmbedding, Equiv.subtypeEquivRight, dif_neg hnotS]
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    -- Combine `i` (used on `S`-edges) and `j` (used on `T`-edges); off `S∪T`, pick `i`.
    refine ⟨fun e => if e ∈ S then i e else j e, ?_⟩
    intro v e
    obtain ⟨heU, hv⟩ := e.2
    by_cases hS : e.1 ∈ S
    · have hf := hi v ⟨e.1, ⟨hS, hv⟩⟩
      have hSi : cgIncOn S v e.1 := ⟨hS, hv⟩
      simp only [hS, if_true]
      rw [← hf]
      simp only [localIdxUnionEquiv, Equiv.symm_trans_apply, Equiv.arrowCongr_symm,
        Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.refl_apply, Function.comp_apply,
        Equiv.symm_symm]
      simp [subtypeOrEquiv, subtypeOrLeftEmbedding, Equiv.subtypeEquivRight, dif_pos hSi]
    · have hT : e.1 ∈ T := by
        rcases Finset.mem_union.mp heU with h | h
        · exact absurd h hS
        · exact h
      have hnotS : ¬ cgIncOn S v e.1 := fun hSe => hS hSe.1
      have hg := hj v ⟨e.1, ⟨hT, hv⟩⟩
      simp only [hS, if_false]
      rw [← hg]
      simp only [localIdxUnionEquiv, Equiv.symm_trans_apply, Equiv.arrowCongr_symm,
        Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.refl_apply, Function.comp_apply,
        Equiv.symm_symm]
      simp [subtypeOrEquiv, subtypeOrLeftEmbedding, Equiv.subtypeEquivRight, dif_neg hnotS]

open VC.Degeneration in
/-- **Disjoint-edge GHZ merge** (Lemma B): for disjoint edge sets `S, T`,
    `ghzH(cgIncOn S) ⊠ ghzH(cgIncOn T) ∼ₜ ghzH(cgIncOn (S∪T))`.  Mirrors
    `ghzH_kron_step_equiv` with `localIdxUnionEquiv`/`ghzHTensor_union_iff` (disjoint-edge
    split) in place of the `Fin (n*N)` product split. -/
theorem ghzH_disjointUnion_equiv {F : Type u} [Field F] {k : ℕ}
    {S T : Finset (cgEdge k)} (hST : Disjoint S T) {n : ℕ} (hn : 1 ≤ n) :
    (ghzH_asKTensor (F := F) (cgIncOn S) hn ⊠ ghzH_asKTensor (F := F) (cgIncOn T) hn)
      ∼ₜ ghzH_asKTensor (F := F) (cgIncOn (S ∪ T)) hn := by
  classical
  refine restrictsEquiv_of_forall_legEquiv ?e ?hval
  · intro v
    exact (kronDecodeEquiv.trans
      ((ghzHEquiv (cgIncOn S) hn v).symm.prodCongr (ghzHEquiv (cgIncOn T) hn v).symm)).trans
        ((localIdxUnionEquiv hST n v).symm.trans (ghzHEquiv (cgIncOn (S ∪ T)) hn v))
  · intro idx
    unfold ghzH_asKTensor reindexKTensor
    rw [kron_apply]
    let f : (v : Fin k) → localIdx (cgIncOn S) n v :=
      fun v => (ghzHEquiv (cgIncOn S) hn v).symm (kronDecodeL (idx v))
    let g : (v : Fin k) → localIdx (cgIncOn T) n v :=
      fun v => (ghzHEquiv (cgIncOn T) hn v).symm (kronDecodeR (idx v))
    have harg : (fun v : Fin k =>
        (ghzHEquiv (cgIncOn (S ∪ T)) hn v).symm
          ((((kronDecodeEquiv.trans
            ((ghzHEquiv (cgIncOn S) hn v).symm.prodCongr (ghzHEquiv (cgIncOn T) hn v).symm)).trans
              ((localIdxUnionEquiv hST n v).symm.trans (ghzHEquiv (cgIncOn (S ∪ T)) hn v)))
            (idx v)))) =
        fun v => (localIdxUnionEquiv hST n v).symm (f v, g v) := by
      funext v
      simp only [Equiv.trans_apply, Equiv.prodCongr_apply, kronDecodeEquiv_apply]
      rw [Equiv.symm_apply_apply]
      rfl
    rw [harg]
    unfold ghzHTensor
    have hpiff := ghzHTensor_union_iff hST n f g
    by_cases hp : ∃ i : cgEdge k → Fin n,
        ∀ v : Fin k, ∀ e : {e // cgIncOn S v e}, f v e = i e.1
    · by_cases hq : ∃ j : cgEdge k → Fin n,
          ∀ v : Fin k, ∀ e : {e // cgIncOn T v e}, g v e = j e.1
      · rw [if_pos hp, if_pos hq, if_pos (hpiff.mpr ⟨hp, hq⟩)]; simp
      · rw [if_pos hp, if_neg hq]
        have hr : ¬ ∃ h : cgEdge k → Fin n, ∀ v : Fin k,
            ∀ e : {e // cgIncOn (S ∪ T) v e},
              (localIdxUnionEquiv hST n v).symm (f v, g v) e = h e.1 :=
          fun hr => hq (hpiff.mp hr).2
        rw [if_neg hr]; simp
    · have hr : ¬ ∃ h : cgEdge k → Fin n, ∀ v : Fin k,
          ∀ e : {e // cgIncOn (S ∪ T) v e},
            (localIdxUnionEquiv hST n v).symm (f v, g v) e = h e.1 :=
        fun hr => hp (hpiff.mp hr).1
      rw [if_neg hp, if_neg hr]; simp

/-- The `cgEdge k` for a pair of distinct vertices `i ≠ j`: the 2-subset `{i, j}`. -/
def edgeOf {k : ℕ} (i j : Fin k) (hij : i ≠ j) : cgEdge k :=
  ⟨{i, j}, by rw [Finset.card_pair hij]⟩

@[simp] theorem mem_edgeOf {k : ℕ} (i j v : Fin k) (hij : i ≠ j) :
    v ∈ (edgeOf i j hij).val ↔ v = i ∨ v = j := by
  simp [edgeOf, Finset.mem_insert, Finset.mem_singleton]

open VC.Degeneration in
/-- **Single-edge GHZ = pair-unit** (Lemma A): for `i ≠ j`, the GHZ of the one-edge
    hypergraph `{edgeOf i j}` equals the rank-`n` pair-unit `⟨n⟩_{i,j}`.  Per leg `v`,
    `localIdx (cgIncOn {e₀}) n v` is `Fin n` when `v ∈ {i,j}` (singleton incident-edge set)
    and a singleton (`Fin 1`) otherwise; the diagonal-consistency entry reduces to the
    endpoint-agreement indicator. -/
theorem pairUnit_equiv_singleEdgeGHZ {F : Type u} [Field F] {k : ℕ} (i j : Fin k)
    (hij : i ≠ j) {n : ℕ} (hn : 1 ≤ n) :
    unitPairTensor (F := F) ⟨n, hn⟩ i j hij
      ∼ₜ ghzH_asKTensor (F := F) (cgIncOn ({edgeOf i j hij} : Finset (cgEdge k))) hn := by
  classical
  set e₀ := edgeOf i j hij with he₀
  -- Per leg `v`: the incident-edge set of the one-edge hypergraph is `{e₀}` if `v ∈ {i,j}`,
  -- else `∅`.  `localIdx (cgIncOn {e₀}) n v = {e // e = e₀ ∧ v ∈ e.val} → Fin n`.
  have hmemIff : ∀ (v : Fin k) (e : cgEdge k),
      cgIncOn ({e₀} : Finset (cgEdge k)) v e ↔ (e = e₀ ∧ (v = i ∨ v = j)) := by
    intro v e
    unfold cgIncOn
    rw [Finset.mem_singleton]
    constructor
    · rintro ⟨rfl, hv⟩; exact ⟨rfl, (mem_edgeOf i j v hij).mp hv⟩
    · rintro ⟨rfl, hv⟩; exact ⟨rfl, (mem_edgeOf i j v hij).mpr hv⟩
  -- Format equality on every leg: `naturalPairFormat = ghzHFormat (cgIncOn {e₀})`.
  -- For `v ∈ {i,j}` both are `n`; else both are `1`.
  -- We build the leg-equiv `Fin (naturalPairFormat …) ≃ localIdx (cgIncOn {e₀}) n v` directly,
  -- and read off the entry identity (the `e₀`-coordinate of each incident leg).
  -- Build `legE v : Fin (naturalPairFormat …) ≃ localIdx (cgIncOn {e₀}) n v`.
  have hposNat : ((naturalPairFormat (⟨n, hn⟩ : ℕ+) i j i : ℕ+) : ℕ) = n := by
    simp [naturalPairFormat]
  have hposNatj : ((naturalPairFormat (⟨n, hn⟩ : ℕ+) i j j : ℕ+) : ℕ) = n := by
    simp [naturalPairFormat]
  -- The leg-equiv together with the `e₀`-value characterization (for incident legs the
  -- inverse image is the constant family, whose `e₀`-coordinate has the same `.val`).
  have natData : ∀ v : Fin k,
      { E : localIdx (cgIncOn ({e₀} : Finset (cgEdge k))) n v
          ≃ Fin ((naturalPairFormat (⟨n, hn⟩ : ℕ+) i j v : ℕ+) : ℕ) //
        ∀ (hv : v = i ∨ v = j) (c : Fin ((naturalPairFormat (⟨n, hn⟩ : ℕ+) i j v : ℕ+) : ℕ))
          (he : cgIncOn ({e₀} : Finset (cgEdge k)) v e₀),
          (E.symm c ⟨e₀, he⟩).val = c.val } := by
    intro v
    by_cases hv : v = i ∨ v = j
    · -- incident: subtype is the singleton `{e₀}`, function space `≃ Fin n`.
      haveI huniq : Unique {e : cgEdge k // cgIncOn ({e₀} : Finset (cgEdge k)) v e} :=
        ⟨⟨⟨e₀, (hmemIff v e₀).mpr ⟨rfl, hv⟩⟩⟩, by
          rintro ⟨e, he⟩; exact Subtype.ext ((hmemIff v e).mp he).1⟩
      have hfmt : ((naturalPairFormat (⟨n, hn⟩ : ℕ+) i j v : ℕ+) : ℕ) = n := by
        simp [naturalPairFormat, hv]
      refine ⟨(Equiv.funUnique _ (Fin n)).trans (finCongr hfmt.symm), ?_⟩
      intro _ c he
      -- `E.symm c` is the constant family `fun _ => cast c`, so its `e₀`-value has `.val = c.val`.
      simp only [Equiv.symm_trans_apply, finCongr_symm, finCongr_apply, Equiv.funUnique_symm_apply]
      simp
    · -- non-incident: subtype empty; the value clause is vacuous (`hv` is false).
      haveI : IsEmpty {e : cgEdge k // cgIncOn ({e₀} : Finset (cgEdge k)) v e} :=
        ⟨fun e => hv ((hmemIff v e.1).mp e.2).2⟩
      have hfmt : ((naturalPairFormat (⟨n, hn⟩ : ℕ+) i j v : ℕ+) : ℕ) = 1 := by
        simp only [naturalPairFormat]
        rw [if_neg]; · rfl
        push_neg; exact ⟨fun h => hv (Or.inl h), fun h => hv (Or.inr h)⟩
      haveI : Unique (Fin ((naturalPairFormat (⟨n, hn⟩ : ℕ+) i j v : ℕ+) : ℕ)) := by
        rw [hfmt]; infer_instance
      exact ⟨Equiv.ofUnique _ _, fun hv' _ _ => absurd hv' hv⟩
  let natEquiv : ∀ v : Fin k,
      localIdx (cgIncOn ({e₀} : Finset (cgEdge k))) n v
        ≃ Fin ((naturalPairFormat (⟨n, hn⟩ : ℕ+) i j v : ℕ+) : ℕ) := fun v => (natData v).1
  refine restrictsEquiv_of_forall_legEquiv
    (fun v => (natEquiv v).symm.trans (ghzHEquiv (cgIncOn ({e₀} : Finset (cgEdge k))) hn v)) ?_
  intro idx
  unfold ghzH_asKTensor reindexKTensor unitPairTensor ghzHTensor
  have harg : (fun v : Fin k =>
      (ghzHEquiv (cgIncOn ({e₀} : Finset (cgEdge k))) hn v).symm
        (((natEquiv v).symm.trans (ghzHEquiv (cgIncOn ({e₀} : Finset (cgEdge k))) hn v)) (idx v)))
        = fun v => (natEquiv v).symm (idx v) := by
    funext v; simp [Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [harg]
  set fLoc : (v : Fin k) → localIdx (cgIncOn ({e₀} : Finset (cgEdge k))) n v :=
    fun v => (natEquiv v).symm (idx v) with hfLoc
  -- The `e₀`-coordinate read from leg `i` resp. `j` (from the bundled value clause).
  have hi_val : ∀ (he : cgIncOn ({e₀} : Finset (cgEdge k)) i e₀),
      (fLoc i ⟨e₀, he⟩).val = (idx i).val :=
    fun he => (natData i).2 (Or.inl rfl) (idx i) he
  have hj_val : ∀ (he : cgIncOn ({e₀} : Finset (cgEdge k)) j e₀),
      (fLoc j ⟨e₀, he⟩).val = (idx j).val :=
    fun he => (natData j).2 (Or.inr rfl) (idx j) he
  -- Consistency over `{e₀}` ⟺ the `i` and `j` reads of `e₀` agree ⟺ `(idx i).val = (idx j).val`.
  by_cases hag : (idx i).val = (idx j).val
  · rw [if_pos hag, if_pos]
    -- Build a global tuple: `glob e := (fLoc i ⟨e₀, _⟩)` works on `e₀`; junk elsewhere.
    have hii : cgIncOn ({e₀} : Finset (cgEdge k)) i e₀ := (hmemIff i e₀).mpr ⟨rfl, Or.inl rfl⟩
    refine ⟨fun e => fLoc i ⟨e₀, hii⟩, ?_⟩
    intro v e
    -- `e = e₀` (only incident edge), and `fLoc v ⟨e₀,_⟩` equals the constant value;
    -- it agrees with `fLoc i ⟨e₀,_⟩` because for `v ∈ {i,j}` both reads equal `(idx i/j).val`.
    obtain ⟨heq, hvij⟩ := (hmemIff v e.1).mp e.2
    have he1 : e.1 = e₀ := heq
    -- Replace `e` by `⟨e₀, _⟩` (same subtype element, since `e.1 = e₀`).
    have hev : cgIncOn ({e₀} : Finset (cgEdge k)) v e₀ := (hmemIff v e₀).mpr ⟨rfl, hvij⟩
    have hee : e = (⟨e₀, hev⟩ : {e // cgIncOn ({e₀} : Finset (cgEdge k)) v e}) :=
      Subtype.ext he1
    change fLoc v e = fLoc i ⟨e₀, hii⟩
    apply Fin.ext
    rw [hee, hi_val hii]
    rcases hvij with rfl | rfl
    · rw [hi_val hev]
    · rw [hj_val hev]; exact hag.symm
  · rw [if_neg hag, if_neg]
    -- No global tuple: `i` and `j` reads of `e₀` would have to coincide, contradicting `hag`.
    rintro ⟨glob, hglob⟩
    apply hag
    have hii : cgIncOn ({e₀} : Finset (cgEdge k)) i e₀ := (hmemIff i e₀).mpr ⟨rfl, Or.inl rfl⟩
    have hjj : cgIncOn ({e₀} : Finset (cgEdge k)) j e₀ := (hmemIff j e₀).mpr ⟨rfl, Or.inr rfl⟩
    have h1 := hglob i ⟨e₀, hii⟩
    have h2 := hglob j ⟨e₀, hjj⟩
    rw [← hi_val hii, ← hj_val hjj, h1, h2]

open VC.Degeneration in
/-- The empty-hypergraph GHZ is the scalar unit (`⟨1⟩`): every leg's incident-edge set is
    empty, so the local index space is a singleton and the diagonal-consistency entry is
    always `1`. -/
theorem ghzH_cgIncOn_empty_equiv {F : Type u} [Field F] {k : ℕ} (hk : 0 < k) {n : ℕ}
    (hn : 1 ≤ n) :
    ghzH_asKTensor (F := F) (cgIncOn (∅ : Finset (cgEdge k))) hn
      ∼ₜ unitTensor F (k := k) 1 := by
  classical
  -- Every leg's local index space is empty-indexed (`{e // e ∈ ∅ ∧ …} = ∅`), hence a singleton.
  haveI hempty : ∀ v : Fin k, IsEmpty {e : cgEdge k // cgIncOn (∅ : Finset (cgEdge k)) v e} :=
    fun v => ⟨fun e => absurd e.2.1 (by simp)⟩
  -- Both leg formats are singletons (`Fin 1`): GHZ side because the index space is empty;
  -- unit side because the format is `1`.
  haveI huS : ∀ v : Fin k,
      Unique (Fin ((ghzHFormat (cgIncOn (∅ : Finset (cgEdge k))) hn v : ℕ+) : ℕ)) := fun v => by
    have : Fintype.card (localIdx (cgIncOn (∅ : Finset (cgEdge k))) n v) = 1 := by
      rw [Fintype.card_eq_one_iff]
      exact ⟨fun e => (hempty v).elim e, fun f => funext fun e => (hempty v).elim e⟩
    rw [show ((ghzHFormat (cgIncOn (∅ : Finset (cgEdge k))) hn v : ℕ+) : ℕ) = 1 from this]
    infer_instance
  haveI huT : ∀ v : Fin k,
      Unique (Fin (((fun _ : Fin k => (1 : ℕ+)) v : ℕ+) : ℕ)) := fun v => by
    change Unique (Fin 1); infer_instance
  refine restrictsEquiv_of_forall_legEquiv
    (fun v => by haveI := huS v; haveI := huT v; exact Equiv.ofUnique _ _) ?_
  intro idx
  -- `unitTensor 1` is constantly `1`; the empty GHZ entry is `1` (consistency is vacuous).
  have hghz : ghzH_asKTensor (F := F) (cgIncOn (∅ : Finset (cgEdge k))) hn idx = (1 : F) := by
    unfold ghzH_asKTensor reindexKTensor ghzHTensor
    rw [if_pos]
    refine ⟨fun _ => ⟨0, hn⟩, ?_⟩
    intro v e
    exact absurd e.2.1 (by simp)
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

/-- Edge of an ordered pair `(i,j)`: `{i,j}` if `i < j`, else `none`. -/
noncomputable def pairEdge {k : ℕ} (p : Fin k × Fin k) : Option (cgEdge k) :=
  if h : p.1 < p.2 then some (edgeOf p.1 p.2 (ne_of_lt h)) else none

/-- **Lemma C** (fold = partial GHZ): the Kronecker fold of the rank-`n` pair-units over a
    list `ps` of ordered pairs `(i,j)` with `i < j`, whose induced edges are distinct, is
    `∼ₜ`-equivalent to the partial complete-graph GHZ on the edge set `{edgeOf p}`.  Single-edge
    induction (`List.reverseRecOn`): each step multiplies by one pair-unit (`∼ₜ` a single-edge
    GHZ by `pairUnit_equiv_singleEdgeGHZ`), merged into the running partial GHZ by
    `ghzH_disjointUnion_equiv`. -/
theorem pairUnitFold_equiv_partialGHZ {F : Type u} [Field F] {k : ℕ} (hk : 0 < k) {n : ℕ}
    (hn : 1 ≤ n) (ps : List (Fin k × Fin k))
    (hlt : ∀ p ∈ ps, p.1 < p.2)
    (hnodup : (ps.filterMap pairEdge).Nodup) :
    (kronFoldl (TT.of (unitTensor F (k := k) (1 : ℕ+))) (ps.map (pairUnitTT n))).2
      ∼ₜ ghzH_asKTensor (F := F) (cgIncOn (ps.filterMap pairEdge).toFinset) hn := by
  classical
  induction ps using List.reverseRecOn with
  | nil =>
      -- empty fold = base unit; empty edge-set GHZ = `⟨1⟩`.
      simp only [List.map_nil, kronFoldl_nil, List.filterMap_nil, List.toFinset_nil]
      exact (ghzH_cgIncOn_empty_equiv (F := F) hk hn).symm
  | append_singleton ps p ih =>
      -- prefix hypotheses.
      have hlt' : ∀ q ∈ ps, q.1 < q.2 := fun q hq => hlt q (List.mem_append_left _ hq)
      have hppair : p.1 < p.2 := hlt p (by simp)
      have hpne : p.1 ≠ p.2 := ne_of_lt hppair
      -- the appended edge.
      have hpe : pairEdge p = some (edgeOf p.1 p.2 hpne) := by
        unfold pairEdge; rw [dif_pos hppair]
      have hfmEdges : (ps ++ [p]).filterMap pairEdge
          = ps.filterMap pairEdge ++ [edgeOf p.1 p.2 hpne] := by
        rw [List.filterMap_append]; simp [hpe]
      have hnodup' : (ps.filterMap pairEdge).Nodup := by
        rw [hfmEdges] at hnodup; exact (List.nodup_append.mp hnodup).1
      -- disjointness of the prefix edge-set from the new edge.
      have hdisj : Disjoint (ps.filterMap pairEdge).toFinset
          ({edgeOf p.1 p.2 hpne} : Finset (cgEdge k)) := by
        rw [Finset.disjoint_singleton_right, List.mem_toFinset]
        rw [hfmEdges] at hnodup
        intro hmem
        exact (List.disjoint_of_nodup_append hnodup) hmem (by simp)
      -- the appended pair-unit factor is `unitPairTensor`.
      have hpUnit : pairUnitTT n p = TT.of (unitPairTensor (F := F) ⟨n, hn⟩ p.1 p.2 hpne) := by
        unfold pairUnitTT; rw [dif_pos ⟨hpne, hn⟩]
      -- fold step: `kronFoldl base (… ++ [factor]) = (kronFoldl base …).kron factor`.
      rw [List.map_append, List.map_singleton, kronFoldl_concat]
      -- the running fold `∼ₜ` the prefix partial GHZ (IH), kron the new pair-unit.
      have hIH := ih hlt' hnodup'
      have hstep1 :
          ((kronFoldl (TT.of (unitTensor F (k := k) (1 : ℕ+))) (ps.map (pairUnitTT n))).kron
              (pairUnitTT n p)).2
            ∼ₜ (ghzH_asKTensor (F := F) (cgIncOn (ps.filterMap pairEdge).toFinset) hn
                ⊠ ghzH_asKTensor (F := F)
                    (cgIncOn ({edgeOf p.1 p.2 hpne} : Finset (cgEdge k))) hn) := by
        rw [hpUnit]
        exact RestrictsEquiv.kron_congr hIH
          (pairUnit_equiv_singleEdgeGHZ (F := F) p.1 p.2 hpne hn)
      -- merge the two disjoint-edge GHZ factors.
      have hstep2 :
          (ghzH_asKTensor (F := F) (cgIncOn (ps.filterMap pairEdge).toFinset) hn
              ⊠ ghzH_asKTensor (F := F)
                  (cgIncOn ({edgeOf p.1 p.2 hpne} : Finset (cgEdge k))) hn)
            ∼ₜ ghzH_asKTensor (F := F)
                (cgIncOn ((ps.filterMap pairEdge).toFinset
                  ∪ {edgeOf p.1 p.2 hpne})) hn :=
        ghzH_disjointUnion_equiv (F := F) hdisj hn
      -- align the union edge-set with the appended filterMap edge-set.
      have hunionEq : (ps.filterMap pairEdge).toFinset ∪ {edgeOf p.1 p.2 hpne}
          = ((ps ++ [p]).filterMap pairEdge).toFinset := by
        rw [hfmEdges, List.toFinset_append]; simp
      rw [hunionEq] at hstep2
      exact hstep1.trans hstep2

/-- **Step 1 identification (genmamu:152-156 / paper tex:984)**:
    `⊠_{i<j} ⟨n⟩_{i,j}` (`pairUnitKronAll`) is `∼ₜ`-equivalent to `ghzH^{K_k}_n`.  A
    leg-index reindex `{e // v ∈ e} ≃ (pairs incident with v)`; both entries are the
    per-pair agreement / global-consistency indicator. -/
theorem pairUnitKronAll_equiv_ghzH {F : Type u} [Field F] (hk : 3 ≤ k) {n : ℕ}
    (hn : 1 ≤ n) :
    (pairUnitKronAll F k n).2 ∼ₜ (⟨_, ghzH_asKTensor (F := F) (cgInc k) hn⟩ : TT F k).2 := by
  classical
  have hk0 : 0 < k := by omega
  -- `pairUnitKronAll` is the fold of pair-units over `cgPairsList k` (all `i < j`).
  -- `cgPairsList k = (univ.filter (·.1 < ·.2)).toList`, so its entries satisfy `.1 < .2`
  -- and it is `Nodup`.
  have hmem : ∀ p ∈ cgPairsList k, p.1 < p.2 := by
    intro p hp
    unfold cgPairsList at hp
    rw [Finset.mem_toList, Finset.mem_filter] at hp
    exact hp.2
  have hlist_nodup : (cgPairsList k).Nodup := by
    unfold cgPairsList; exact Finset.nodup_toList _
  -- `pairEdge` is injective on the `.1 < .2` pairs (recovers the unordered pair), so the
  -- induced edge list is `Nodup`.
  have hedge_inj : ∀ p q : Fin k × Fin k, p.1 < p.2 → q.1 < q.2 →
      pairEdge p = pairEdge q → p = q := by
    intro p q hp hq hpq
    unfold pairEdge at hpq
    rw [dif_pos hp, dif_pos hq] at hpq
    have hval : ({p.1, p.2} : Finset (Fin k)) = ({q.1, q.2} : Finset (Fin k)) := by
      have := Subtype.ext_iff.mp (Option.some.inj hpq)
      simpa [edgeOf] using this
    -- the min/max of `{p.1,p.2}` recover `p` (since `p.1 < p.2`), similarly `q`.
    have hp1 : p.1 ∈ ({q.1, q.2} : Finset (Fin k)) := by rw [← hval]; simp
    have hp2 : p.2 ∈ ({q.1, q.2} : Finset (Fin k)) := by rw [← hval]; simp
    have hq1 : q.1 ∈ ({p.1, p.2} : Finset (Fin k)) := by rw [hval]; simp
    have hq2 : q.2 ∈ ({p.1, p.2} : Finset (Fin k)) := by rw [hval]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp1 hp2 hq1 hq2
    -- `p.1` is the smaller, so `p.1 = q.1` and `p.2 = q.2`.
    have h11 : p.1 = q.1 := by
      rcases hp1 with h | h
      · exact h
      · -- `p.1 = q.2`; but `p.1 < p.2` and `q.1 < q.2` force `p.1 = q.1`.
        rcases hq1 with h' | h'
        · exact h'.symm
        · omega
    have h22 : p.2 = q.2 := by
      rcases hp2 with h | h
      · omega
      · exact h
    exact Prod.ext h11 h22
  have hfm_nodup : ((cgPairsList k).filterMap pairEdge).Nodup := by
    refine List.Nodup.filterMap ?_ hlist_nodup
    intro a a' b hb hb'
    -- `b ∈ pairEdge a` forces `a.1 < a.2` and `pairEdge a = some b`.
    have ha : a.1 < a.2 := by
      unfold pairEdge at hb; by_contra h; rw [dif_neg h] at hb; exact (Option.not_mem_none b) hb
    have ha' : a'.1 < a'.2 := by
      unfold pairEdge at hb'; by_contra h; rw [dif_neg h] at hb'; exact (Option.not_mem_none b) hb'
    have hba : pairEdge a = some b := by rw [Option.mem_def] at hb; exact hb
    have hba' : pairEdge a' = some b := by rw [Option.mem_def] at hb'; exact hb'
    exact hedge_inj a a' ha ha' (hba.trans hba'.symm)
  -- The induced edge-set is everything: every 2-subset `{a,b}` arises from `(min,max)`.
  have hedge_univ : ((cgPairsList k).filterMap pairEdge).toFinset
      = (Finset.univ : Finset (cgEdge k)) := by
    rw [Finset.eq_univ_iff_forall]
    intro e
    rw [List.mem_toFinset, List.mem_filterMap]
    -- `e.val = {a, b}` with `a ≠ b`; order them so `i < j`.
    obtain ⟨a, b, hab, hval⟩ := Finset.card_eq_two.mp e.2
    -- choose `i = min, j = max`.
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · refine ⟨(a, b), ?_, ?_⟩
      · unfold cgPairsList
        rw [Finset.mem_toList, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hlt⟩
      · unfold pairEdge; rw [dif_pos hlt]; congr 1
        exact Subtype.ext (by rw [edgeOf]; exact hval.symm)
    · refine ⟨(b, a), ?_, ?_⟩
      · unfold cgPairsList
        rw [Finset.mem_toList, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hgt⟩
      · unfold pairEdge; rw [dif_pos hgt]; congr 1
        refine Subtype.ext ?_; rw [edgeOf]
        rw [hval]; exact Finset.pair_comm b a
  -- Assemble: fold ∼ₜ partial GHZ on full edge-set = univ ∼ₜ ghzH(cgInc).
  have hfold := pairUnitFold_equiv_partialGHZ (F := F) hk0 hn (cgPairsList k) hmem hfm_nodup
  change (kronFoldl (TT.of (unitTensor F (k := k) (1 : ℕ+)))
      ((cgPairsList k).map (pairUnitTT n))).2
    ∼ₜ ghzH_asKTensor (F := F) (cgInc k) hn
  rw [hedge_univ] at hfold
  exact hfold.trans (ghzH_cgIncOn_univ_equiv_cgInc (F := F) hn)

/-! ## Step 4b — the washed-out genmamu bound for `ghzH^{K_k}`.

With a *fixed* line-graph GOR `c` (level-independent, from `exists_cgGorData`), the
per-level achievability `(N)^{|E|} ≤ (2·C·N)^D · borderSubrank(ghzH_N)` holds for every
`N ≥ 1` with the same `C = cubeBound c`.  Applying it at `N = n^{m+1}`, using the power
identity `asympSubrank(ghzH_n)^{m+1} = asympSubrank(ghzH_{n^{m+1}})`
(`ghzH_kronPow_equiv` + `asympSubrank_kronPowNat`), the `n^D` factors cancel
(`|E| − D = k−1`) leaving the constant overhead `(2C)^D`; `washout_const_le` then yields
`n^{k−1} ≤ asympSubrank(ghzH_n)`. -/

/-- **Fixed-`c` per-level border bound** (genmamu:181). For the level-independent
    line-graph rep `c` (`exists_cgGorData`), every `N ≥ 1` satisfies
    `N^{k(k-1)/2} ≤ (2·cubeBound c·N)^{(k-1)(k-2)/2} · borderSubrank(ghzH_N)`. -/
theorem borderSubrank_ghzH_fixedC {F : Type u} [Field F] (hk : 3 ≤ k)
    {c : cgEdge k → Fin ((k - 1) * (k - 2) / 2) → ℤ}
    (horth : ∀ e f : cgEdge k, ¬ edgesIncident (cgInc k) e f → idot (c e) (c f) = 0)
    (hgpAll : ∀ (N : ℕ) (g : Fin ((k - 1) * (k - 2) / 2) → ℤ),
      GeneralPositionInjective (k := k) (cgInc k) c N g)
    {N : ℕ} (hN : 1 ≤ N) :
    N ^ (k * (k - 1) / 2) ≤ (2 * cubeBound c * N) ^ ((k - 1) * (k - 2) / 2) *
      borderSubrank (ghzH_asKTensor (F := F) (cgInc k) hN) := by
  classical
  have hk2 : 2 ≤ k := by omega
  have hk0 : 0 < k := by omega
  set edgeOwner := cgEdgeOwner k with hEO
  set pairOwner := cgPairOwner k with hPO
  have hEdgeInc : ∀ e, cgInc k (edgeOwner e) e := cgEdgeOwner_inc k
  have hPairInc : ∀ e f, e ≠ f → idot (c e) (c f) ≠ 0 →
      cgInc k (pairOwner e f) e ∧ cgInc k (pairOwner e f) f := by
    intro e f hef hidot
    have hinc : edgesIncident (cgInc k) e f := by
      by_contra hni; exact hidot (horth e f hni)
    exact cgPairOwner_inc k hinc
  obtain ⟨g, hg⟩ := exists_g_solCount_ge c N hN
  have hM : solCount c N g ≤ borderSubrank (ghzH_asKTensor (F := F) (cgInc k) hN) :=
    solCount_le_borderSubrank_ghzH (cgInc k) c horth edgeOwner pairOwner ⟨0, hk0⟩
      hEdgeInc hPairInc hN hk0 g (hgpAll N g)
      (bddAbove_borderSubrankK_ghzH (cgInc k) hN hk2)
      (bddAbove_borderRestricts_ghzH (cgInc k) hN hk2)
  rw [← card_cgEdge k]
  calc N ^ (Fintype.card (cgEdge k))
      ≤ (2 * cubeBound c * N) ^ ((k - 1) * (k - 2) / 2) * solCount c N g := hg
    _ ≤ (2 * cubeBound c * N) ^ ((k - 1) * (k - 2) / 2) *
        borderSubrank (ghzH_asKTensor (F := F) (cgInc k) hN) :=
        Nat.mul_le_mul_left _ hM

/-- A `k`-tensor with a nonzero entry has `mk ⟨d, T⟩ ≠ 0`.  Converse of
    `exists_ne_zero_of_mk_ne_zero`: a nonzero entry makes some `{i₀}`-flattening matrix
    nonzero (rank ≥ 1), while `mk = 0` would force `Restricts T zeroT` hence
    `flatRank T {i₀} ≤ flatRank zeroT {i₀} = 0`. -/
theorem mk_ne_zero_of_entry {F : Type u} [Field F] [NeZero k] {d : Fin k → ℕ+}
    (T : KTensor F d) {idx : ∀ i, Fin (d i)} (hidx : T idx ≠ 0) :
    TensorClass.mk ⟨d, T⟩ ≠ (0 : TensorClass F k) := by
  classical
  intro hmk
  -- `mk T = 0 = mk zeroT`, so `T ∼ₜ zeroT`; in particular `Restricts T zeroT`.
  have hequiv : T ∼ₜ (zeroT : KTensor F (fun _ => (1 : ℕ+))) := by
    have : TensorClass.mk ⟨d, T⟩ = TensorClass.mk ⟨_, (zeroT : KTensor F (fun _ => (1 : ℕ+)))⟩ := by
      rw [hmk, TensorClass.zero_def]
    exact Quotient.exact this
  have hres : Restricts T (zeroT : KTensor F (fun _ => (1 : ℕ+))) := hequiv.1
  -- `flatRank T ∅ ≤ flatRank zeroT ∅`.
  have hle := hres.flatRank_le (∅ : Finset (Fin k))
  -- `flatRank zeroT ∅ = 0` (zero matrix).
  have hzero : flatRank (zeroT : KTensor F (fun _ => (1 : ℕ+))) (∅ : Finset (Fin k)) = 0 := by
    have : flattenMatrix (zeroT : KTensor F (fun _ => (1 : ℕ+))) (∅ : Finset (Fin k)) = 0 := by
      funext row col; rfl
    unfold flatRank; rw [this, Matrix.rank_zero]
  -- so `flatRank T ∅ = 0`, hence the flattening matrix is `0` — but it has the nonzero
  -- entry `T idx`, contradiction.
  have hT0 : flatRank T (∅ : Finset (Fin k)) = 0 := by omega
  have hmat0 : flattenMatrix T (∅ : Finset (Fin k)) = 0 := by
    -- rank 0 ⟹ matrix 0 (range of `mulVecLin` is `⊥`).
    have hfr : Module.finrank F (LinearMap.range (flattenMatrix T (∅ : Finset (Fin k))).mulVecLin)
        = 0 := hT0
    have hrange : LinearMap.range (flattenMatrix T (∅ : Finset (Fin k))).mulVecLin = ⊥ :=
      Submodule.finrank_eq_zero.mp hfr
    have hmvl : (flattenMatrix T (∅ : Finset (Fin k))).mulVecLin = 0 :=
      LinearMap.range_eq_bot.mp hrange
    ext p q
    have hcol : (flattenMatrix T (∅ : Finset (Fin k))).mulVec (Pi.single q 1) p = 0 := by
      have := congrFun (congrArg (fun f : (_ → F) →ₗ[F] (_ → F) => f.toFun) hmvl) (Pi.single q 1)
      exact congrFun this p
    simpa [Matrix.mulVec_single] using hcol
  -- evaluate at the column matching `idx` (rows over `{i // i ∈ ∅}` are empty).
  have hev := congrFun (congrFun hmat0 (fun i => absurd i.2 (Finset.notMem_empty _)))
    (fun j : {j // j ∉ (∅ : Finset (Fin k))} => idx j.val)
  rw [flattenMatrix] at hev
  simp only [Matrix.zero_apply] at hev
  apply hidx
  rw [← hev]
  congr 1

/-- `ghzH^{K_k}_n` is `∼ₜ`-nonzero (it has the all-consistent entry `= 1`, so
    `mk ⟨_, ghzH_n⟩ ≠ 0`).  Needed as the Fekete precondition of
    `asympSubrank_kronPowNat`. -/
theorem ghzH_mk_ne_zero {F : Type u} [Field F] [NeZero k] (hk : 3 ≤ k) {n : ℕ} (hn : 1 ≤ n) :
    TensorClass.mk ⟨_, ghzH_asKTensor (F := F) (cgInc k) hn⟩ ≠ (0 : TensorClass F k) := by
  classical
  -- The all-consistent label (from the global tuple `i ≡ 0`) gives entry `1 ≠ 0`.
  set i₀ : cgEdge k → Fin n := fun _ => ⟨0, by omega⟩ with hi₀
  -- the reindexed multi-index hitting `globalToLocal i₀`.
  set idx : ∀ v : Fin k, Fin ((ghzHFormat (cgInc k) hn v : ℕ+) : ℕ) :=
    fun v => (ghzHEquiv (cgInc k) hn v) (globalToLocal (cgInc k) i₀ v) with hidx
  apply mk_ne_zero_of_entry _ (idx := idx)
  -- `ghzH_asKTensor … idx = ghzHTensor … (globalToLocal i₀) = 1`.
  have hval : ghzH_asKTensor (F := F) (cgInc k) hn idx = 1 := by
    unfold ghzH_asKTensor reindexKTensor
    have : (fun v => (ghzHEquiv (cgInc k) hn v).symm (idx v))
        = globalToLocal (cgInc k) i₀ := by
      funext v; rw [hidx]; simp
    rw [this]
    exact ghzHTensor_globalToLocal (cgInc k) i₀
  rw [hval]; exact one_ne_zero

/-- **The washed-out genmamu bound for `ghzH^{K_k}`** (genmamu main theorem, `H = K_k`):
    `n^{k-1} ≤ asympSubrank(ghzH^{K_k}_n)`.

    PROOF (washout).  Fix the level-independent line-graph rep `c` (`exists_cgGorData`,
    `C := cubeBound c`).  For each `m`, apply `borderSubrank_ghzH_fixedC` at level
    `n^{m+1}` and lift to `asympSubrank` (`borderSubrank_le_asympSubrank`):

      `(n^{m+1})^{|E|} ≤ (2C·n^{m+1})^D · asympSubrank(ghzH_{n^{m+1}})`.

    The power identity `asympSubrank(ghzH_{n^{m+1}}) = asympSubrank(ghzH_n)^{m+1}`
    (`asympSubrank_congr ghzH_kronPow_equiv` + `asympSubrank_kronPowNat`) and the cancellation
    `|E| − D = k − 1` reduce this to `(n^{k-1})^{m+1} ≤ (2C)^D · asympSubrank(ghzH_n)^{m+1}`;
    `washout_const_le` (constant overhead `(2C)^D`) gives the claim.

    The Kronecker-reindex identities `ghzH_kronPow_equiv` (step 4) and `ghzH_mk_ne_zero`
    it invokes are now both fully proved (finite computations). -/
theorem asympSubrank_ghzH_ge {F : Type u} [Field F] [Infinite F] (hk : 3 ≤ k)
    {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ (k - 1) ≤
      asympSubrank (ghzH_asKTensor (F := F) (cgInc k) (by omega : 1 ≤ n)) := by
  classical
  haveI : NeZero k := ⟨by omega⟩
  have hk2 : 2 ≤ k := by omega
  have hn1 : 1 ≤ n := by omega
  -- Fix the level-independent GOR rep `c`.
  obtain ⟨c, horth, hgpAll⟩ := exists_cgGorData (k := k) hk
  -- abbreviations (no `set` on `c`-dependent terms to avoid spurious renames)
  let C : ℕ := cubeBound c
  let Dexp : ℕ := (k - 1) * (k - 2) / 2
  let K : ℝ := (((2 * C) ^ Dexp : ℕ) : ℝ)
  set Q : ℝ := asympSubrank (ghzH_asKTensor (F := F) (cgInc k) hn1) with hQ
  have hQnn : 0 ≤ Q := by rw [hQ]; exact asympSubrank_nonneg' hk2 _
  have hCpos : 1 ≤ C := one_le_cubeBound c
  have hKpos : 0 < K := by
    change 0 < (((2 * C) ^ Dexp : ℕ) : ℝ)
    have : 0 < (2 * C) ^ Dexp := pow_pos (by omega) Dexp
    exact_mod_cast this
  -- The amplified bound `(n^{k-1})^{m+1} ≤ K · Q^{m+1}`.
  have hamp : ∀ m : ℕ, 1 ≤ m → ((n : ℝ) ^ (k - 1)) ^ m ≤ K * Q ^ m := by
    intro m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    -- level `N := n^{m'+1}`.
    set N : ℕ := n ^ (m' + 1) with hN
    have hNpos : 1 ≤ N := Nat.one_le_pow _ _ (by omega)
    -- per-level border bound (fixed C).
    have hbound := borderSubrank_ghzH_fixedC (F := F) hk (c := c) horth hgpAll (N := N) hNpos
    -- lift to asympSubrank.
    have hbr : (borderSubrank (ghzH_asKTensor (F := F) (cgInc k) hNpos) : ℝ)
        ≤ asympSubrank (ghzH_asKTensor (F := F) (cgInc k) hNpos) :=
      borderSubrank_le_asympSubrank hk2 _
    -- power identity: asympSubrank(ghzH_N) = Q^{m'+1}.
    have hpow : asympSubrank (ghzH_asKTensor (F := F) (cgInc k) hNpos) = Q ^ (m' + 1) := by
      have hequiv := ghzH_kronPow_equiv (F := F) hk hn1 m' hNpos
      have h1 : asympSubrank (ghzH_asKTensor (F := F) (cgInc k) hNpos)
          = asympSubrank (kronPowNat (ghzH_asKTensor (F := F) (cgInc k) hn1) m') :=
        (asympSubrank_congr hk2 hequiv).symm
      rw [h1, asympSubrank_kronPowNat hk2 _ (ghzH_mk_ne_zero hk hn1) m', ← hQ]
    -- assemble over ℝ.
    have hboundR : ((N ^ (k * (k - 1) / 2) : ℕ) : ℝ) ≤
        (((2 * C * N) ^ Dexp : ℕ) : ℝ) *
          (borderSubrank (ghzH_asKTensor (F := F) (cgInc k) hNpos) : ℝ) := by
      exact_mod_cast hbound
    -- chain: (N^{|E|}) ≤ (2CN)^D · asympSubrank(ghzH_N) = (2CN)^D · Q^{m'+1}.
    have hchain : ((N : ℝ) ^ (k * (k - 1) / 2)) ≤
        (((2 * C * N) ^ Dexp : ℕ) : ℝ) * Q ^ (m' + 1) := by
      calc ((N : ℝ) ^ (k * (k - 1) / 2))
          = ((N ^ (k * (k - 1) / 2) : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (((2 * C * N) ^ Dexp : ℕ) : ℝ) *
            (borderSubrank (ghzH_asKTensor (F := F) (cgInc k) hNpos) : ℝ) := hboundR
        _ ≤ (((2 * C * N) ^ Dexp : ℕ) : ℝ) *
            asympSubrank (ghzH_asKTensor (F := F) (cgInc k) hNpos) := by
            apply mul_le_mul_of_nonneg_left hbr; positivity
        _ = (((2 * C * N) ^ Dexp : ℕ) : ℝ) * Q ^ (m' + 1) := by rw [hpow]
    -- exponent algebra: cancel (n^D)^{m'+1}, leaving (n^{k-1})^{m'+1} ≤ K · Q^{m'+1}.
    -- |E| = (k-1) + D.
    have hED : k * (k - 1) / 2 = (k - 1) + (k - 1) * (k - 2) / 2 := by
      have := card_sub_dim k hk; have := dim_le_card k; omega
    -- positive factor `P := n^((m'+1)·D)`.
    set P : ℝ := (n : ℝ) ^ ((m' + 1) * ((k - 1) * (k - 2) / 2)) with hP
    have hPpos : 0 < P := by rw [hP]; positivity
    -- `(N : ℝ) = (n:ℝ)^(m'+1)`.
    have hNr : (N : ℝ) = (n : ℝ) ^ (m' + 1) := by rw [hN]; push_cast; ring
    -- LHS factorization: N^|E| = (n^{k-1})^{m'+1} · P.
    have hLHS : ((N : ℝ) ^ (k * (k - 1) / 2)) = ((n : ℝ) ^ (k - 1)) ^ (m' + 1) * P := by
      rw [hNr, hP, ← pow_mul, ← pow_mul, ← pow_add, hED]
      ring_nf
    -- RHS factorization: (2CN)^D = K · P.
    have hRHS : (((2 * C * N) ^ Dexp : ℕ) : ℝ) = K * P := by
      change (((2 * cubeBound c * N) ^ ((k - 1) * (k - 2) / 2) : ℕ) : ℝ) = K * P
      change _ = (((2 * cubeBound c) ^ ((k - 1) * (k - 2) / 2) : ℕ) : ℝ) * P
      rw [hP]
      push_cast
      rw [hNr, mul_pow, ← pow_mul]
    rw [hLHS, hRHS] at hchain
    have hcancel : ((n : ℝ) ^ (k - 1)) ^ (m' + 1) * P ≤ (K * P) * Q ^ (m' + 1) := hchain
    have hfin : ((n : ℝ) ^ (k - 1)) ^ (m' + 1) * P ≤ (K * Q ^ (m' + 1)) * P := by
      rw [mul_right_comm K P (Q ^ (m'+1))] at hcancel; linarith [hcancel]
    exact le_of_mul_le_mul_right hfin hPpos
  -- washout.
  have := washout_const_le (s := (n : ℝ) ^ (k - 1)) (Q := Q) (K := K)
    (by positivity) hQnn hKpos hamp
  rwa [hQ] at this

/-! ##  1 headline — uniform Vrana–Christandl achievability for `K_k`.

`uniformVC` (semicontinuity tex:982-996, genmamu main theorem at `H = K_k`):

  `n^{k-1} ≤ asympSubrank(⊠_{i<j} ⟨n⟩_{i,j})`.

Combines the washed-out genmamu bound `asympSubrank_ghzH_ge`
(`n^{k-1} ≤ asympSubrank(ghzH^{K_k}_n)`) with the identification
`pairUnitKronAll_equiv_ghzH` (`⊠_{i<j}⟨n⟩_{i,j} ∼ₜ ghzH^{K_k}_n`) transported by
`asympSubrank_congr`. -/

/-- **`uniformVC`** — uniform Vrana–Christandl achievability for the complete graph
    `K_k` (semicontinuity tex:982-996; genmamu main theorem, `H = K_k`,
    `λ(K_k) = k-1`):

      `n^{k-1} ≤ asympSubrank(pairUnitKronAll F k n)`,

    where `pairUnitKronAll F k n = ⊠_{i<j} ⟨n⟩_{i,j}`.  This is the load-bearing core
    of Corollary 3.5; the weighted generalization is handled by the multigraph version.

    Reduces to the two Kronecker-reindex lemmas
    `ghzH_kronPow_equiv` (step 4 washout power identity) and
    `pairUnitKronAll_equiv_ghzH` (step 1 identification) — plus `ghzH_mk_ne_zero` — via
    the washed-out genmamu bound `asympSubrank_ghzH_ge` and `asympSubrank_congr`. -/
theorem uniformVC {F : Type u} [Field F] [Infinite F] (hk : 3 ≤ k) (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) ^ (k - 1) ≤ asympSubrank (pairUnitKronAll F k n).2 := by
  haveI : NeZero k := ⟨by omega⟩
  have hk2 : 2 ≤ k := by omega
  have hn1 : 1 ≤ n := by omega
  -- identification: asympSubrank(pairUnitKronAll) = asympSubrank(ghzH).
  have hid : asympSubrank (pairUnitKronAll F k n).2
      = asympSubrank (ghzH_asKTensor (F := F) (cgInc k) hn1) :=
    asympSubrank_congr hk2 (pairUnitKronAll_equiv_ghzH (F := F) hk hn1)
  rw [hid]
  exact asympSubrank_ghzH_ge (F := F) hk hn

end Semicontinuity
