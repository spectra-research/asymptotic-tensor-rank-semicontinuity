/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.Degeneration.Assembly
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.LSS.Descent

/-!
# General position ⇒ GHZ injectivity (Vrana–Christandl genmamu:158-159)

This file derives the `GeneralPositionInjective` hypothesis that the
Corollary 3.5 GHZ degeneration assembly (`Assembly.lean`) carries, deriving it
from the *general-position* property of the orthogonal representation `c` of the
line graph (genmamu:158-159, citing LSS).

## Source (genmamu:158-159, 194-199)

genmamu:158-159 (summarized): the resulting state is GHZ precisely when the
indices at any one vertex determine the rest uniquely; after fixing the indices
at a vertex the system `∑_e c_e i_e = g` is linear in the remaining indices, so a
*sufficient* condition is that any `D` of the vectors `c_e` are linearly
independent (`D ≥ |E| − min_j |E_j|`). An orthogonal representation with this
property is said to be in **general position**.

genmamu:194-199 states the existence theorem (verbatim statement):

> "Let `H = ([k], E, I)` be a hypergraph. Then its line graph has a
> general-position orthogonal representation `c : E → ℤ^{|E|−λ(H)}`. […] Since `H`
> is `λ(H)`-edge-connected, its line graph is `λ(H)`-vertex-connected. A result by
> Lovász, Saks and Schrijver states that any `(n−d)`-vertex-connected graph with
> `n` vertices admits a general-position orthogonal representation in `ℝ^d`."

## What this file builds

1. `GeneralPosition c` — the predicate of genmamu:159's *sufficient condition*:
   **every `D`-element subset of `{c_e}` is linearly independent** (over `ℚ`,
   the cast of the integer vectors). This is the integer analogue of `LSS.IsGP`.

2. `generalPositionInjective_of_generalPosition` — given
   `GeneralPosition c`, the dimension bound `D ≤ |E|` and the incidence-deficiency
   bound `|{e | ¬ inc v₀ e}| ≤ D` (= genmamu:159's `d ≥ |E| − min_j |E_j|`), two
   solutions of `∑_e c_e i_e = g` agreeing at one vertex are equal.

3. `generalPosition_of_isGP` — the (conditional) LSS bridge: transferring
   `LSS.IsGP` of the GOR to `GeneralPosition c`, **given** the identification of
   `E` with the line-graph vertices and the cast-compatibility of the integer
   vectors with the GOR's `EuclideanSpace ℝ` vectors. See its docstring and the
   file footer for the precise gap that remains for an *unconditional* bridge.

## Index arithmetic (genmamu:159, load-bearing)

After fixing the indices at a vertex `v₀`, the surviving unknowns are the edges
**not incident** with `v₀`. Their count is `|E| − |E_{v₀}| ≤ |E| − min_j |E_j|`.
The system `∑_e c_e i_e = g` restricted to these unknowns is homogeneous on the
differences `i_e − i'_e`; general position ("any `D` vectors independent", with
`D ≥ |E| − min_j |E_j|`) forces those differences to vanish. We carry the two
arithmetic facts as the hypotheses `hDcard : D ≤ |E|` (so a `D`-subset exists)
and `hdef : |{e | ¬ inc v₀ e}| ≤ D` (genmamu:159's deficiency bound).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset BigOperators

namespace VC.Degeneration

variable {E : Type*} [Fintype E] [DecidableEq E] {k D : ℕ}
variable (inc : Fin k → E → Prop) [∀ v e, Decidable (inc v e)]

/-! ## The general-position predicate (genmamu:159) -/

/-- The rational vector `c_e ∈ ℚ^D` associated to an edge `e` (the cast of the
    integer orthogonal-representation vector). -/
def cQ (c : E → Fin D → ℤ) (e : E) : Fin D → ℚ := fun r => (c e r : ℚ)

/-- **General position** (genmamu:159, the *sufficient condition* "any `d` vectors
    are linearly independent"; the integer analogue of `LSS.IsGP`,
    `Descent.lean:61`). The orthogonal representation `c : E → ℤ^D` is in general
    position iff **every `D`-element subset** of the vectors `{c_e}` is linearly
    independent (over `ℚ`, after casting). (genmamu:159) -/
def GeneralPosition (c : E → Fin D → ℤ) : Prop :=
  ∀ s : Finset E, s.card = D →
    LinearIndependent ℚ (fun e : (s : Set E) => cQ c e.val)

/-- General position passes to subsets of size `≤ D`: any subset `T` with
    `|T| ≤ D` indexes a linearly independent family (extend `T` to a `D`-subset
    via `Finset.exists_superset_card_eq`, then restrict by `LinearIndepOn.mono`).
    This is genmamu:159's step "the vectors corresponding to edges not incident
    with any one vertex (`≤ D` of them) are linearly independent". -/
theorem GeneralPosition.linearIndepOn_of_card_le {c : E → Fin D → ℤ}
    (hgp : GeneralPosition c) (hDcard : D ≤ Fintype.card E)
    {T : Finset E} (hT : T.card ≤ D) :
    LinearIndepOn ℚ (cQ c) (↑T : Set E) := by
  -- Extend `T` to a `D`-subset `s ⊇ T`.
  obtain ⟨s, hsub, hscard⟩ := Finset.exists_superset_card_eq hT hDcard
  -- General position on `s` gives `LinearIndepOn` on `↑s`, then restrict to `↑T`.
  have hs : LinearIndepOn ℚ (cQ c) (↑s : Set E) :=
    (linearIndependent_set_coe_iff).1 (hgp s hscard)
  exact hs.mono (by exact_mod_cast hsub)

/-! ## General position ⇒ GHZ injectivity (genmamu:158-159) -/

/-- **General position ⇒ GHZ injectivity** (genmamu:158-159).  General position of the orthogonal
    representation `c` implies `GeneralPositionInjective` for *every* `n` and `g`:
    two solutions `i, i'` of `∑_e c_e i_e = g` that agree on the edges incident
    with some single vertex `v₀` are equal.

    PROOF (genmamu:158-159). Fixing the indices at `v₀`, the difference
    `δ_e := i_e − i'_e` vanishes on the incident edges and satisfies the
    homogeneous system `∑_e c_e δ_e = 0`, i.e. `∑_{e ∉ E_{v₀}} c_e δ_e = 0` over
    the **non-incident** edges `T := {e | ¬ inc v₀ e}`.  By `hdef`,
    `|T| ≤ D` (= genmamu:159's `d ≥ |E| − min_j |E_j|`), so by general position
    (`GeneralPosition.linearIndepOn_of_card_le`) the family `(c_e)_{e ∈ T}` is
    linearly independent; hence every `δ_e = 0` on `T`.  Combined with the
    incident agreement, `δ ≡ 0`, i.e. `i = i'`.

    The two index-arithmetic facts are carried as hypotheses, exactly per
    genmamu:159: `hDcard : D ≤ |E|` (a `D`-subset exists) and, for each vertex,
    `hdef v₀ : |{e | ¬ inc v₀ e}| ≤ D` (the deficiency bound). -/
theorem generalPositionInjective_of_generalPosition
    {c : E → Fin D → ℤ} (hgp : GeneralPosition c)
    (hDcard : D ≤ Fintype.card E)
    (hdef : ∀ v₀ : Fin k, (Finset.univ.filter (fun e => ¬ inc v₀ e)).card ≤ D)
    (n : ℕ) (g : Fin D → ℤ) :
    GeneralPositionInjective (k := k) inc c n g := by
  intro v₀ i i' hi hi' hagree
  -- The non-incident edges `T` at `v₀`.
  set T : Finset E := Finset.univ.filter (fun e => ¬ inc v₀ e) with hT_def
  -- Coefficients: the rational index differences `δ_e = i_e − i'_e`.
  set δ : E → ℚ := fun e => ((i e : ℤ) : ℚ) - ((i' e : ℤ) : ℚ) with hδ_def
  -- `δ` vanishes on the incident edges (those NOT in `T`).
  have hδ_incident : ∀ e ∈ Tᶜ, δ e = 0 := by
    intro e he
    have hinc : inc v₀ e := by
      simp only [hT_def, Finset.compl_filter, Finset.mem_filter, Finset.mem_univ,
        true_and, not_not] at he
      exact he
    simp only [hδ_def, sub_eq_zero]
    exact_mod_cast congrArg (fun (x : Fin n) => (x : ℤ)) (hagree e hinc)
  -- The homogeneous combination over `T` is zero (coordinatewise, from `hi − hi'`).
  have hcomb : ∑ e ∈ T, δ e • cQ c e = 0 := by
    funext r
    simp only [Finset.sum_apply, Pi.zero_apply, Pi.smul_apply, cQ, smul_eq_mul]
    -- Extend the sum from `T` to all of `E`: the complementary terms vanish (`δ = 0`).
    have hext : ∑ e ∈ T, δ e * (c e r : ℚ) = ∑ e : E, δ e * (c e r : ℚ) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun e => ¬ inc v₀ e)
        (fun e => δ e * (c e r : ℚ))]
      have hzero : ∑ e ∈ Finset.univ.filter (fun e => ¬ ¬ inc v₀ e),
          δ e * (c e r : ℚ) = 0 := by
        apply Finset.sum_eq_zero
        intro e he
        have : e ∈ Tᶜ := by
          simp only [hT_def, Finset.compl_filter] at *
          simpa using he
        rw [hδ_incident e this, zero_mul]
      simp only [hT_def, hzero, add_zero]
    rw [hext]
    -- The full sum is `∑_e (i_e − i'_e) c_e r = (∑_e c_e r i_e) − (∑_e c_e r i'_e) = g_r − g_r`.
    have hi_r := hi r
    have hi'_r := hi' r
    have key : ∑ e : E, δ e * (c e r : ℚ) =
        (∑ e : E, ((c e r : ℤ) : ℚ) * ((i e : ℤ) : ℚ))
          - (∑ e : E, ((c e r : ℤ) : ℚ) * ((i' e : ℤ) : ℚ)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro e _
      simp only [hδ_def]; ring
    rw [key]
    have c1 : (∑ e : E, ((c e r : ℤ) : ℚ) * ((i e : ℤ) : ℚ)) = ((g r : ℤ) : ℚ) := by
      rw [← hi_r]; push_cast; rfl
    have c2 : (∑ e : E, ((c e r : ℤ) : ℚ) * ((i' e : ℤ) : ℚ)) = ((g r : ℤ) : ℚ) := by
      rw [← hi'_r]; push_cast; rfl
    rw [c1, c2, sub_self]
  -- General position ⇒ the family on `T` is linearly independent ⇒ all `δ_e = 0` on `T`.
  have hindep : LinearIndepOn ℚ (cQ c) (↑T : Set E) :=
    hgp.linearIndepOn_of_card_le hDcard (hdef v₀)
  have hδ_T : ∀ e ∈ T, δ e = 0 :=
    (linearIndepOn_iff'.1 hindep) T δ (le_refl _) hcomb
  -- Conclude `i = i'`: on `T` from `hδ_T`, on `Tᶜ` from `hagree`.
  funext e
  by_cases he : e ∈ T
  · have hδe : δ e = 0 := hδ_T e he
    simp only [hδ_def, sub_eq_zero] at hδe
    have hZ : ((i e : ℕ) : ℤ) = ((i' e : ℕ) : ℤ) := by exact_mod_cast hδe
    exact Fin.val_injective (by exact_mod_cast hZ)
  · have hinc : inc v₀ e := by
      simp only [hT_def, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at he
      exact he
    exact hagree e hinc

/-! ## The LSS-GOR bridge (genmamu:194-199) — conditional

The LSS existence theorem (`LSS.exists_rat_gor`,
`AsymptoticSubrank/LSS/Existence.lean:277`, and its line-graph instance
`LSS.exists_rat_gor_lineCompleteGraph`, `CompleteLineGraph.lean:625`) produces a
GOR `f : Fin N → EuclideanSpace ℝ (Fin D)` with `LSS.IsGOR (lineCompleteGraph k) f`,
where `LSS.IsGP f` says *every `D`-subset of `f` is `ℝ`-linearly independent*
(`Descent.lean:61`). This is the **same** general-position notion as
`GeneralPosition c` — but stated over a **different carrier**:

* the GOR's index type is `Fin N` (the line-graph vertices), not the abstract
  edge type `E` of the degeneration;
* the GOR's vectors live in `EuclideanSpace ℝ (Fin D)`, not `Fin D → ℤ`;
* `LSS.IsGP` gives `ℝ`-independence; `GeneralPosition` asks for `ℚ`-independence
  of the integer cast.

`generalPosition_of_isGP` below transfers `IsGP` to `GeneralPosition` **given**
those identifications as explicit hypotheses (an `E ≃ Fin N`, and the
cast-compatibility `(f (eqv e)) r = (c e r : ℝ)`). It is a true lemma; the
remaining gap to an *unconditional* bridge is precisely the construction of the
identification `E ≃ Fin N` + the integer LCM-clearing (`f` rational ⇒ `c`
integer, genmamu:197), which the repo's degeneration layer does not yet wire to
the `lineCompleteGraph` GOR layer. -/

/-- **Conditional LSS bridge** (genmamu:194-199).  `LSS.IsGP` of a real GOR `f`
    transfers to `GeneralPosition c` for an integer representation `c`, provided
    an identification `eqv : E ≃ Fin N` of the edge type with the GOR's index type
    and cast-compatibility `hcast : ∀ e r, (f (eqv e)) r = ((c e r : ℤ) : ℝ)`.

    Proof: a `D`-subset `s ⊆ E` maps under `eqv` to a `D`-subset of `Fin N`;
    `IsGP` gives `ℝ`-independence of the `f`-family there, which transfers along
    `eqv` and the cast back to `ℚ`-independence of `cQ c` on `s`.

    The construction of `eqv` and integer clearing is described in the section
    docstring. -/
theorem generalPosition_of_isGP {N : ℕ} {c : E → Fin D → ℤ}
    {f : Fin N → EuclideanSpace ℝ (Fin D)} (eqv : E ≃ Fin N)
    (hgp : LSS.IsGP f)
    (hcast : ∀ e r, (f (eqv e)) r = ((c e r : ℤ) : ℝ)) :
    GeneralPosition c := by
  intro s hscard
  -- Transfer to a `D`-subset of `Fin N`.
  have himg : (s.image eqv).card = D := by
    rw [Finset.card_image_of_injective _ eqv.injective, hscard]
  have hreal : LinearIndepOn ℝ f (↑(s.image eqv) : Set (Fin N)) :=
    (linearIndependent_set_coe_iff).1 (hgp _ himg)
  -- We reduce to `linearIndepOn_iff'` on the `ℚ`-family `cQ c` over `↑s`.
  rw [linearIndependent_set_coe_iff, linearIndepOn_iff']
  intro t gℚ ht hcomb
  -- ℝ-coefficients pushed forward along `eqv`: `hℝ (eqv e) = (gℚ e : ℝ)`.
  set hℝ : Fin N → ℝ := fun j => ((gℚ (eqv.symm j) : ℚ) : ℝ) with hℝ_def
  -- The ℝ-relation over the image `t.image eqv ⊆ s.image eqv`.
  have hcombℝ : ∑ j ∈ t.image eqv, hℝ j • f j = 0 := by
    rw [Finset.sum_image (fun a _ b _ h => eqv.injective h)]
    -- Reindexed: `∑_{e ∈ t} (gℚ e : ℝ) • f (eqv e) = 0`, coordinatewise from `hcomb`.
    apply (WithLp.linearEquiv 2 ℝ (Fin D → ℝ)).injective
    ext r
    -- LHS coordinate `r`: `∑_{e∈t} (gℚ e : ℝ) · (f (eqv e)).ofLp r`.
    have hlhs : (WithLp.linearEquiv 2 ℝ (Fin D → ℝ)) (∑ x ∈ t, hℝ (eqv x) • f (eqv x)) r =
        ∑ e ∈ t, ((gℚ e : ℝ)) * ((f (eqv e)).ofLp r) := by
      rw [map_sum]
      simp only [Finset.sum_apply, hℝ_def, Equiv.symm_apply_apply, map_smul,
        WithLp.coe_linearEquiv, Pi.smul_apply, smul_eq_mul]
    rw [hlhs]
    have hcomb_r := congrFun hcomb r
    simp only [Finset.sum_apply, Pi.zero_apply, Pi.smul_apply, cQ, smul_eq_mul] at hcomb_r
    -- `∑_{e∈t} (gℚ e)(c e r) = 0` in ℚ; cast to ℝ, using `hcast` for `(f (eqv e)).ofLp r`.
    have hcast_sum : ∑ e ∈ t, ((gℚ e : ℝ)) * ((f (eqv e)).ofLp r) =
        ((∑ e ∈ t, (gℚ e) * ((c e r : ℤ) : ℚ) : ℚ) : ℝ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro e _
      rw [hcast e r]
    rw [hcast_sum, hcomb_r]; simp
  -- `t.image eqv ⊆ s.image eqv`, so `hreal` forces the ℝ-coefficients to vanish.
  have htsub : (↑(t.image eqv) : Set (Fin N)) ⊆ (↑(s.image eqv) : Set (Fin N)) := by
    apply Finset.coe_subset.2
    apply Finset.image_subset_image
    exact Finset.coe_subset.1 ht
  have hzeroℝ : ∀ j ∈ t.image eqv, hℝ j = 0 :=
    (linearIndepOn_iff'.1 hreal) (t.image eqv) hℝ htsub hcombℝ
  -- Pull back to `gℚ e = 0` for `e ∈ t`.
  intro e he
  have hj : eqv e ∈ t.image eqv := Finset.mem_image_of_mem eqv he
  have := hzeroℝ (eqv e) hj
  simp only [hℝ_def, Equiv.symm_apply_apply] at this
  exact_mod_cast this

end VC.Degeneration
