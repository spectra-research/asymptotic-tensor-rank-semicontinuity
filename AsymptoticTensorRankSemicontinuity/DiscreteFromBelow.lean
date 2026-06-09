/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.EuclideanClosed

/-!
# §4.2 Geometric characterization of discreteness from below

Source: the semicontinuity manuscript,
lines 1269-1370.

* `discreteFromBelow_iff_levelSet_open` — **Theorem 4.7** (tex:1308-1351,
  `\label{th:geom-charac}`).
* `asympRank_discreteFromBelow_iff` — **Corollary 4.8** (tex:1353-1364,
  `\label{cor:asymprank-disc-equiv}`).
-/

namespace Semicontinuity

universe u v

variable {V : Type v} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]

/-- A subset `S ⊆ ℝ` is **discrete from below** if every nondecreasing sequence in `S`
    stabilizes. Equivalently (over ℝ): every element has a neighbourhood below it
    disjoint from `S \ {s}`. -/
def IsDiscreteFromBelow (S : Set ℝ) : Prop :=
  ∀ f : ℕ → ℝ, (∀ i, f i ∈ S) → (∀ i, f i ≤ f (i + 1)) → ∃ N, ∀ n ≥ N, f n = f N

/-- A subset `S ⊆ ℝ` is **discrete** if every point is isolated: each `x ∈ S` has
    an `ε > 0` such that no other element of `S` lies within distance `ε`.

    Equivalently: discrete from above and from below. -/
def IsDiscrete (S : Set ℝ) : Prop :=
  ∀ x ∈ S, ∃ ε > 0, ∀ y ∈ S, y ≠ x → ε ≤ |y - x|

/-- The empty set is Zariski-closed. -/
private lemma zariskiClosed_empty_set :
    IsZariskiClosed (F := ℂ) (∅ : Set V) := by
  simpa [IsZariskiClosed] using (zariskiClosure_empty (V := V))

/-- The whole ambient space is Zariski-closed. -/
private lemma zariskiClosed_univ_set :
    IsZariskiClosed (F := ℂ) (Set.univ : Set V) := by
  unfold IsZariskiClosed
  ext T
  constructor
  · intro _; trivial
  · intro hT
    exact subset_zariskiClosure (F := ℂ) Set.univ hT

/-- Zariski-closed sets are closed under binary intersections. -/
private lemma zariskiClosed_inter {A B : Set V}
    (hA : IsZariskiClosed (F := ℂ) A) (hB : IsZariskiClosed (F := ℂ) B) :
    IsZariskiClosed (F := ℂ) (A ∩ B) := by
  unfold IsZariskiClosed at hA hB ⊢
  apply Set.eq_of_subset_of_subset
  · intro T hT
    constructor
    · rw [← hA]
      intro f hf hfA
      exact hT f hf (fun S hS => hfA S hS.1)
    · rw [← hB]
      intro f hf hfB
      exact hT f hf (fun S hS => hfB S hS.2)
  · exact subset_zariskiClosure (F := ℂ) (A ∩ B)

/-- A Zariski-LSC function on the ambient finite-dimensional space is bounded above. -/
private lemma bddAbove_range_of_zariskiLSC
    (Func : V → ℝ) (hF : ZariskiLSC Func) :
    BddAbove (Set.range Func) := by
  classical
  obtain ⟨s, hs_ne, h_univ_union, hs_irred⟩ :=
    IsZariskiClosed.exists_irreducible_decomposition
      (V := V) Set.univ ⟨0, trivial⟩ zariskiClosed_univ_set
  obtain ⟨Y₀, hY₀s, hY₀_max⟩ :=
    Finset.exists_max_image s (fun Y => supOn Func Y) hs_ne
  refine ⟨supOn Func Y₀, ?_⟩
  rintro y ⟨T, rfl⟩
  have hT_union : T ∈ ⋃ Y ∈ s, Y := by
    simp [← h_univ_union]
  rcases Set.mem_iUnion.mp hT_union with ⟨Y, hT_mem_Ys⟩
  rcases Set.mem_iUnion.mp hT_mem_Ys with ⟨hYs, hTY⟩
  have hY_irr : IsZariskiIrreducible Y := (hs_irred Y hYs).2
  have hbddY_image : BddAbove (Func '' Y) :=
    (irreducible_variety_maximizers_dense Func hF Y hY_irr).2.2
  have hbddY_subtype : BddAbove (Set.range fun T : Y => Func T) := by
    rcases hbddY_image with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rintro z ⟨S, rfl⟩
    exact hb ⟨S.1, S.2, rfl⟩
  have hT_le_supY : Func T ≤ supOn Func Y := by
    rw [supOn]
    exact le_ciSup hbddY_subtype ⟨T, hTY⟩
  exact hT_le_supY.trans (hY₀_max Y hYs)

/-- A closed, bounded-above, pointwise-discrete subset of `ℝ` is discrete from below. -/
private lemma discreteFromBelow_of_isDiscrete_of_closed_of_bddAbove
    {S : Set ℝ} (hdisc : IsDiscrete S) (hclosed : IsClosed S) (hbdd : BddAbove S) :
    IsDiscreteFromBelow S := by
  classical
  intro f hfS hfmono_succ
  let r : ℝ := ⨆ i, f i
  have hfmono : Monotone f := monotone_nat_of_le_succ hfmono_succ
  have hfr_bdd : BddAbove (Set.range f) := hbdd.mono (by
    rintro y ⟨i, rfl⟩
    exact hfS i)
  have hrS : r ∈ S := by
    exact hclosed.mem_of_tendsto
      (by simpa [r] using tendsto_atTop_ciSup hfmono hfr_bdd)
      (Filter.Eventually.of_forall hfS)
  obtain ⟨ε, hεpos, hεiso⟩ := hdisc r hrS
  have hhalf_pos : 0 < ε / 2 := half_pos hεpos
  have htarget_lt : r - ε / 2 < r := by linarith
  rcases (lt_ciSup_iff hfr_bdd).mp htarget_lt with ⟨N, hN⟩
  have hN_eq : f N = r := by
    have hfN_le_r : f N ≤ r := le_ciSup hfr_bdd N
    by_contra hneN
    have hfN_lt_r : f N < r := lt_of_le_of_ne hfN_le_r hneN
    have habs_lt : |f N - r| < ε := by
      rw [abs_of_neg]
      · linarith
      · linarith
    exact not_lt_of_ge (hεiso (f N) (hfS N) hneN) habs_lt
  refine ⟨N, fun n hn => ?_⟩
  have hfn_le_r : f n ≤ r := by
    exact le_ciSup hfr_bdd n
  by_contra hne
  have hne_r : f n ≠ r := by
    intro hnr
    apply hne
    simpa [hN_eq] using hnr
  have hN_le_fn : r ≤ f n := by
    simpa [hN_eq] using hfmono hn
  exact hne_r (le_antisymm hfn_le_r hN_le_fn)

/-- Well-foundedness of a containing value set gives a gap above each value. -/
private lemma exists_gap_above_of_wellFoundedLT
    {U S : Set ℝ} (hSU : S ⊆ U) (hWF : WellFoundedLT U) {x : ℝ} (_hxS : x ∈ S) :
    ∃ ε > 0, ∀ y ∈ S, x < y → ε ≤ y - x := by
  classical
  let B : Set U := { y : U | x < (y : ℝ) }
  by_cases hB : B.Nonempty
  · obtain ⟨m, hmB, hm_min⟩ := hWF.wf.has_min B hB
    refine ⟨(m : ℝ) - x, sub_pos.mpr hmB, ?_⟩
    intro y hyS hxy
    have hyU : y ∈ U := hSU hyS
    let yu : U := ⟨y, hyU⟩
    have hyuB : yu ∈ B := hxy
    have hnot_lt : ¬ (yu : ℝ) < (m : ℝ) := hm_min yu hyuB
    exact sub_le_sub_right (le_of_not_gt hnot_lt) x
  · refine ⟨1, by norm_num, ?_⟩
    intro y hyS hxy
    have hyU : y ∈ U := hSU hyS
    exact (hB ⟨⟨y, hyU⟩, hxy⟩).elim

/-- Pure order-theoretic gap needed in the proof of Theorem 4.7, `(a) ⇒ (b)`.

This is the remaining real-analysis extraction from the sequence definition of
`IsDiscreteFromBelow`: if no such `r'` existed, one recursively chooses a
nondecreasing sequence of values below `r` which is eventually forced above any
fixed eventual value, contradicting stabilization. -/
lemma exists_gap_below_of_discreteFromBelow
    (S : Set ℝ) (hdisc : IsDiscreteFromBelow S) (r : ℝ) :
    ∃ r' : ℝ, r' < r ∧ ∀ s ∈ S, s < r → s < r' := by
  classical
  by_contra hgap
  push_neg at hgap
  have hinit : ∃ s : ℝ, s ∈ S ∧ s < r := by
    obtain ⟨s, hsS, hslt, _⟩ := hgap (r - 1) (by linarith)
    exact ⟨s, hsS, hslt⟩
  let A : Type := { s : ℝ // s ∈ S ∧ s < r }
  let a0 : A := ⟨Classical.choose hinit, Classical.choose_spec hinit⟩
  have hstep : ∀ a : A, ∃ b : A, (a.1 + r) / 2 ≤ b.1 := by
    intro a
    have hmid_lt : (a.1 + r) / 2 < r := by
      linarith [a.2.2]
    obtain ⟨s, hsS, hslt, hle⟩ := hgap ((a.1 + r) / 2) hmid_lt
    exact ⟨⟨s, hsS, hslt⟩, hle⟩
  let next : A → A := fun a => Classical.choose (hstep a)
  have hnext : ∀ a : A, (a.1 + r) / 2 ≤ (next a).1 := by
    intro a
    exact Classical.choose_spec (hstep a)
  let fA : ℕ → A := fun n => Nat.rec a0 (fun _ a => next a) n
  have hf_mem : ∀ i, (fA i).1 ∈ S := fun i => (fA i).2.1
  have hf_mono : ∀ i, (fA i).1 ≤ (fA (i + 1)).1 := by
    intro i
    have hle_mid : (fA i).1 ≤ ((fA i).1 + r) / 2 := by
      linarith [(fA i).2.2]
    have hmid_next : ((fA i).1 + r) / 2 ≤ (fA (i + 1)).1 := by
      simpa [fA, next] using hnext (fA i)
    exact hle_mid.trans hmid_next
  obtain ⟨N, hstable⟩ := hdisc (fun i => (fA i).1) hf_mem hf_mono
  have hstrict : (fA N).1 < (fA (N + 1)).1 := by
    have hlt_mid : (fA N).1 < ((fA N).1 + r) / 2 := by
      linarith [(fA N).2.2]
    have hmid_next : ((fA N).1 + r) / 2 ≤ (fA (N + 1)).1 := by
      simpa [fA, next] using hnext (fA N)
    exact hlt_mid.trans_le hmid_next
  have heq : (fA (N + 1)).1 = (fA N).1 := hstable (N + 1) (Nat.le_succ N)
  linarith

/-- Discreteness from below plus well-foundedness of a containing value set gives
pointwise discreteness. -/
private lemma isDiscrete_of_discreteFromBelow_of_wellFoundedLT
    {U S : Set ℝ} (hSU : S ⊆ U) (hWF : WellFoundedLT U)
    (hbelow : IsDiscreteFromBelow S) :
    IsDiscrete S := by
  classical
  intro x hxS
  obtain ⟨r', hr'lt, hgap_below⟩ := exists_gap_below_of_discreteFromBelow S hbelow x
  obtain ⟨εabove, hεabove_pos, hgap_above⟩ :=
    exists_gap_above_of_wellFoundedLT hSU hWF hxS
  refine ⟨min (x - r') εabove, ?_, ?_⟩
  · exact lt_min (sub_pos.mpr hr'lt) hεabove_pos
  · intro y hyS hyne
    rcases lt_or_gt_of_ne hyne with hylt | hxlt
    · have hyr' : y < r' := hgap_below y hyS hylt
      have hdist : x - r' ≤ |y - x| := by
        rw [abs_of_neg]
        · linarith
        · linarith
      exact (min_le_left _ _).trans hdist
    · have hdist : εabove ≤ |y - x| := by
        rw [abs_of_pos]
        · exact hgap_above y hyS hxlt
        · linarith
      exact (min_le_right _ _).trans hdist

/-- **Theorem 4.7, (a) ⇒ (b)** (tex:1322-1335).

Paper proof: discreteness from below gives `r' < r` isolating `r` from lower
values of `F`; then `V_{=r} = V_{>r'} ∩ V_{≤r}`, and `V_{>r'}` is Zariski-open
because `F` is Zariski-LSC. -/
lemma levelSet_open_of_discreteFromBelow
    (Func : V → ℝ) (hF : ZariskiLSC Func)
    (hdisc : IsDiscreteFromBelow (Set.range Func)) :
    ∀ r : ℝ, IsZariskiOpenIn { T : V | Func T = r } { T : V | Func T ≤ r } := by
  intro r
  rcases exists_gap_below_of_discreteFromBelow (Set.range Func) hdisc r with
    ⟨r', hr'lt, hgap⟩
  refine ⟨?_, { T : V | Func T ≤ r' }, hF r', ?_⟩
  · intro T hT
    exact le_of_eq hT
  · ext T
    constructor
    · rintro ⟨hTr, hTne⟩
      refine ⟨hTr, ?_⟩
      exact le_of_lt (hgap (Func T) ⟨T, rfl⟩ (lt_of_le_of_ne hTr hTne))
    · rintro ⟨hTr, hTr'⟩
      refine ⟨hTr, ?_⟩
      intro hTeq
      exact (not_le_of_gt hr'lt) (hTeq ▸ hTr')

/-- **Theorem 4.7, (b) ⇒ (a)** (tex:1337-1351).

Paper proof: a nondecreasing value sequence has a limit value `r` by the
maximizer/closedness results. If it is strictly increasing to `r`, then
`V_{<r}` is a countable union of proper closed subvarieties, contradicting the
Baire property for irreducible components. -/
lemma discreteFromBelow_of_levelSet_open
    (Func : V → ℝ) (hF : ZariskiLSC Func)
    (hopen : ∀ r : ℝ,
      IsZariskiOpenIn { T : V | Func T = r } { T : V | Func T ≤ r }) :
    IsDiscreteFromBelow (Set.range Func) := by
  classical
  intro f hf_range hfmono_succ
  have hfmono : Monotone f := monotone_nat_of_le_succ hfmono_succ
  have hFunc_bdd : BddAbove (Set.range Func) := bddAbove_range_of_zariskiLSC Func hF
  have hf_bdd : BddAbove (Set.range f) := hFunc_bdd.mono (by
    rintro y ⟨i, rfl⟩
    exact hf_range i)
  let r : ℝ := ⨆ i, f i
  have hf_le_r : ∀ i, f i ≤ r := fun i => le_ciSup hf_bdd i
  by_cases hhit : ∃ N, f N = r
  · rcases hhit with ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    exact le_antisymm (by simpa [hN] using hf_le_r n) (hfmono hn)
  · have hf_lt_r : ∀ i, f i < r := by
      intro i
      exact lt_of_le_of_ne (hf_le_r i) (by
        intro hi
        exact hhit ⟨i, hi⟩)
    let X : Set V := { T : V | Func T ≤ r }
    let U : Set V := { T : V | Func T = r }
    let W : Set V := { T : V | Func T < r }
    rcases hopen r with ⟨hUX, C, hC_closed, hdiff⟩
    have hW_eq : W = X ∩ C := by
      ext T
      constructor
      · intro hT
        have hTlt : Func T < r := by simpa [W] using hT
        have hTdiff : T ∈ X \ U := by
          exact ⟨by simpa [X] using le_of_lt hTlt,
            fun hEq => (ne_of_lt hTlt) hEq⟩
        simpa [X, U, W, hdiff] using hTdiff
      · intro hT
        have hTdiff : T ∈ X \ U := by
          simpa [X, U, W, hdiff] using hT
        exact lt_of_le_of_ne hTdiff.1 hTdiff.2
    have hW_closed : IsZariskiClosed (F := ℂ) W := by
      rw [hW_eq]
      exact zariskiClosed_inter (hF r) hC_closed
    have hW_ne : W.Nonempty := by
      rcases hf_range 0 with ⟨T₀, hT₀⟩
      exact ⟨T₀, by simpa [W, hT₀] using hf_lt_r 0⟩
    obtain ⟨Tstar, hTstarW, hTstar_sup⟩ :=
      exists_maximizer Func hF W hW_ne hW_closed
    have hW_bdd : BddAbove (Set.range fun T : W => Func T) := by
      refine ⟨r, ?_⟩
      rintro y ⟨T, rfl⟩
      exact le_of_lt T.2
    have hf_le_star : ∀ i, f i ≤ Func Tstar := by
      intro i
      rcases hf_range i with ⟨Tᵢ, hTᵢ⟩
      have hTᵢW : Tᵢ ∈ W := by
        simpa [W, hTᵢ] using hf_lt_r i
      have hle_sup : Func Tᵢ ≤ supOn Func W := by
        rw [supOn]
        exact le_ciSup hW_bdd ⟨Tᵢ, hTᵢW⟩
      simpa [hTᵢ, hTstar_sup] using hle_sup
    have hr_le_star : r ≤ Func Tstar := by
      exact ciSup_le hf_le_star
    exact False.elim ((not_lt_of_ge hr_le_star) hTstarW)

/-- **Theorem 4.7** (tex:1308-1317, `\label{th:geom-charac}`).

Let `V` be a complex vector space, `F : V → ℝ` Zariski-LSC. The following are equivalent:

(a) `{F(T) : T ∈ V}` is discrete from below.

(b) For every `r ∈ ℝ`, `V_{=r} = {T : F(T) = r}` is Zariski-open in
    `V_{≤r} = {T : F(T) ≤ r}`. -/
theorem discreteFromBelow_iff_levelSet_open
    (Func : V → ℝ) (hF : ZariskiLSC Func) :
    IsDiscreteFromBelow (Set.range Func)
      ↔
    (∀ r : ℝ, IsZariskiOpenIn { T : V | Func T = r } { T : V | Func T ≤ r }) := by
  constructor
  · exact levelSet_open_of_discreteFromBelow Func hF
  · exact discreteFromBelow_of_levelSet_open Func hF

/-- **Corollary 4.8 input from Corollary 2.4** (tex:1363, using tex:722-727).

For fixed tensor format over `ℂ`, asymptotic rank has Zariski-closed sublevel
sets, hence is Zariski-LSC. -/
lemma asympRank_zariskiLSC {k : ℕ} (d : Fin k → ℕ+) :
    ZariskiLSC (fun T : KTensor ℂ d => asympRank T) := by
  intro r
  classical
  by_cases hk : 1 ≤ k
  · unfold asympRank
    simp only [dif_pos hk]
    exact sublevel_zariski_closed (tensorRankAdmissible ℂ hk d) r
  · have hconst :
        { T : KTensor ℂ d | asympRank T ≤ r } =
          if 0 ≤ r then Set.univ else ∅ := by
      ext T
      simp [asympRank, hk]
    rw [hconst]
    split_ifs
    · exact zariskiClosed_univ_set
    · exact zariskiClosed_empty_set

set_option linter.flexible false in
/-- **Corollary 4.8 discreteness reduction** (tex:1353-1364, using Corollary 2.5).

For fixed tensor format, asymptotic-rank values are already discrete from above
by the well-ordering result, so pointwise discreteness is equivalent to
discreteness from below. -/
lemma asympRank_isDiscrete_iff_discreteFromBelow {k : ℕ} (d : Fin k → ℕ+) :
    IsDiscrete (Set.range fun T : KTensor ℂ d => asympRank T)
      ↔
    IsDiscreteFromBelow (Set.range fun T : KTensor ℂ d => asympRank T) := by
  classical
  constructor
  · intro hdisc
    have hclosed := asympRank_range_per_format_closed d
    have hbdd : BddAbove (Set.range fun T : KTensor ℂ d => asympRank T) := by
      have hF := asympRank_zariskiLSC d
      exact bddAbove_range_of_zariskiLSC (fun T : KTensor ℂ d => asympRank T) hF
    exact discreteFromBelow_of_isDiscrete_of_closed_of_bddAbove hdisc hclosed hbdd
  · intro hbelow
    by_cases hk : 1 ≤ k
    · let U : Set ℝ :=
        ⋃ d' : Fin k → ℕ+, Set.range (fun T : KTensor ℂ d' => asympRank T)
      have hSU :
          (Set.range fun T : KTensor ℂ d => asympRank T) ⊆ U := by
        intro x hx
        exact Set.mem_iUnion.mpr ⟨d, hx⟩
      have hWF : WellFoundedLT U := by
        simpa [U] using (asympRank_values_wellOrdered (F := ℂ) hk)
      exact isDiscrete_of_discreteFromBelow_of_wellFoundedLT hSU hWF hbelow
    · have hconst :
          (fun T : KTensor ℂ d => asympRank T) = fun _ => (0 : ℝ) := by
        funext T
        simp [asympRank, hk]
      rw [hconst]
      intro x hx
      refine ⟨1, by norm_num, ?_⟩
      intro y hy hyne
      simp at hx hy
      subst hx
      subst hy
      exact (hyne rfl).elim

/-- **Corollary 4.8** (tex:1353-1364, `\label{cor:asymprank-disc-equiv}`).

Let `V = ℂ^{d_1} ⊗ ⋯ ⊗ ℂ^{d_k}` with `d : Fin k → ℕ+`. The following are equivalent:

(a) `{R̃(T) : T ∈ V}` is discrete (i.e. every value is isolated; combines
    discreteness from above — known via Cor 2.5 — and from below).

(b) For every `r ∈ ℝ`, `V_{=r} = {T : R̃(T) = r}` is Zariski-open in
    `V_{≤r} = {T : R̃(T) ≤ r}`. -/
theorem asympRank_discreteFromBelow_iff {k : ℕ} (d : Fin k → ℕ+) :
    IsDiscrete (Set.range fun T : KTensor ℂ d => asympRank T)
      ↔
    (∀ r : ℝ,
      IsZariskiOpenIn
        { T : KTensor ℂ d | asympRank T = r }
        { T : KTensor ℂ d | asympRank T ≤ r }) := by
  exact (asympRank_isDiscrete_iff_discreteFromBelow d).trans
    (discreteFromBelow_iff_levelSet_open
      (fun T : KTensor ℂ d => asympRank T)
      (asympRank_zariskiLSC d))

end Semicontinuity

