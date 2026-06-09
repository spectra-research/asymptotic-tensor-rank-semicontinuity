/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.BaireProperty
import AsymptoticTensorRankSemicontinuity.SpectrumDescend
import AsymptoticTensorRankSemicontinuity.ZariskiSublevel
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# §4.1 Euclidean closedness over ℂ

Source: the semicontinuity manuscript,
lines 1095-1267.

* `ZariskiLSC` — Definition (tex:1149).
* `irreducible_variety_maximizers_dense` — **Theorem 4.3** (tex:1153-1164,
  `\label{thm:irreducible-variety-rank-maximizers-dense-general}`).
* `exists_maximizer` — **Corollary 4.4** (tex:1165-1173, `\label{cor:exist-max-general}`).
* `values_euclidean_closed` — **Corollary 4.5** (tex:1174-1184, `\label{cor:eucl-cl-general}`).
* `asympRank_values_euclidean_closed` — **Theorem 4.1** (tex:1089-1094, `\label{cor:closed}`).
* `asympSpectrum_values_euclidean_closed` — **Corollary 4.6** (tex:1250-1260,
  `\label{cor:spec-eucl-closed}`).
-/

namespace Semicontinuity

universe u v

variable {V : Type v} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]

/-- **Zariski lower semicontinuity** (tex:1149).

A function `F : V → ℝ` is Zariski-LSC if every sublevel set
`{T ∈ V : F(T) ≤ r}` is Zariski-closed. -/
def ZariskiLSC (Func : V → ℝ) : Prop :=
  ∀ r : ℝ, IsZariskiClosed (F := ℂ) { T : V | Func T ≤ r }

/-- `F[A] = sup_{T ∈ A} F(T)` (tex:1152). -/
noncomputable def supOn (Func : V → ℝ) (A : Set V) : ℝ :=
  ⨆ T : A, Func T

/-! ## Irreducibility (tex:1155 + standard AG). -/

/-- An affine subset `X ⊆ V` is **Zariski-irreducible** if it cannot be written as
    the union of two proper Zariski-closed subsets. -/
def IsZariskiIrreducible (X : Set V) : Prop :=
  X.Nonempty ∧ IsZariskiClosed (F := ℂ) X ∧
    ∀ Y Z : Set V, IsZariskiClosed (F := ℂ) Y → IsZariskiClosed (F := ℂ) Z →
      X ⊆ Y ∪ Z → X ⊆ Y ∨ X ⊆ Z

/-! ## Theorem 4.3 (tex:1153-1164): maximizers are Zariski-dense in irreducibles. -/

lemma zariskiClosure_closed (A : Set V) :
    IsZariskiClosed (F := ℂ) (zariskiClosure (F := ℂ) A) := by
  apply Set.eq_of_subset_of_subset
  · intro T hT f hf hfA
    refine hT f hf ?_
    intro S hS
    exact hS f hf hfA
  · exact subset_zariskiClosure (F := ℂ) (zariskiClosure (F := ℂ) A)

lemma zariskiClosure_empty :
    zariskiClosure (F := ℂ) (∅ : Set V) = ∅ := by
  ext T
  constructor
  · intro hT
    have hOne : (fun _ : V => (1 : ℂ)) T = 0 := by
      refine hT (fun _ : V => (1 : ℂ)) ?_ ?_
      · refine ⟨MvPolynomial.C 1, ?_⟩
        intro S
        simp
      · intro S hS
        simp at hS
    exact (one_ne_zero hOne).elim
  · intro hT
    simp at hT

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

lemma zariskiDenseIn_nonempty {U X : Set V}
    (h_dense : IsZariskiDenseIn U X) (hX_ne : X.Nonempty) :
    U.Nonempty := by
  by_contra hU
  rw [Set.not_nonempty_iff_eq_empty] at hU
  obtain ⟨T, hTX⟩ := hX_ne
  have hT : T ∈ zariskiClosure (F := ℂ) U := h_dense hTX
  rw [hU, zariskiClosure_empty] at hT
  exact hT

lemma zariskiOpenIn_dense_of_irreducible {U X : Set V}
    (hX_irr : IsZariskiIrreducible X)
    (hU_open : IsZariskiOpenIn U X) (hU_ne : U.Nonempty) :
    IsZariskiDenseIn U X := by
  rcases hX_irr with ⟨hX_ne, hX_closed, hX_irred⟩
  rcases hU_open with ⟨hUX, C, hC_closed, hdiff⟩
  have hcover : X ⊆ C ∪ zariskiClosure (F := ℂ) U := by
    intro T hTX
    by_cases hTU : T ∈ U
    · exact Or.inr (subset_zariskiClosure (F := ℂ) U hTU)
    · left
      have hTdiff : T ∈ X \ U := ⟨hTX, hTU⟩
      have hTC : T ∈ X ∩ C := by
        simpa [hdiff] using hTdiff
      exact hTC.2
  have hclosed_closure : IsZariskiClosed (F := ℂ) (zariskiClosure (F := ℂ) U) :=
    zariskiClosure_closed (V := V) U
  rcases hX_irred C (zariskiClosure (F := ℂ) U) hC_closed hclosed_closure hcover with
    hXC | hXclosure
  · obtain ⟨T, hTU⟩ := hU_ne
    have hTX : T ∈ X := hUX hTU
    have hTdiff : T ∈ X \ U := by
      rw [hdiff]
      exact ⟨hTX, hXC hTX⟩
    exact (hTdiff.2 hTU).elim
  · exact hXclosure

lemma zariskiOpenIn_gt_of_lsc
    (Func : V → ℝ) (hF : ZariskiLSC Func) (X : Set V) (r : ℝ) :
    IsZariskiOpenIn { T ∈ X | r < Func T } X := by
  refine ⟨?_, { T : V | Func T ≤ r }, hF r, ?_⟩
  · intro T hT
    exact hT.1
  · ext T
    simp [not_lt]

lemma bddAbove_image_of_zariskiLSC_irreducible
    (Func : V → ℝ) (hF : ZariskiLSC Func)
    (X : Set V) (hX_irr : IsZariskiIrreducible X) :
    BddAbove (Func '' X) := by
  classical
  rcases hX_irr with ⟨hX_ne, hX_closed, hX_irred⟩
  by_contra h_unbdd
  have hU_open : ∀ n : ℕ, IsZariskiOpenIn { T ∈ X | (n : ℝ) < Func T } X :=
    fun n => zariskiOpenIn_gt_of_lsc Func hF X n
  have hU_ne : ∀ n : ℕ, ({ T ∈ X | (n : ℝ) < Func T } : Set V).Nonempty := by
    intro n
    by_contra h_empty
    apply h_unbdd
    refine ⟨(n : ℝ), ?_⟩
    rintro y ⟨T, hTX, rfl⟩
    by_contra hle
    have hT : T ∈ ({ T ∈ X | (n : ℝ) < Func T } : Set V) := ⟨hTX, lt_of_not_ge hle⟩
    rw [Set.not_nonempty_iff_eq_empty] at h_empty
    rw [h_empty] at hT
    exact hT
  have hU_dense : ∀ n : ℕ, IsZariskiDenseIn { T ∈ X | (n : ℝ) < Func T } X :=
    fun n => zariskiOpenIn_dense_of_irreducible
      ⟨hX_ne, hX_closed, hX_irred⟩ (hU_open n) (hU_ne n)
  have hInter_dense :
      IsZariskiDenseIn (⋂ n : ℕ, { T ∈ X | (n : ℝ) < Func T }) X :=
    zariski_baire X hX_ne hX_closed
      (fun n : ℕ => { T ∈ X | (n : ℝ) < Func T }) hU_open hU_dense
  obtain ⟨T, hT⟩ := zariskiDenseIn_nonempty hInter_dense hX_ne
  obtain ⟨n, hn⟩ := exists_nat_gt (Func T)
  have hnT : (n : ℝ) < Func T := (Set.mem_iInter.mp hT n).2
  exact not_lt_of_ge hn.le hnT

/-- **Theorem 4.3** (tex:1153-1164,
    `\label{thm:irreducible-variety-rank-maximizers-dense-general}`).

For a non-empty Zariski-closed irreducible `X ⊆ V` and a Zariski-LSC `F : V → ℝ`,
the set `{T ∈ X : F(T) = F[X]}` is Zariski-dense in `X`, in particular
non-empty, and `F[X] < ⊤`. -/
theorem irreducible_variety_maximizers_dense
    (Func : V → ℝ) (hF : ZariskiLSC Func)
    (X : Set V) (hX_irr : IsZariskiIrreducible X) :
    IsZariskiDenseIn { T ∈ X | Func T = supOn Func X } X
    ∧ { T ∈ X | Func T = supOn Func X }.Nonempty
    ∧ BddAbove (Func '' X) := by
  classical
  rcases hX_irr with ⟨hX_ne, hX_closed, hX_irred⟩
  haveI : Nonempty X := hX_ne.to_subtype
  have hbdd : BddAbove (Func '' X) :=
    bddAbove_image_of_zariskiLSC_irreducible Func hF X ⟨hX_ne, hX_closed, hX_irred⟩
  have hbdd_subtype : BddAbove (Set.range fun T : X => Func T) := by
    rcases hbdd with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rintro y ⟨T, rfl⟩
    exact hb ⟨T.1, T.2, rfl⟩
  obtain ⟨r, _hr_strict, hr_lt, hr_tendsto⟩ :=
    exists_seq_strictMono_tendsto (supOn Func X)
  let U : ℕ → Set V := fun i => { T ∈ X | r i < Func T }
  have hU_open : ∀ i, IsZariskiOpenIn (U i) X := by
    intro i
    exact zariskiOpenIn_gt_of_lsc Func hF X (r i)
  have hU_ne : ∀ i, (U i).Nonempty := by
    intro i
    have hlt : r i < ⨆ T : X, Func T := by
      simpa [supOn] using hr_lt i
    rcases (lt_ciSup_iff hbdd_subtype).mp hlt with ⟨T, hT⟩
    exact ⟨T.1, T.2, hT⟩
  have hU_dense : ∀ i, IsZariskiDenseIn (U i) X := by
    intro i
    exact zariskiOpenIn_dense_of_irreducible
      ⟨hX_ne, hX_closed, hX_irred⟩ (hU_open i) (hU_ne i)
  have hInter_dense : IsZariskiDenseIn (⋂ i, U i) X :=
    zariski_baire X hX_ne hX_closed U hU_open hU_dense
  have hInter_eq :
      (⋂ i, U i) = { T ∈ X | Func T = supOn Func X } := by
    ext T
    constructor
    · intro hT
      have hT0 : T ∈ U 0 := Set.mem_iInter.mp hT 0
      have hTX : T ∈ X := hT0.1
      have hle : supOn Func X ≤ Func T := by
        rw [supOn]
        exact le_of_tendsto_of_tendsto hr_tendsto tendsto_const_nhds
          (Filter.Eventually.of_forall fun i => (Set.mem_iInter.mp hT i).2.le)
      have hge : Func T ≤ supOn Func X := by
        rw [supOn]
        exact le_ciSup hbdd_subtype ⟨T, hTX⟩
      exact ⟨hTX, le_antisymm hge hle⟩
    · intro hT
      rw [Set.mem_iInter]
      intro i
      exact ⟨hT.1, by simpa [hT.2] using hr_lt i⟩
  have h_dense : IsZariskiDenseIn { T ∈ X | Func T = supOn Func X } X := by
    simpa [← hInter_eq] using hInter_dense
  exact ⟨h_dense, zariskiDenseIn_nonempty h_dense hX_ne, hbdd⟩

/-! ## Corollary 4.4 (tex:1165-1173): existence of a maximizer. -/

private abbrev ZariskiClosedSet (V : Type v) [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] :=
  { A : Set V // IsZariskiClosed (F := ℂ) A }

private def zariskiClosedProperSubset (A B : ZariskiClosedSet V) : Prop :=
  A.1 ⊂ B.1

private lemma zariskiClosedProperSubset_wf :
    WellFounded (zariskiClosedProperSubset (V := V)) := by
  classical
  let R := MvPolynomial (Fin (Module.finrank ℂ V)) ℂ
  haveI : IsNoetherianRing R := MvPolynomial.isNoetherianRing_fin
  let I : ZariskiClosedSet V → Ideal R :=
    fun A => vanishingIdeal (F := ℂ) (V := V) A.1
  refine Subrelation.wf (r := InvImage ((· > ·) : Ideal R → Ideal R → Prop) I) ?_
    (InvImage.wf I (inferInstance : WellFoundedGT (Ideal R)).wf)
  intro A B hAB
  dsimp [zariskiClosedProperSubset] at hAB
  dsimp [InvImage, I]
  have hle : vanishingIdeal (F := ℂ) (V := V) B.1 ≤
      vanishingIdeal (F := ℂ) (V := V) A.1 :=
    vanishingIdeal_antitone hAB.1
  refine lt_of_le_of_ne hle ?_
  intro hEq
  apply hAB.2
  have hsets : A.1 = B.1 :=
    eq_of_vanishingIdeal_eq (F := ℂ) (V := V) A.2 B.2 hAB.1 hEq.symm
  exact hsets ▸ subset_rfl

/-- Every non-empty Zariski-closed set has a finite decomposition into
    irreducible Zariski-closed components. Follows from Noetherianity of
    the Zariski topology on a finite-dimensional vector space over ℂ
    (`MvPolynomial.isNoetherianRing`). Paper tex:1169. -/
lemma IsZariskiClosed.exists_irreducible_decomposition
    (X : Set V) (hX_ne : X.Nonempty) (hX_closed : IsZariskiClosed (F := ℂ) X) :
    ∃ (s : Finset (Set V)), s.Nonempty ∧ X = ⋃ Y ∈ s, Y ∧
      ∀ Y ∈ s, IsZariskiClosed (F := ℂ) Y ∧ IsZariskiIrreducible Y := by
  classical
  let P : ZariskiClosedSet V → Prop := fun X =>
    X.1.Nonempty →
      ∃ (s : Finset (Set V)), s.Nonempty ∧ X.1 = ⋃ Y ∈ s, Y ∧
        ∀ Y ∈ s, IsZariskiClosed (F := ℂ) Y ∧ IsZariskiIrreducible Y
  have hP : ∀ X : ZariskiClosedSet V,
      (∀ Y : ZariskiClosedSet V, zariskiClosedProperSubset Y X → P Y) → P X := by
    intro X ih hX_ne
    by_cases hX_irred : IsZariskiIrreducible X.1
    · refine ⟨{X.1}, by simp, ?_, ?_⟩
      · ext T
        simp
      · intro Y hY
        simp only [Finset.mem_singleton] at hY
        subst hY
        exact ⟨X.2, hX_irred⟩
    · have hnot :
          ¬ ∀ Y Z : Set V, IsZariskiClosed (F := ℂ) Y → IsZariskiClosed (F := ℂ) Z →
            X.1 ⊆ Y ∪ Z → X.1 ⊆ Y ∨ X.1 ⊆ Z := by
        intro h
        exact hX_irred ⟨hX_ne, X.2, h⟩
      push_neg at hnot
      rcases hnot with ⟨Y, Z, hY_closed, hZ_closed, hcover, hX_not_Y, hX_not_Z⟩
      let XY : ZariskiClosedSet V :=
        ⟨X.1 ∩ Y, zariskiClosed_inter X.2 hY_closed⟩
      let XZ : ZariskiClosedSet V :=
        ⟨X.1 ∩ Z, zariskiClosed_inter X.2 hZ_closed⟩
      have hXY_ssub : zariskiClosedProperSubset XY X := by
        constructor
        · intro T hT
          exact hT.1
        · intro h
          exact hX_not_Y fun T hTX => (h hTX).2
      have hXZ_ssub : zariskiClosedProperSubset XZ X := by
        constructor
        · intro T hT
          exact hT.1
        · intro h
          exact hX_not_Z fun T hTX => (h hTX).2
      have hXY_ne : XY.1.Nonempty := by
        rcases Set.not_subset.mp hX_not_Z with ⟨T, hTX, hTZ⟩
        have hTY : T ∈ Y := by
          rcases hcover hTX with hTY | hTZ'
          · exact hTY
          · exact (hTZ hTZ').elim
        exact ⟨T, hTX, hTY⟩
      have hXZ_ne : XZ.1.Nonempty := by
        rcases Set.not_subset.mp hX_not_Y with ⟨T, hTX, hTY⟩
        have hTZ : T ∈ Z := by
          rcases hcover hTX with hTY' | hTZ
          · exact (hTY hTY').elim
          · exact hTZ
        exact ⟨T, hTX, hTZ⟩
      rcases ih XY hXY_ssub hXY_ne with ⟨sY, hsY_ne, hXY_union, hsY⟩
      rcases ih XZ hXZ_ssub hXZ_ne with ⟨sZ, hsZ_ne, hXZ_union, hsZ⟩
      refine ⟨sY ∪ sZ, Finset.Nonempty.inl hsY_ne, ?_, ?_⟩
      · ext T
        constructor
        · intro hTX
          rcases hcover hTX with hTY | hTZ
          · have hTXY : T ∈ XY.1 := ⟨hTX, hTY⟩
            rw [hXY_union] at hTXY
            rcases Set.mem_iUnion.mp hTXY with ⟨W, hW⟩
            rcases Set.mem_iUnion.mp hW with ⟨hWsY, hTW⟩
            exact Set.mem_iUnion.mpr ⟨W,
              Set.mem_iUnion.mpr ⟨Finset.mem_union.mpr (Or.inl hWsY), hTW⟩⟩
          · have hTXZ : T ∈ XZ.1 := ⟨hTX, hTZ⟩
            rw [hXZ_union] at hTXZ
            rcases Set.mem_iUnion.mp hTXZ with ⟨W, hW⟩
            rcases Set.mem_iUnion.mp hW with ⟨hWsZ, hTW⟩
            exact Set.mem_iUnion.mpr ⟨W,
              Set.mem_iUnion.mpr ⟨Finset.mem_union.mpr (Or.inr hWsZ), hTW⟩⟩
        · intro hT
          rcases Set.mem_iUnion.mp hT with ⟨W, hW⟩
          rcases Set.mem_iUnion.mp hW with ⟨hWs, hTW⟩
          rcases Finset.mem_union.mp hWs with hWsY | hWsZ
          · have hTWXY : T ∈ XY.1 := by
              rw [hXY_union]
              exact Set.mem_iUnion.mpr ⟨W, Set.mem_iUnion.mpr ⟨hWsY, hTW⟩⟩
            exact hTWXY.1
          · have hTWXZ : T ∈ XZ.1 := by
              rw [hXZ_union]
              exact Set.mem_iUnion.mpr ⟨W, Set.mem_iUnion.mpr ⟨hWsZ, hTW⟩⟩
            exact hTWXZ.1
      · intro W hWs
        rcases Finset.mem_union.mp hWs with hWsY | hWsZ
        · exact hsY W hWsY
        · exact hsZ W hWsZ
  exact (zariskiClosedProperSubset_wf (V := V)).induction ⟨X, hX_closed⟩ hP hX_ne

/-- **Corollary 4.4** (tex:1165-1173, `\label{cor:exist-max-general}`).

For non-empty Zariski-closed `X ⊆ V` and Zariski-LSC `F : V → ℝ`,
there exists `T ∈ X` with `F(T) = F[X]`. -/
theorem exists_maximizer
    (Func : V → ℝ) (hF : ZariskiLSC Func)
    (X : Set V) (hX_ne : X.Nonempty) (hX_closed : IsZariskiClosed (F := ℂ) X) :
    ∃ T ∈ X, Func T = supOn Func X := by
  classical
  haveI : Nonempty X := hX_ne.to_subtype
  obtain ⟨s, hs_ne, hX_union, hs_irred⟩ :=
    IsZariskiClosed.exists_irreducible_decomposition (V := V) X hX_ne hX_closed
  obtain ⟨Y₀, hY₀s, hY₀_max⟩ :=
    Finset.exists_max_image s (fun Y => supOn Func Y) hs_ne
  have hY₀_irr : IsZariskiIrreducible Y₀ := (hs_irred Y₀ hY₀s).2
  obtain ⟨_, hY₀_maximizers_ne, _⟩ :=
    irreducible_variety_maximizers_dense Func hF Y₀ hY₀_irr
  obtain ⟨T₀, hT₀_mem⟩ := hY₀_maximizers_ne
  rcases hT₀_mem with ⟨hT₀Y₀, hT₀_supY₀⟩
  have hT₀X : T₀ ∈ X := by
    rw [hX_union]
    exact Set.mem_iUnion.mpr ⟨Y₀, Set.mem_iUnion.mpr ⟨hY₀s, hT₀Y₀⟩⟩
  have hpoint_le_Y₀ : ∀ T ∈ X, Func T ≤ supOn Func Y₀ := by
    intro T hTX
    have hT_union : T ∈ ⋃ Y ∈ s, Y := by
      simpa [hX_union] using hTX
    rcases Set.mem_iUnion.mp hT_union with ⟨Y, hT_mem_Ys⟩
    rcases Set.mem_iUnion.mp hT_mem_Ys with ⟨hYs, hTY⟩
    have hY_irr : IsZariskiIrreducible Y := (hs_irred Y hYs).2
    have hbddY_image : BddAbove (Func '' Y) :=
      (irreducible_variety_maximizers_dense Func hF Y hY_irr).2.2
    have hbddY_subtype : BddAbove (Set.range fun T : Y => Func T) := by
      rcases hbddY_image with ⟨b, hb⟩
      refine ⟨b, ?_⟩
      rintro y ⟨T, rfl⟩
      exact hb ⟨T.1, T.2, rfl⟩
    have hT_le_supY : Func T ≤ supOn Func Y := by
      rw [supOn]
      exact le_ciSup hbddY_subtype ⟨T, hTY⟩
    exact hT_le_supY.trans (hY₀_max Y hYs)
  have hsupX_le_supY₀ : supOn Func X ≤ supOn Func Y₀ := by
    rw [supOn]
    exact ciSup_le fun T : X => hpoint_le_Y₀ T.1 T.2
  have hbddX_subtype : BddAbove (Set.range fun T : X => Func T) := by
    refine ⟨supOn Func Y₀, ?_⟩
    rintro y ⟨T, rfl⟩
    exact hpoint_le_Y₀ T.1 T.2
  have hT₀_le_supX : Func T₀ ≤ supOn Func X := by
    rw [supOn]
    exact le_ciSup hbddX_subtype ⟨T₀, hT₀X⟩
  have hsupX_le_T₀ : supOn Func X ≤ Func T₀ := by
    simpa [hT₀_supY₀] using hsupX_le_supY₀
  exact ⟨T₀, hT₀X, le_antisymm hT₀_le_supX hsupX_le_T₀⟩

/-! ## Corollary 4.5 (tex:1174-1184): values are Euclidean-closed. -/

private lemma zariskiLSC_range_wellFoundedLT
    (Func : V → ℝ) (hF : ZariskiLSC Func) :
    WellFoundedLT (Set.range Func) := by
  classical
  refine ⟨?_⟩
  rw [RelEmbedding.wellFounded_iff_isEmpty]
  refine ⟨fun e => ?_⟩
  set r : ℕ → ℝ := fun k => (e k : ℝ) with hr_def
  have hr_anti : StrictAnti r := by
    intro k m hkm
    exact e.map_rel_iff.mpr (show m > k from hkm)
  have hr_mem : ∀ k, r k ∈ Set.range Func := fun k => (e k).2
  choose T hT using hr_mem
  let A : ℕ → Set V := fun k => { S : V | Func S ≤ r k }
  have hA_closed : ∀ k, IsZariskiClosed (F := ℂ) (A k) := by
    intro k
    simpa [A] using hF (r k)
  have hA_anti : Antitone A := by
    intro k m hkm S hS
    exact hS.trans (hr_anti.antitone hkm)
  let I : ℕ → Ideal (MvPolynomial (Fin (Module.finrank ℂ V)) ℂ) :=
    fun k => vanishingIdeal (F := ℂ) (V := V) (A k)
  have hI_mono : Monotone I := by
    intro k m hkm
    exact vanishingIdeal_antitone (hA_anti hkm)
  haveI : IsNoetherianRing (MvPolynomial (Fin (Module.finrank ℂ V)) ℂ) :=
    MvPolynomial.isNoetherianRing_fin
  obtain ⟨N, hN⟩ :=
    (monotone_stabilizes_iff_noetherian
      (R := MvPolynomial (Fin (Module.finrank ℂ V)) ℂ)
      (M := MvPolynomial (Fin (Module.finrank ℂ V)) ℂ)).mpr
      inferInstance ⟨I, hI_mono⟩
  have hI_eq : I N = I (N + 1) := hN (N + 1) (Nat.le_succ N)
  have hA_eq_succ : A (N + 1) = A N :=
    eq_of_vanishingIdeal_eq
      (hA_closed (N + 1))
      (hA_closed N)
      (hA_anti (Nat.le_succ N))
      (by simp only [I] at hI_eq; exact hI_eq.symm)
  have hA_eq : A N = A (N + 1) := hA_eq_succ.symm
  have hT_N_in_A_N : T N ∈ A N := by
    change Func (T N) ≤ r N
    rw [hT N]
  have hT_N_le : Func (T N) ≤ r (N + 1) := by
    have : T N ∈ A (N + 1) := hA_eq ▸ hT_N_in_A_N
    exact this
  have hr_succ_lt : r (N + 1) < r N := hr_anti (Nat.lt_succ_self N)
  exact not_lt_of_ge (by simpa [hT N] using hT_N_le) hr_succ_lt

private lemma exists_gap_above_of_wellFoundedLT'
    {S : Set ℝ} (hWF : WellFoundedLT S) (r : ℝ) :
    ∃ ε > 0, ∀ y ∈ S, r < y → ε ≤ y - r := by
  classical
  let B : Set S := { y : S | r < (y : ℝ) }
  by_cases hB : B.Nonempty
  · obtain ⟨m, hmB, hm_min⟩ := hWF.wf.has_min B hB
    refine ⟨(m : ℝ) - r, sub_pos.mpr hmB, ?_⟩
    intro y hyS hry
    let yu : S := ⟨y, hyS⟩
    have hyuB : yu ∈ B := hry
    have hnot_lt : ¬ (yu : ℝ) < (m : ℝ) := hm_min yu hyuB
    exact sub_le_sub_right (le_of_not_gt hnot_lt) r
  · refine ⟨1, by norm_num, ?_⟩
    intro y hyS hry
    exact (hB ⟨⟨y, hyS⟩, hry⟩).elim

private lemma isClosed_of_increasing_limits_of_wellFoundedLT
    {S : Set ℝ} (hWF : WellFoundedLT S)
    (h_increasing_limit_attained :
      ∀ (r : ℝ) (u : ℕ → ℝ), StrictMono u →
        Filter.Tendsto u Filter.atTop (nhds r) →
        (∀ i, u i ∈ S) → r ∈ S) :
    IsClosed S := by
  classical
  apply isClosed_of_closure_subset
  intro r hr_closure
  by_contra hr_not
  have hbelow_or_gap :
      (∀ a : ℝ, a < r → ∃ s ∈ S, a ≤ s ∧ s < r) ∨
        ∃ a : ℝ, a < r ∧ ∀ s ∈ S, s < r → s < a := by
    by_cases h : ∀ a : ℝ, a < r → ∃ s ∈ S, a ≤ s ∧ s < r
    · exact Or.inl h
    · push_neg at h
      rcases h with ⟨a, har, ha⟩
      refine Or.inr ⟨a, har, ?_⟩
      intro s hsS hsr
      exact lt_of_not_ge (fun has => not_lt_of_ge (ha s hsS has) hsr)
  rcases hbelow_or_gap with hbelow_dense | hbelow_gap
  · have hinit_exists : ∃ s : ℝ, s ∈ S ∧ r - 1 ≤ s ∧ s < r := by
      have hlt : r - 1 < r := by norm_num
      rcases hbelow_dense (r - 1) hlt with ⟨s, hsS, hsle, hslt⟩
      exact ⟨s, hsS, hsle, hslt⟩
    let A : Type := { s : ℝ // s ∈ S ∧ s < r }
    let a0 : A :=
      ⟨Classical.choose hinit_exists,
        (Classical.choose_spec hinit_exists).1,
        (Classical.choose_spec hinit_exists).2.2⟩
    have ha0_lower : r - 1 ≤ a0.1 := (Classical.choose_spec hinit_exists).2.1
    have hstep : ∀ n : ℕ, ∀ a : A,
        ∃ b : A, max ((a.1 + r) / 2) (r - 1 / (((n + 1 : ℕ) : ℝ) + 1)) ≤ b.1 := by
      intro n a
      have hmid_lt : (a.1 + r) / 2 < r := by linarith [a.2.2]
      have htail_lt : r - 1 / (((n + 1 : ℕ) : ℝ) + 1) < r := by
        have hpos : 0 < (1 : ℝ) / (((n + 1 : ℕ) : ℝ) + 1) := by positivity
        linarith
      have hmax_lt : max ((a.1 + r) / 2) (r - 1 / (((n + 1 : ℕ) : ℝ) + 1)) < r :=
        max_lt hmid_lt htail_lt
      rcases hbelow_dense _ hmax_lt with ⟨s, hsS, hsle, hslt⟩
      exact ⟨⟨s, hsS, hslt⟩, hsle⟩
    let next : ℕ → A → A := fun n a => Classical.choose (hstep n a)
    have hnext : ∀ n a,
        max ((a.1 + r) / 2) (r - 1 / (((n + 1 : ℕ) : ℝ) + 1)) ≤ (next n a).1 := by
      intro n a
      exact Classical.choose_spec (hstep n a)
    let fA : ℕ → A := fun n => Nat.rec a0 (fun n a => next n a) n
    let u : ℕ → ℝ := fun n => (fA n).1
    have hu_mem : ∀ n, u n ∈ S := fun n => (fA n).2.1
    have hu_lt_r : ∀ n, u n < r := fun n => (fA n).2.2
    have hu_succ_lower : ∀ n, max ((u n + r) / 2)
        (r - 1 / (((n + 1 : ℕ) : ℝ) + 1)) ≤ u (n + 1) := by
      intro n
      simpa [u, fA, next] using hnext n (fA n)
    have hu_strict : StrictMono u := by
      refine strictMono_nat_of_lt_succ ?_
      intro n
      have hmid_le : (u n + r) / 2 ≤ u (n + 1) :=
        (le_max_left _ _).trans (hu_succ_lower n)
      have hlt_mid : u n < (u n + r) / 2 := by linarith [hu_lt_r n]
      exact hlt_mid.trans_le hmid_le
    have hu_lower : ∀ n, r - 1 / (((n : ℕ) : ℝ) + 1) ≤ u n := by
      intro n
      cases n with
      | zero =>
          simpa [u, fA] using ha0_lower
      | succ n =>
          have htail_le : r - 1 / (((n + 1 : ℕ) : ℝ) + 1) ≤ u (n + 1) :=
            (le_max_right _ _).trans (hu_succ_lower n)
          simpa using htail_le
    have htend_lower :
        Filter.Tendsto (fun n : ℕ => r - 1 / (((n : ℕ) : ℝ) + 1))
          Filter.atTop (nhds r) := by
      simpa using (tendsto_const_nhds.sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    have htend_upper : Filter.Tendsto (fun _ : ℕ => r) Filter.atTop (nhds r) :=
      tendsto_const_nhds
    have hu_tend : Filter.Tendsto u Filter.atTop (nhds r) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le htend_lower htend_upper
        hu_lower (fun n => le_of_lt (hu_lt_r n))
    · exact hr_not (h_increasing_limit_attained r u hu_strict hu_tend hu_mem)
  · rcases hbelow_gap with ⟨a, har, hgap_below⟩
    rcases exists_gap_above_of_wellFoundedLT' hWF r with ⟨ε, hεpos, hgap_above⟩
    let δ := min (r - a) ε
    have hδpos : 0 < δ := lt_min (sub_pos.mpr har) hεpos
    rcases Real.mem_closure_iff.mp hr_closure δ hδpos with ⟨y, hyS, hyδ⟩
    have hdist_lower : δ ≤ |y - r| := by
      by_cases hyr : y < r
      · have hya : y < a := hgap_below y hyS hyr
        have hle : r - a ≤ |y - r| := by
          rw [abs_of_neg]
          · linarith
          · linarith
        exact (min_le_left _ _).trans hle
      · have hry : r < y := lt_of_le_of_ne (le_of_not_gt hyr) (by
          intro h
          exact hr_not (h ▸ hyS))
        have hle : ε ≤ |y - r| := by
          rw [abs_of_pos]
          · exact hgap_above y hyS hry
          · linarith
        exact (min_le_right _ _).trans hle
    exact not_lt_of_ge hdist_lower hyδ

/-- Noetherian bridge for the decreasing branch of Corollary 4.5 (paper tex:1179).

The increasing-limit branch is proved directly from `exists_maximizer` in
`values_euclidean_closed`.  The remaining branch is the standard Noetherian
argument: for a decreasing convergent sequence of values, the closed sublevel
sets `{T | Func T ≤ r_i}` form a descending chain; Noetherianity of the Zariski
topology stabilizes the chain, forcing the values to stabilize at the limit. -/
private lemma values_euclidean_closed_noetherian_decreasing_bridge
    (Func : V → ℝ) (hF : ZariskiLSC Func)
    (h_increasing_limit_attained :
      ∀ (r : ℝ) (u : ℕ → ℝ), StrictMono u →
        Filter.Tendsto u Filter.atTop (nhds r) →
        (∀ i, u i ∈ Set.range Func) → r ∈ Set.range Func) :
    IsClosed (Set.range Func) := by
  exact isClosed_of_increasing_limits_of_wellFoundedLT
    (zariskiLSC_range_wellFoundedLT Func hF)
    h_increasing_limit_attained

/-- **Corollary 4.5** (tex:1174-1184, `\label{cor:eucl-cl-general}`).

For any Zariski-LSC `F : V → ℝ`, the set `{F(T) : T ∈ V}` is Euclidean-closed in ℝ. -/
theorem values_euclidean_closed
    (Func : V → ℝ) (hF : ZariskiLSC Func) :
    IsClosed (Set.range Func) := by
  classical
  have h_increasing_limit_attained :
      ∀ (r : ℝ) (u : ℕ → ℝ), StrictMono u →
        Filter.Tendsto u Filter.atTop (nhds r) →
        (∀ i, u i ∈ Set.range Func) → r ∈ Set.range Func := by
    intro r u hu_strict hu_tend hu_range
    let S : Set V := { T : V | Func T ≤ r }
    have hu_mono : Monotone u := hu_strict.monotone
    have hu_le_limit : ∀ i, u i ≤ r := by
      intro i
      exact le_of_tendsto_of_tendsto tendsto_const_nhds hu_tend
        ((Filter.eventually_ge_atTop i).mono fun n hn => hu_mono hn)
    have hS_ne : S.Nonempty := by
      rcases hu_range 0 with ⟨T₀, hT₀⟩
      exact ⟨T₀, by simpa [S, hT₀] using hu_le_limit 0⟩
    have hS_closed : IsZariskiClosed (F := ℂ) S := by
      simpa [S] using hF r
    obtain ⟨Tstar, hTstarS, hTstar_sup⟩ :=
      exists_maximizer Func hF S hS_ne hS_closed
    have hS_bdd : BddAbove (Set.range fun T : S => Func T) := by
      refine ⟨r, ?_⟩
      rintro y ⟨T, rfl⟩
      exact T.2
    have hu_le_star : ∀ i, u i ≤ Func Tstar := by
      intro i
      rcases hu_range i with ⟨Tᵢ, hTᵢ⟩
      have hTᵢS : Tᵢ ∈ S := by
        simpa [S, hTᵢ] using hu_le_limit i
      have hTᵢ_le_sup : Func Tᵢ ≤ supOn Func S := by
        rw [supOn]
        exact le_ciSup hS_bdd ⟨Tᵢ, hTᵢS⟩
      simpa [hTᵢ, hTstar_sup] using hTᵢ_le_sup
    have h_limit_le_star : r ≤ Func Tstar :=
      le_of_tendsto_of_tendsto hu_tend tendsto_const_nhds
        (Filter.Eventually.of_forall hu_le_star)
    have h_star_le_limit : Func Tstar ≤ r := hTstarS
    exact ⟨Tstar, le_antisymm h_star_le_limit h_limit_le_star⟩
  have h_noetherian_decreasing_subcase : IsClosed (Set.range Func) := by
    exact values_euclidean_closed_noetherian_decreasing_bridge
      Func hF h_increasing_limit_attained
  exact h_noetherian_decreasing_subcase

/-! ## Theorem 4.1 (tex:1089-1094): asymptotic rank values are Euclidean-closed. -/

/-- Fixed-format asymptotic-rank values are Euclidean-closed.

This is Corollary 4.5 applied to the Zariski-LSC regularized tensor-rank
functional from Corollary 2.4. -/
lemma asympRank_range_per_format_closed {k : ℕ} (d : Fin k → ℕ+) :
    IsClosed (Set.range (fun T : KTensor ℂ d => asympRank T)) := by
  classical
  by_cases hk : 1 ≤ k
  · exact values_euclidean_closed
      (fun T : KTensor ℂ d => asympRank T) (by
        intro r
        unfold asympRank
        simp only [dif_pos hk]
        exact sublevel_zariski_closed (tensorRankAdmissible ℂ hk d) r)
  · have hconst :
        (fun T : KTensor ℂ d => asympRank T) = fun _ => (0 : ℝ) := by
      funext T
      simp [asympRank, hk]
    rw [hconst]
    simp

/-- **Theorem 4.1** (tex:1089-1094, `\label{cor:closed}`).

The set of asymptotic tensor ranks
`⋃ d : Fin k → ℕ+, {R̃(T) : T ∈ ℂ^{d_1} ⊗ ⋯ ⊗ ℂ^{d_k}}` is Euclidean-closed in ℝ. -/
theorem asympRank_values_euclidean_closed {k : ℕ} :
    IsClosed
      (⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor ℂ d => asympRank T)) := by
  classical
  -- paper tex:1235-1236: concise tensor with asympRank ≤ m has all dim_j ≤ m.
  --
  -- Here "concise" is represented by the API conclusion
  -- `∀ j, (d j : ℕ) = flatRank T {j}` from `exists_concise_restriction`.
  have h_concise_dims_le {d : Fin k → ℕ+} (T : KTensor ℂ d) {m : ℝ}
      (hflat : ∀ j, (d j : ℕ) = flatRank T {j}) (hT : asympRank T ≤ m) :
      ∀ j, ((d j : ℕ) : ℝ) ≤ m := by
    intro j
    have hdim_eq : ((d j : ℕ) : ℝ) = (flatRank T {j} : ℝ) := by
      exact_mod_cast hflat j
    calc
      ((d j : ℕ) : ℝ) = (flatRank T {j} : ℝ) := hdim_eq
      _ ≤ asympRank T := flatRank_le_asympRank T j
      _ ≤ m := hT
  have h_concise_dims_le_natCeil {d : Fin k → ℕ+} (T : KTensor ℂ d) {m : ℝ}
      (hflat : ∀ j, (d j : ℕ) = flatRank T {j}) (hT : asympRank T ≤ m) :
      ∀ j, (d j : ℕ) ≤ Nat.ceil m := by
    intro j
    have hreal : ((d j : ℕ) : ℝ) ≤ m := h_concise_dims_le T hflat hT j
    exact_mod_cast hreal.trans (Nat.le_ceil m)
  -- Global closure step: use `exists_concise_restriction`,
  -- `Restricts.asympRank_eq_of_equiv`, and `h_concise_dims_le_natCeil` to show
  -- every bounded part of the global value set lies in a finite union of fixed
  -- formats; close that finite union with `asympRank_range_per_format_closed`,
  -- then conclude via the sequential-closedness criterion in ℝ.
  let S : Set ℝ :=
    ⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor ℂ d => asympRank T)
  -- Bounded-format reduction: every value `≤ M` lies in a finite union of
  -- formats whose coordinates fit inside `Fin N` for `N := Nat.ceil M + 1`.
  have hbounded_format_reduction :
      ∀ M : ℝ, ∃ N : ℕ, 0 < N ∧
        S ∩ Set.Iic M ⊆
          ⋃ a : Fin k → Fin N,
            Set.range (fun T : KTensor ℂ
              (fun j => (⟨(a j).val + 1, Nat.succ_pos _⟩ : ℕ+)) =>
              asympRank T) := by
    intro M
    refine ⟨Nat.ceil M + 1, Nat.succ_pos _, ?_⟩
    rintro x ⟨hxS, hxM⟩
    simp only [S, Set.mem_iUnion, Set.mem_range] at hxS ⊢
    obtain ⟨d, T, hxT⟩ := hxS
    have hxT_le_M : asympRank T ≤ M := by simpa [hxT] using hxM
    by_cases hTzero : T = 0
    · -- Zero tensor: `asympRank T = 0`, realized in the all-coordinate-`1`
      -- bounded format (witnessed by `a j = 0`) by the zero tensor there.
      set a : Fin k → Fin (Nat.ceil M + 1) := fun _ => ⟨0, Nat.succ_pos _⟩
        with ha_def
      refine ⟨a, 0, ?_⟩
      rw [hTzero, asympRank_zero] at hxT
      rw [asympRank_zero]
      exact hxT
    · -- Nonzero tensor: pass to a concise equivalent `T'` of format `d'` with
      -- `d' j = flatRank T' {j} ≤ Nat.ceil M`, then re-embed into the bounded
      -- format `a` defined by `a j = d' j - 1` (so the bounded format equals
      -- `d'`).
      obtain ⟨d', T', hT'_T, hT_T', hflat⟩ := exists_concise_restriction T hTzero
      have hval_eq : asympRank T' = asympRank T :=
        Restricts.asympRank_eq_of_equiv hT'_T hT_T'
      have hT'_le_M : asympRank T' ≤ M := by rw [hval_eq]; exact hxT_le_M
      have hdim_le : ∀ j, (d' j : ℕ) ≤ Nat.ceil M :=
        h_concise_dims_le_natCeil T' hflat hT'_le_M
      set a : Fin k → Fin (Nat.ceil M + 1) :=
        fun j => ⟨(d' j : ℕ) - 1, by
          have hdpos : 1 ≤ (d' j : ℕ) := (d' j).2
          have := hdim_le j
          omega⟩ with ha_def
      have hfmt :
          (fun j => (⟨(a j).val + 1, Nat.succ_pos _⟩ : ℕ+)) = d' := by
        funext j
        apply PNat.coe_injective
        have hdpos : 1 ≤ (d' j : ℕ) := (d' j).2
        simp only [a, PNat.mk_coe]
        omega
      refine ⟨a, ?_⟩
      rw [hfmt]
      exact ⟨T', by rw [hval_eq, hxT]⟩
  -- Each fixed bounded format gives a closed range; the finite union is closed.
  have hfinite_union_closed :
      ∀ N : ℕ,
        IsClosed
          (⋃ a : Fin k → Fin N,
            Set.range (fun T : KTensor ℂ
              (fun j => (⟨(a j).val + 1, Nat.succ_pos _⟩ : ℕ+)) =>
              asympRank T)) := by
    intro N
    apply isClosed_iUnion_of_finite
    intro a
    exact asympRank_range_per_format_closed
      (fun j => (⟨(a j).val + 1, Nat.succ_pos _⟩ : ℕ+))
  -- Sequential-closedness wrap-up.
  rw [← isSeqClosed_iff_isClosed]
  intro x r hxS hxlim
  have hx_bdd : BddAbove (Set.range x) := hxlim.bddAbove_range
  obtain ⟨M, hM⟩ := hx_bdd
  obtain ⟨N, _hNpos, hsubN⟩ := hbounded_format_reduction M
  have hxN :
      ∀ n, x n ∈
        ⋃ a : Fin k → Fin N,
          Set.range (fun T : KTensor ℂ
            (fun j => (⟨(a j).val + 1, Nat.succ_pos _⟩ : ℕ+)) =>
            asympRank T) := by
    intro n
    exact hsubN ⟨by simpa [S] using hxS n, hM ⟨n, rfl⟩⟩
  have hrN :
      r ∈
        ⋃ a : Fin k → Fin N,
          Set.range (fun T : KTensor ℂ
            (fun j => (⟨(a j).val + 1, Nat.succ_pos _⟩ : ℕ+)) =>
            asympRank T) :=
    (hfinite_union_closed N).mem_of_tendsto hxlim (Filter.Eventually.of_forall hxN)
  simp only [Set.mem_iUnion, Set.mem_range] at hrN ⊢
  rcases hrN with ⟨a, T, hT⟩
  exact ⟨fun j => (⟨(a j).val + 1, Nat.succ_pos _⟩ : ℕ+), T, hT⟩

/-! ## Corollary 4.6 (tex:1250-1260): same for the asymptotic spectrum. -/

/-- Fixed-format spectral points are Zariski-LSC.

This is the bridge used at paper tex:1257.  Mathematically, a spectral point
`F ∈ Δ(ℂ,k)` belongs to the regularized-admissible-functional construction
(paper tex:783), so `F = F̃`; then Corollary 2.4 (`sublevel_zariski_closed`,
paper tex:722-727) gives Zariski-closed sublevel sets.

The helper below records the concrete fixed-format construction.  Its level-`n`
component evaluates the spectral point after regrouping
`(KTensor ℂ d)^{⊗ n}` as the ordinary `k`-tensor of format `formatPow d n`.
The `Real.toNNReal` coercion is the Lean-side packaging of the nonnegativity of
spectral points; multiplicativity under `⊠` is the paper tex:783 input that
makes the regularization equal to the original spectral point.

The F_1-boundedness helper `Fspec_le_prod_dims` below supplies the trivial
bound `Fspec X ≤ ∏ d'_i` (paper tex:534-536). -/
private lemma Fspec_le_prod_dims {k : ℕ} (hk : 1 ≤ k) {d' : Fin k → ℕ+}
    (Fspec : SpectralPoint k ℂ) (X : KTensor ℂ d') :
    Fspec.toFun X ≤ ∏ i, (d' i : ℕ) := by
  classical
  -- Enumerate the index set `∀ i, Fin (d' i)` by `Fin N`, `N = ∏ d'_i`.
  set Idx := ∀ i : Fin k, Fin (d' i) with hIdx
  set N : ℕ := Fintype.card Idx with hN
  have hcard : N = ∏ i, (d' i : ℕ) := by simp [hN, hIdx, Fintype.card_pi]
  -- `N ≥ 1` since each `d' i ≥ 1`.
  have hNpos : 0 < N := by
    rw [hcard]
    exact Finset.prod_pos (fun i _ => (d' i).pos)
  let e : Fin N ≃ Idx := (Fintype.equivFin Idx).symm
  -- `X ≤ₜ unitTensor ⟨N⟩`: each diagonal coordinate `c` of the unit tensor
  -- contributes the `c`-th standard-basis simple tensor of `X`.
  have hrestr : Restricts X (unitTensor (F := ℂ) (k := k) ⟨N, hNpos⟩) := by
    -- Leg matrices: leg `⟨0,hk⟩` carries the scalar `X (e c)`; other legs select
    -- the matching coordinate, so `∏ i, A i (jdx i) c = X (e c)` iff `jdx = e c`.
    refine ⟨fun i => fun (j : Fin (d' i)) (c : Fin N) =>
      if i = ⟨0, hk⟩ then (if j = (e c) i then X (e c) else 0)
                     else (if j = (e c) i then 1 else 0), ?_⟩
    intro jdx
    -- Goal (after unfolding Restricts): `X jdx = ∑ idx, (∏ A) * unitTensor idx`.
    -- Each `c`-diagonal product equals `if jdx = e c then X (e c) else 0`.
    have hterm : ∀ c : Fin N,
        (∏ i, (if i = ⟨0, hk⟩ then (if jdx i = (e c) i then X (e c) else 0)
                              else (if jdx i = (e c) i then 1 else 0)))
          = (if jdx = e c then X (e c) else 0) := by
      intro c
      by_cases h : jdx = e c
      · rw [h, if_pos rfl]
        rw [show (∏ i, (if i = (⟨0, hk⟩ : Fin k)
                  then (if (e c) i = (e c) i then X (e c) else 0)
                  else (if (e c) i = (e c) i then 1 else 0)))
              = ∏ i, if i = (⟨0, hk⟩ : Fin k) then X (e c) else 1 from
            Finset.prod_congr rfl (fun i _ => by simp)]
        rw [Finset.prod_ite_eq' (Finset.univ) (⟨0, hk⟩ : Fin k) (fun _ => X (e c))]
        simp
      · rw [if_neg h]
        have hex : ∃ i₀ : Fin k, jdx i₀ ≠ (e c) i₀ := by
          by_contra hne
          push_neg at hne
          exact h (funext hne)
        obtain ⟨i₀, hi₀⟩ := hex
        apply Finset.prod_eq_zero (Finset.mem_univ i₀)
        by_cases hi : i₀ = ⟨0, hk⟩ <;> simp [hi, hi₀]
    -- Step 1: `X jdx = ∑ c, if jdx = e c then X (e c) else 0` (bijection `e`).
    have hX_eq : X jdx
        = ∑ c : Fin N, (if jdx = e c then X (e c) else 0) := by
      rw [Finset.sum_eq_single (e.symm jdx)]
      · rw [Equiv.apply_symm_apply, if_pos rfl]
      · intro c _ hc
        have : jdx ≠ e c := by
          intro heq; apply hc
          rw [heq, Equiv.symm_apply_apply]
        rw [if_neg this]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    -- Step 2: fold the diagonal sum back into the full sum over the unit tensor.
    rw [hX_eq]
    refine Finset.sum_of_injOn (e := fun c : Fin N => (fun _ : Fin k => c))
      ?_ ?_ ?_ ?_
    · -- injectivity of the diagonal embedding
      intro a _ b _ hab
      have := congrFun hab ⟨0, hk⟩
      simpa using this
    · intro c _; exact Finset.mem_univ _
    · -- off-image terms (non-constant idx) have `unitTensor = 0`
      intro idx _ hidx
      have hne : ¬ (∀ i j : Fin k, idx i = idx j) := by
        intro hconst
        apply hidx
        refine ⟨idx ⟨0, hk⟩, by simp, ?_⟩
        funext i
        exact (hconst ⟨0, hk⟩ i)
      have huz : unitTensor (F := ℂ) (k := k) ⟨N, hNpos⟩ idx = 0 := by
        simp only [unitTensor]; rw [if_neg hne]
      rw [huz, mul_zero]
    · -- on the diagonal at `c`, the term reduces to `if jdx = e c then X (e c) else 0`
      intro c _
      have hud : unitTensor (F := ℂ) (k := k) ⟨N, hNpos⟩ (fun _ : Fin k => c) = 1 := by
        simp [unitTensor]
      simp only [hud, mul_one]
      exact (hterm c).symm
  -- Combine: Fspec X ≤ Fspec (unitTensor ⟨N⟩) = N = ∏ d'_i.
  have hmono := Fspec.mono _ _ hrestr
  rw [Fspec.normalize (k := k) (F := ℂ) ⟨N, hNpos⟩] at hmono
  -- `Fspec (unitTensor ⟨N⟩) = (N : ℝ) = (∏ d'_i : ℝ)`.
  have hmono' : Fspec.toFun X ≤ (N : ℝ) := by exact_mod_cast hmono
  rw [hcard] at hmono'
  exact_mod_cast hmono'

private lemma Fspec_regroupingMap_admissible_exists {k : ℕ} (d : Fin k → ℕ+)
    (Fspec : SpectralPoint k ℂ) :
    ∃ Func : AdmissibleFunctional ℂ (KTensor ℂ d),
      ∀ (n : ℕ+) (T : TensorPower ℂ (n : ℕ) (KTensor ℂ d)),
        Func.toFun n T = Real.toNNReal (Fspec.toFun (regroupingMap d n T)) := by
  /- Construction (paper tex:783): every spectral point `Fspec ∈ Δ(ℂ, k)`
     induces an admissible functional on a fixed format `d` via
     `toFun n T := Real.toNNReal (Fspec.toFun (regroupingMap d n T))`.

     Source lines:
     * `references/main.tex:789-793` (semicontinuity-main): "Any element of
       Δ(F, k) gives an admissible functional on V = F^{d_1} ⊗ ⋯ ⊗ F^{d_k}".
     * `ZariskiSublevel.lean:3742`: regrouping compatibility (paper tex:564).
     * `ZariskiSublevel.lean:4183`: public `regroupingMap_tensorPowerBlock_perm_eq_legPerm`.
     * `ZariskiSublevel.lean:4341`: `tensorRankAdmissible` is the structural template. -/
  classical
  -- At `k = 0`, `Fspec` is inconsistent: `unitTensor 1` and `unitTensor 2`
  -- are mutually restricting (vacuous leg matrices) but `Fspec.normalize`
  -- gives values `1 ≠ 2`, so this branch is vacuous.
  have absurd_at_zero : k = 0 →
      ∃ Func : AdmissibleFunctional ℂ (KTensor ℂ d),
        ∀ (n : ℕ+) (T : TensorPower ℂ (n : ℕ) (KTensor ℂ d)),
          Func.toFun n T = Real.toNNReal (Fspec.toFun (regroupingMap d n T)) := by
    intro hk0
    subst hk0
    have h1 :
        Restricts (unitTensor (F := ℂ) (k := 0) 1)
          (unitTensor (F := ℂ) (k := 0) 2) := by
      refine Restricts.of_eq_cast (fun (i : Fin 0) => i.elim0) ?_
      intro jdx
      simp [unitTensor]
    have h2 :
        Restricts (unitTensor (F := ℂ) (k := 0) 2)
          (unitTensor (F := ℂ) (k := 0) 1) := by
      refine Restricts.of_eq_cast (fun (i : Fin 0) => i.elim0) ?_
      intro jdx
      simp [unitTensor]
    have h12 := Fspec.mono _ _ h1
    have h21 := Fspec.mono _ _ h2
    have h1eq2 :
        Fspec.toFun (unitTensor (F := ℂ) (k := 0) 1) =
          Fspec.toFun (unitTensor (F := ℂ) (k := 0) 2) := le_antisymm h12 h21
    have hn1 := Fspec.normalize (k := 0) (F := ℂ) (1 : ℕ+)
    have hn2 := Fspec.normalize (k := 0) (F := ℂ) (2 : ℕ+)
    rw [hn1, hn2] at h1eq2
    norm_num at h1eq2
  by_cases hk : 1 ≤ k
  swap
  · exact absurd_at_zero (by omega)
  -- Helper: `cast`-preservation of `Fspec.toFun` along a format equality.
  have Fspec_cast :
      ∀ {d₁ d₂ : Fin k → ℕ+} (hfmt : d₁ = d₂) (T : KTensor ℂ d₁),
        Fspec.toFun (hfmt ▸ T) = Fspec.toFun T := by
    intro d₁ d₂ hfmt T
    subst hfmt
    rfl
  -- Helper: `α • X` is restriction-equivalent to `X` for `α ≠ 0` (needs k ≥ 1).
  have smul_Restricts :
      ∀ {d' : Fin k → ℕ+} (α : ℂ) (hα : α ≠ 0) (X : KTensor ℂ d'),
        Restricts (α • X) X := by
    intro d' α _hα X
    refine ⟨fun i => if (i : ℕ) = 0 then
              (α : ℂ) • (1 : Matrix (Fin (d' i)) (Fin (d' i)) ℂ)
            else (1 : Matrix (Fin (d' i)) (Fin (d' i)) ℂ), ?_⟩
    intro jdx
    rw [Finset.sum_eq_single jdx]
    · have hprod :
          (∏ i : Fin k,
            (if (i : ℕ) = 0 then
                (α : ℂ) • (1 : Matrix (Fin (d' i)) (Fin (d' i)) ℂ)
              else (1 : Matrix (Fin (d' i)) (Fin (d' i)) ℂ)) (jdx i) (jdx i)) = α := by
        have hk_pos : 0 < k := hk
        have h0_mem : (⟨0, hk_pos⟩ : Fin k) ∈ (Finset.univ : Finset (Fin k)) :=
          Finset.mem_univ _
        rw [← Finset.mul_prod_erase _ _ h0_mem]
        have hzero_branch :
            (if ((⟨0, hk_pos⟩ : Fin k) : ℕ) = 0 then
                (α : ℂ) • (1 : Matrix (Fin (d' ⟨0, hk_pos⟩)) (Fin (d' ⟨0, hk_pos⟩)) ℂ)
              else (1 : Matrix (Fin (d' ⟨0, hk_pos⟩)) (Fin (d' ⟨0, hk_pos⟩)) ℂ))
              (jdx ⟨0, hk_pos⟩) (jdx ⟨0, hk_pos⟩) = α := by
          simp [Matrix.one_apply_eq]
        rw [hzero_branch]
        have hrest_eq_one :
            (∏ i ∈ (Finset.univ : Finset (Fin k)).erase ⟨0, hk_pos⟩,
              (if (i : ℕ) = 0 then
                  (α : ℂ) • (1 : Matrix (Fin (d' i)) (Fin (d' i)) ℂ)
                else (1 : Matrix (Fin (d' i)) (Fin (d' i)) ℂ)) (jdx i) (jdx i)) = 1 := by
          apply Finset.prod_eq_one
          intro i hi
          have hi_ne : (i : ℕ) ≠ 0 := by
            intro hcontra
            have : i = ⟨0, hk_pos⟩ := Fin.ext hcontra
            exact (Finset.mem_erase.mp hi).1 this
          simp [hi_ne, Matrix.one_apply_eq]
        rw [hrest_eq_one, mul_one]
      rw [hprod]; rfl
    · intro idx _ hidx
      have hne : ∃ i : Fin k, jdx i ≠ idx i := by
        by_contra hall
        push_neg at hall
        exact hidx (funext (fun i => (hall i).symm))
      obtain ⟨i₀, hi₀⟩ := hne
      have hzero_entry :
          (if (i₀ : ℕ) = 0 then
              (α : ℂ) • (1 : Matrix (Fin (d' i₀)) (Fin (d' i₀)) ℂ)
            else (1 : Matrix (Fin (d' i₀)) (Fin (d' i₀)) ℂ)) (jdx i₀) (idx i₀) = 0 := by
        by_cases h0 : (i₀ : ℕ) = 0
        · simp [h0, hi₀]
        · simp [h0, hi₀]
      have hprod_zero :
          (∏ i : Fin k, (if (i : ℕ) = 0 then
                (α : ℂ) • (1 : Matrix (Fin (d' i)) (Fin (d' i)) ℂ)
              else (1 : Matrix (Fin (d' i)) (Fin (d' i)) ℂ)) (jdx i) (idx i)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i₀) hzero_entry
      rw [hprod_zero, zero_mul]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim
  have Restricts_smul :
      ∀ {d' : Fin k → ℕ+} (α : ℂ) (hα : α ≠ 0) (X : KTensor ℂ d'),
        Restricts X (α • X) := by
    intro d' α hα X
    have hα_inv : α⁻¹ ≠ 0 := inv_ne_zero hα
    have h := smul_Restricts (α⁻¹) hα_inv (α • X)
    have hcancel : α⁻¹ • (α • X) = X := by
      rw [smul_smul, inv_mul_cancel₀ hα, one_smul]
    rw [hcancel] at h
    exact h
  have Fspec_smul_inv :
      ∀ {d' : Fin k → ℕ+} (α : ℂ) (hα : α ≠ 0) (X : KTensor ℂ d'),
        Fspec.toFun (α • X) = Fspec.toFun X := by
    intro d' α hα X
    apply le_antisymm
    · exact Fspec.mono _ _ (smul_Restricts α hα X)
    · exact Fspec.mono _ _ (Restricts_smul α hα X)
  -- Helper: `Restricts (0 : KTensor ℂ d') X` for any X (uses k ≥ 1).
  have zero_Restricts :
      ∀ {dS dT : Fin k → ℕ+} (X : KTensor ℂ dT),
        Restricts (0 : KTensor ℂ dS) X := by
    intro dS dT X
    refine ⟨fun i => (0 : Matrix (Fin (dS i)) (Fin (dT i)) ℂ), ?_⟩
    intro jdx
    change (0 : KTensor ℂ dS) jdx
        = ∑ idx : (∀ i : Fin k, Fin (dT i)),
          (∏ i, (0 : Matrix (Fin (dS i)) (Fin (dT i)) ℂ) (jdx i) (idx i)) * X idx
    have hk_pos : 0 < k := hk
    have h0_mem : (⟨0, hk_pos⟩ : Fin k) ∈ (Finset.univ : Finset (Fin k)) :=
      Finset.mem_univ _
    simp only [Pi.zero_apply]
    apply (Finset.sum_eq_zero _).symm
    intro idx _
    have hprod0 :
        (∏ i, (0 : Matrix (Fin (dS i)) (Fin (dT i)) ℂ) (jdx i) (idx i)) = 0 := by
      apply Finset.prod_eq_zero h0_mem
      simp
    rw [hprod0, zero_mul]
  -- Helper: `Fspec.toFun (0 : KTensor ℂ d') = 0` (uses k ≥ 1).
  have Fspec_zero :
      ∀ {d' : Fin k → ℕ+}, Fspec.toFun (0 : KTensor ℂ d') = 0 := by
    intro d'
    have hsum_eq_zero :
        (0 : KTensor ℂ d') ⊕ₜ (0 : KTensor ℂ d') = (0 : KTensor ℂ (fun i => d' i + d' i)) := by
      funext idx
      unfold directSumTensor
      split_ifs <;> rfl
    have hadd := Fspec.add (dS := d') (dT := d') (0 : KTensor ℂ d') (0 : KTensor ℂ d')
    rw [hsum_eq_zero] at hadd
    have hr1 : Restricts (0 : KTensor ℂ (fun i => d' i + d' i)) (0 : KTensor ℂ d') :=
      zero_Restricts _
    have hr2 : Restricts (0 : KTensor ℂ d') (0 : KTensor ℂ (fun i => d' i + d' i)) :=
      zero_Restricts _
    have heq : Fspec.toFun (0 : KTensor ℂ (fun i => d' i + d' i)) =
        Fspec.toFun (0 : KTensor ℂ d') :=
      le_antisymm (Fspec.mono _ _ hr1) (Fspec.mono _ _ hr2)
    rw [heq] at hadd
    linarith
  -- Helper: `Fspec.toFun X ≥ 0` for any X (uses k ≥ 1).
  have Fspec_nonneg :
      ∀ {d' : Fin k → ℕ+} (X : KTensor ℂ d'), 0 ≤ Fspec.toFun X := by
    intro d' X
    have hz : Fspec.toFun (0 : KTensor ℂ d') ≤ Fspec.toFun X :=
      Fspec.mono _ _ (zero_Restricts X)
    rw [Fspec_zero] at hz
    exact hz
  -- Helper: `Restricts (A + B) (A ⊕ₜ B)` for A, B in the same format.
  -- Construction: on each leg i, the matrix `M_i : Matrix (Fin (d' i)) (Fin (d' i + d' i)) ℂ`
  -- has `M_i j idx = 1` iff `idx.val = j.val` (first block) OR `idx.val = d' i + j.val`
  -- (second block), else 0. Summing over all `2^k` choices of "first vs second block per leg"
  -- yields the all-first contribution (= A jdx), the all-second contribution (= B jdx),
  -- and 2^k - 2 mixed off-block-diagonal contributions (= 0 by definition of directSumTensor).
  have sum_Restricts_directSum :
      ∀ {d' : Fin k → ℕ+} (A B : KTensor ℂ d'),
        Restricts (A + B) (A ⊕ₜ B) := by
    intro d' A B
    -- leg-wise matrix: select first block (idx = jdx.castAdd) or second block
    -- (idx = jdx.natAdd shifted).
    let foldMat : ∀ i : Fin k, Matrix (Fin (d' i)) (Fin (d' i + d' i)) ℂ :=
      fun i j idx =>
        if idx.val = j.val ∨ idx.val = (d' i : ℕ) + j.val then 1 else 0
    refine ⟨foldMat, ?_⟩
    intro jdx
    -- The non-zero `idx` are exactly those where for each leg i,
    -- `idx i ∈ {Fin.castLE jdx i, Fin.natAdd jdx i}`, i.e., a "choice" function
    -- `c : Fin k → Fin 2`.
    -- Define the bijection `Fin k → Fin 2 ↔ {nonzero idx in the sum}`.
    set sumLHS :
        ∀ i : Fin k, (Fin (d' i + d' i)) := fun _ => 0 with _hsum_def
    -- Direct calculation: split sum over `idx` by partitioning on choice tuples.
    -- We use `Fintype.sum_equiv` to re-index.
    let chooseIdx : (Fin k → Fin 2) → (∀ i, Fin (d' i + d' i)) :=
      fun c i =>
        if c i = 0 then
          ⟨(jdx i).val, by
            have hjlt : (jdx i).val < (d' i : ℕ) := (jdx i).isLt
            omega⟩
        else
          ⟨(d' i : ℕ) + (jdx i).val, by
            have hjlt : (jdx i).val < (d' i : ℕ) := (jdx i).isLt
            omega⟩
    -- The contributing terms are exactly the image of `chooseIdx`.
    -- For `idx = chooseIdx c`, the product `∏ i, foldMat i (jdx i) (idx i) = 1`.
    -- For `idx` outside the image, the product is 0.
    have hcontrib_eq_one : ∀ c : Fin k → Fin 2,
        (∏ i, foldMat i (jdx i) (chooseIdx c i)) = 1 := by
      intro c
      apply Finset.prod_eq_one
      intro i _
      simp only [foldMat, chooseIdx]
      by_cases hc : c i = 0
      · simp [hc]
      · simp [hc]
    have hother_zero : ∀ idx : (∀ i, Fin (d' i + d' i)),
        (∀ c : Fin k → Fin 2, idx ≠ chooseIdx c) →
          (∏ i, foldMat i (jdx i) (idx i)) = 0 := by
      intro idx hne
      -- There exists a leg `i₀` where `(idx i₀).val ∉ {jdx i₀.val, d' i₀ + jdx i₀.val}`.
      by_contra hprod_ne
      -- Otherwise, every leg satisfies the membership condition; define c accordingly.
      have hper_leg : ∀ i : Fin k,
          (idx i).val = (jdx i).val ∨ (idx i).val = (d' i : ℕ) + (jdx i).val := by
        intro i
        by_contra h
        push_neg at h
        apply hprod_ne
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [foldMat, h.1, h.2]
      -- Construct the choice function.
      let c : Fin k → Fin 2 := fun i =>
        if (idx i).val = (jdx i).val then 0 else 1
      have hidx_eq : idx = chooseIdx c := by
        funext i
        rcases hper_leg i with h1 | h2
        · -- idx i.val = jdx i.val, so c i = 0.
          have hci : c i = 0 := by simp [c, h1]
          apply Fin.ext
          show (idx i).val = (chooseIdx c i).val
          simp [chooseIdx, hci, h1]
        · -- idx i.val = d' i + jdx i.val, so c i = 1 (need jdx i.val ≠ d' i + jdx i.val).
          have hjlt : (jdx i).val < (d' i : ℕ) := (jdx i).isLt
          have hne_first : (idx i).val ≠ (jdx i).val := by
            rw [h2]; omega
          have hci : c i = 1 := by simp [c, hne_first]
          apply Fin.ext
          show (idx i).val = (chooseIdx c i).val
          simp [chooseIdx, hci, h2]
      exact hne c hidx_eq
    -- The directSumTensor value at chooseIdx c:
    --   - If c is constantly 0: (A ⊕ₜ B) at "all-first-block" = A jdx.
    --   - If c is constantly 1: (A ⊕ₜ B) at "all-second-block" = B jdx.
    --   - Otherwise: off block-diagonal, = 0.
    have hds_value : ∀ c : Fin k → Fin 2,
        (A ⊕ₜ B) (chooseIdx c) =
          (if ∀ i, c i = 0 then A jdx else 0) +
          (if ∀ i, c i = 1 then B jdx else 0) := by
      intro c
      -- Compute (A ⊕ₜ B) on chooseIdx c.
      unfold directSumTensor
      by_cases hall0 : ∀ i, c i = 0
      · -- All first-block. The first dif is true.
        have hSall : ∀ i, (chooseIdx c i).val < (d' i : ℕ) := by
          intro i
          have hci : c i = 0 := hall0 i
          have hjlt : (jdx i).val < (d' i : ℕ) := (jdx i).isLt
          simp [chooseIdx, hci, hjlt]
        have h_eq : (fun i => (⟨(chooseIdx c i).val, hSall i⟩ : Fin (d' i))) = jdx := by
          funext i
          have hci : c i = 0 := hall0 i
          apply Fin.ext
          simp [chooseIdx, hci]
        simp only [dif_pos hSall, h_eq]
        have hnot_all1 : ¬ ∀ i, c i = 1 := by
          intro hall1
          have hk_pos : 0 < k := hk
          let i₀ : Fin k := ⟨0, hk_pos⟩
          have h0 : c i₀ = 0 := hall0 i₀
          have h1 : c i₀ = 1 := hall1 i₀
          rw [h0] at h1
          exact absurd h1 (by decide)
        rw [if_pos hall0, if_neg hnot_all1, add_zero]
      · -- Not all first-block.
        by_cases hall1 : ∀ i, c i = 1
        · -- All second-block. The first dif is false (some leg has c i = 1, so val ≥ d').
          have hnot_first : ¬ ∀ i, (chooseIdx c i).val < (d' i : ℕ) := by
            push_neg
            have hk_pos : 0 < k := hk
            let i₀ : Fin k := ⟨0, hk_pos⟩
            refine ⟨i₀, ?_⟩
            have hci₀ : c i₀ = 1 := hall1 i₀
            simp [chooseIdx, hci₀]
          have hTall : ∀ i, (d' i : ℕ) ≤ (chooseIdx c i).val := by
            intro i
            have hci : c i = 1 := hall1 i
            simp [chooseIdx, hci]
          simp only [dif_neg hnot_first, dif_pos hTall]
          have h_eq : (fun i =>
                (⟨(chooseIdx c i).val - (d' i : ℕ), by
                  have h1 : (chooseIdx c i).val < ((d' i + d' i : ℕ+) : ℕ) :=
                    (chooseIdx c i).isLt
                  have h2 : ((d' i + d' i : ℕ+) : ℕ) = (d' i : ℕ) + (d' i : ℕ) :=
                    PNat.add_coe _ _
                  have h3 : (d' i : ℕ) ≤ (chooseIdx c i).val := hTall i
                  omega⟩ : Fin (d' i))) = jdx := by
            funext i
            have hci : c i = 1 := hall1 i
            apply Fin.ext
            simp [chooseIdx, hci]
          rw [h_eq]
          rw [if_neg hall0, if_pos hall1, zero_add]
        · -- Mixed: some leg is first, some leg is second.
          push_neg at hall0
          push_neg at hall1
          obtain ⟨i_first, h_first⟩ := hall1
          obtain ⟨i_second, h_second⟩ := hall0
          have hci_first_zero : c i_first = 0 := by
            have h2 : (c i_first).val < 2 := (c i_first).isLt
            have h1 : (c i_first).val ≠ 1 := fun h => h_first (Fin.ext h)
            apply Fin.ext
            change (c i_first).val = 0
            omega
          have hci_second_one : c i_second = 1 := by
            have h2 : (c i_second).val < 2 := (c i_second).isLt
            have h0 : (c i_second).val ≠ 0 := fun h => h_second (Fin.ext h)
            apply Fin.ext
            change (c i_second).val = 1
            omega
          -- First dif fails at i_second (val = d' + jdx ≥ d').
          have hnot_first : ¬ ∀ i, (chooseIdx c i).val < (d' i : ℕ) := by
            push_neg
            refine ⟨i_second, ?_⟩
            simp [chooseIdx, hci_second_one]
          -- Second dif fails at i_first (val = jdx < d').
          have hnot_second : ¬ ∀ i, (d' i : ℕ) ≤ (chooseIdx c i).val := by
            push_neg
            refine ⟨i_first, ?_⟩
            have hjlt : (jdx i_first).val < (d' i_first : ℕ) := (jdx i_first).isLt
            simp [chooseIdx, hci_first_zero, hjlt]
          simp only [dif_neg hnot_first, dif_neg hnot_second]
          have hnot_all0 : ¬ ∀ i, c i = 0 := by
            intro h
            apply h_second
            exact h i_second
          have hnot_all1 : ¬ ∀ i, c i = 1 := by
            intro h
            apply h_first
            exact h i_first
          simp [hnot_all0, hnot_all1]
    -- Now compute the sum.
    -- The sum splits over `chooseIdx c` for c : Fin k → Fin 2, plus a 0 from
    -- the other (vanishing) indices.
    have hchooseIdx_inj : Function.Injective chooseIdx := by
      intro c c' hcc
      funext i
      have hd : ((d' i + d' i : ℕ+) : ℕ) = (d' i : ℕ) + (d' i : ℕ) :=
        PNat.add_coe _ _
      have hjlt : (jdx i).val < (d' i : ℕ) := (jdx i).isLt
      have h_eq : (chooseIdx c i).val = (chooseIdx c' i).val := by
        rw [hcc]
      by_cases hci : c i = 0
      · by_cases hci' : c' i = 0
        · rw [hci, hci']
        · exfalso
          have h1 : (chooseIdx c i).val = (jdx i).val := by simp [chooseIdx, hci]
          have h2 : (chooseIdx c' i).val = (d' i : ℕ) + (jdx i).val := by
            simp [chooseIdx, hci']
          rw [h1, h2] at h_eq
          omega
      · by_cases hci' : c' i = 0
        · exfalso
          have h1 : (chooseIdx c i).val = (d' i : ℕ) + (jdx i).val := by
            simp [chooseIdx, hci]
          have h2 : (chooseIdx c' i).val = (jdx i).val := by simp [chooseIdx, hci']
          rw [h1, h2] at h_eq
          omega
        · -- Both are 1.
          have hci_one : c i = 1 := by
            have h2 : (c i).val < 2 := (c i).isLt
            have h0 : (c i).val ≠ 0 := fun h => hci (Fin.ext h)
            apply Fin.ext
            change (c i).val = 1
            omega
          have hci'_one : c' i = 1 := by
            have h2 : (c' i).val < 2 := (c' i).isLt
            have h0 : (c' i).val ≠ 0 := fun h => hci' (Fin.ext h)
            apply Fin.ext
            change (c' i).val = 1
            omega
          rw [hci_one, hci'_one]
    -- Now do the calculation.
    change (A + B) jdx
        = ∑ idx : (∀ i, Fin (d' i + d' i)),
          (∏ i, foldMat i (jdx i) (idx i)) * (A ⊕ₜ B) idx
    -- Split the sum into `image of chooseIdx` and its complement.
    have huniv_eq :
        (Finset.univ : Finset (∀ i, Fin (d' i + d' i)))
          = (Finset.image chooseIdx Finset.univ) ∪
              ((Finset.univ : Finset (∀ i, Fin (d' i + d' i)))
                \ Finset.image chooseIdx Finset.univ) := by
      ext x
      constructor
      · intro _
        rw [Finset.mem_union]
        by_cases hex : x ∈ Finset.image chooseIdx Finset.univ
        · left; exact hex
        · right; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hex⟩
      · intro _
        exact Finset.mem_univ _
    rw [huniv_eq]
    rw [Finset.sum_union (Finset.disjoint_sdiff)]
    have hcompl_zero :
        ∑ idx ∈ (Finset.univ : Finset (∀ i, Fin (d' i + d' i)))
              \ Finset.image chooseIdx Finset.univ,
          (∏ i, foldMat i (jdx i) (idx i)) * (A ⊕ₜ B) idx = 0 := by
      apply Finset.sum_eq_zero
      intro idx hmem
      rw [Finset.mem_sdiff] at hmem
      have hno : ∀ c, idx ≠ chooseIdx c := by
        intro c hidx
        apply hmem.2
        exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, hidx.symm⟩
      rw [hother_zero idx hno, zero_mul]
    -- For the union part — reindex via chooseIdx.
    have himg_eq :
        ∑ idx ∈ Finset.image chooseIdx Finset.univ,
            (∏ i, foldMat i (jdx i) (idx i)) * (A ⊕ₜ B) idx
          = ∑ c : Fin k → Fin 2,
            (∏ i, foldMat i (jdx i) (chooseIdx c i)) * (A ⊕ₜ B) (chooseIdx c) :=
      Finset.sum_image (fun a _ b _ => hchooseIdx_inj.eq_iff.mp)
    rw [himg_eq, hcompl_zero, add_zero]
    -- Now each term = 1 * (A ⊕ₜ B) (chooseIdx c) = (A ⊕ₜ B) (chooseIdx c)
    --              = (if all 0 then A jdx) + (if all 1 then B jdx).
    have hsum_eq :
        ∑ c : Fin k → Fin 2,
          (∏ i, foldMat i (jdx i) (chooseIdx c i)) * (A ⊕ₜ B) (chooseIdx c)
          = ∑ c : Fin k → Fin 2,
            ((if ∀ i, c i = 0 then A jdx else 0) +
             (if ∀ i, c i = 1 then B jdx else 0)) := by
      refine Finset.sum_congr rfl ?_
      intro c _
      rw [hcontrib_eq_one c, one_mul, hds_value c]
    rw [hsum_eq]
    -- Split sum.
    rw [Finset.sum_add_distrib]
    -- Each "if ∀ i, c i = 0" picks out exactly the constant-0 function.
    have hconst0_sum :
        ∑ c : Fin k → Fin 2,
          (if ∀ i, c i = 0 then A jdx else 0) = A jdx := by
      let c0 : Fin k → Fin 2 := fun _ => 0
      rw [Finset.sum_eq_single c0]
      · simp [c0]
      · intro c _ hne
        have : ¬ ∀ i, c i = 0 := by
          intro h
          apply hne
          funext i
          exact h i
        simp [this]
      · intro h
        exact absurd (Finset.mem_univ c0) h
    have hconst1_sum :
        ∑ c : Fin k → Fin 2,
          (if ∀ i, c i = 1 then B jdx else 0) = B jdx := by
      let c1 : Fin k → Fin 2 := fun _ => 1
      rw [Finset.sum_eq_single c1]
      · simp [c1]
      · intro c _ hne
        have : ¬ ∀ i, c i = 1 := by
          intro h
          apply hne
          funext i
          exact h i
        simp [this]
      · intro h
        exact absurd (Finset.mem_univ c1) h
    rw [hconst0_sum, hconst1_sum]
    rfl
  -- Construct `Func`.
  refine ⟨{
    toFun := fun n T => Real.toNNReal (Fspec.toFun (regroupingMap d n T))
    subadd := ?_
    submul := ?_
    perm_inv := ?_
    scalar_inv := ?_
    bdd_one := ?_
  }, ?_⟩
  · -- subadd: regroupingMap is linear; bridge `+` to `⊕ₜ` for Fspec.
    intro n T S
    have hmap : regroupingMap d n (T + S) =
        regroupingMap d n T + regroupingMap d n S := by
      exact LinearMap.map_add _ T S
    change Real.toNNReal (Fspec.toFun (regroupingMap d n (T + S)))
        ≤ Real.toNNReal (Fspec.toFun (regroupingMap d n T)) +
            Real.toNNReal (Fspec.toFun (regroupingMap d n S))
    rw [hmap]
    set A := regroupingMap d n T
    set B := regroupingMap d n S
    -- Fspec.add gives Fspec(A ⊕ₜ B) = Fspec A + Fspec B.
    have hadd := Fspec.add A B
    -- Restricts (A + B) (A ⊕ₜ B) bridges + to ⊕ₜ.
    have hbridge : Restricts (A + B) (A ⊕ₜ B) := sum_Restricts_directSum A B
    have hle : Fspec.toFun (A + B) ≤ Fspec.toFun (A ⊕ₜ B) :=
      Fspec.mono _ _ hbridge
    rw [hadd] at hle
    -- Now Fspec (A + B) ≤ Fspec A + Fspec B; turn into Real.toNNReal inequality.
    have hAnn : 0 ≤ Fspec.toFun A := Fspec_nonneg A
    have hBnn : 0 ≤ Fspec.toFun B := Fspec_nonneg B
    calc Real.toNNReal (Fspec.toFun (A + B))
        ≤ Real.toNNReal (Fspec.toFun A + Fspec.toFun B) :=
          Real.toNNReal_mono hle
      _ = Real.toNNReal (Fspec.toFun A) + Real.toNNReal (Fspec.toFun B) :=
          Real.toNNReal_add hAnn hBnn
  · -- submul: regroupingMap commutes with ⊗-product modulo format cast,
    -- then `Fspec.mult` closes the multiplicativity inequality.
    intro n n' T S
    set hfmt : formatPow d ⟨(n : ℕ) + (n' : ℕ), Nat.add_pos_left n.pos _⟩
        = fun i => formatPow d n i * formatPow d n' i :=
      formatPow_add_eq_mul d n n'
    have hbridge :
        (hfmt ▸ regroupingMap d ⟨(n : ℕ) + (n' : ℕ), Nat.add_pos_left n.pos _⟩
            ((tensorPowerAdd ℂ (KTensor ℂ d) (n : ℕ) (n' : ℕ)).symm (T ⊗ₜ[ℂ] S)))
          = (regroupingMap d n T) ⊠ (regroupingMap d n' S) :=
      regroupingMap_tensorPowerAdd_symm_eq_kron_cast (F := ℂ) d n n' T S
    have hLHS_eq :
        Fspec.toFun
          (regroupingMap d ⟨(n : ℕ) + (n' : ℕ), Nat.add_pos_left n.pos _⟩
            ((tensorPowerAdd ℂ (KTensor ℂ d) (n : ℕ) (n' : ℕ)).symm (T ⊗ₜ[ℂ] S)))
          =
        Fspec.toFun ((regroupingMap d n T) ⊠ (regroupingMap d n' S)) := by
      rw [← hbridge, Fspec_cast hfmt]
    have hmul := Fspec.mult (regroupingMap d n T) (regroupingMap d n' S)
    change Real.toNNReal
        (Fspec.toFun
          (regroupingMap d ⟨(n : ℕ) + (n' : ℕ), Nat.add_pos_left n.pos _⟩
            ((tensorPowerAdd ℂ (KTensor ℂ d) (n : ℕ) (n' : ℕ)).symm (T ⊗ₜ[ℂ] S))))
        ≤ Real.toNNReal (Fspec.toFun (regroupingMap d n T)) *
            Real.toNNReal (Fspec.toFun (regroupingMap d n' S))
    rw [hLHS_eq, hmul]
    rw [Real.toNNReal_mul (Fspec_nonneg _)]
  · -- perm_inv: use the public `regroupingMap_tensorPowerBlock_perm_eq_legPerm`
    -- to identify the two regrouped block tensors (modulo format cast) up to
    -- a leg-wise permutation, then Fspec.mono in both directions via
    -- legPerm_Restricts / Restricts_legPerm.
    intro ℓ nVec σ Ts hpos₁ hpos₂
    change Real.toNNReal
        (Fspec.toFun
          (regroupingMap d ⟨_, hpos₁⟩
            (tensorPowerBlock ℂ (KTensor ℂ d) (fun i => (nVec i : ℕ)) Ts)))
        = Real.toNNReal
          (Fspec.toFun
            (regroupingMap d ⟨_, hpos₂⟩
              (tensorPowerBlock ℂ (KTensor ℂ d) (fun i => ((nVec (σ i)) : ℕ))
                (fun i => Ts (σ i)))))
    -- The format-cast LHS coincides with `RHS.legPerm φ_σ` for some `φ_σ`.
    set hfmt := formatPow_block_perm_eq d nVec σ hpos₁ hpos₂
    set LHS := regroupingMap d ⟨_, hpos₁⟩
          (tensorPowerBlock ℂ (KTensor ℂ d) (fun i => (nVec i : ℕ)) Ts)
    set RHS := regroupingMap d ⟨_, hpos₂⟩
          (tensorPowerBlock ℂ (KTensor ℂ d) (fun i => ((nVec (σ i)) : ℕ))
            (fun i => Ts (σ i)))
    -- Step 1: Fspec(LHS) = Fspec(hfmt ▸ LHS) by the format cast helper.
    have hLHS_cast : Fspec.toFun LHS = Fspec.toFun (hfmt ▸ LHS) :=
      (Fspec_cast hfmt LHS).symm
    -- Step 2: hfmt ▸ LHS = RHS.legPerm φ_σ for some φ_σ.
    obtain ⟨φ_σ, hLHS_eq⟩ := regroupingMap_tensorPowerBlock_perm_eq_legPerm
      (F := ℂ) d nVec σ Ts hpos₁ hpos₂
    -- Step 3: Fspec(RHS.legPerm φ_σ) = Fspec(RHS) by bidirectional Restricts.
    have hperm_le : Fspec.toFun (RHS.legPerm φ_σ) ≤ Fspec.toFun RHS :=
      Fspec.mono _ _ (KTensor.legPerm_Restricts RHS φ_σ)
    have hperm_ge : Fspec.toFun RHS ≤ Fspec.toFun (RHS.legPerm φ_σ) :=
      Fspec.mono _ _ (KTensor.Restricts_legPerm RHS φ_σ)
    have hperm_eq : Fspec.toFun (RHS.legPerm φ_σ) = Fspec.toFun RHS :=
      le_antisymm hperm_le hperm_ge
    rw [hLHS_cast, hLHS_eq, hperm_eq]
  · -- scalar_inv: Fspec is restriction-invariant under nonzero scaling.
    intro n α hα T
    show Real.toNNReal (Fspec.toFun (regroupingMap d n (α • T)))
        = Real.toNNReal (Fspec.toFun (regroupingMap d n T))
    rw [LinearMap.map_smul]
    rw [Fspec_smul_inv α hα]
  · -- bdd_one: bound Fspec by Fspec(unitTensor(∏ d_i)) via standard restriction.
    -- Paper tex:783 + Fspec.normalize: every `X : KTensor ℂ d'` restricts to
    -- `unitTensor (∏ d_i')` because X is a linear combination of (∏ d_i')
    -- standard-basis simple tensors. Combining with the simple-tensor restriction
    -- `simpleTensor ≤ unitTensor 1` and the unit-tensor scaling lemma gives the
    -- bound; concretely `Fspec X ≤ Fspec(unitTensor (tensorRank X)) =
    -- tensorRank X ≤ ∏ d_i'` (the trivial F_1-bound, paper tex:534-536).
    -- The bound constant is `∏ (formatPow d 1 i)` = `∏ d_i`.
    refine ⟨((∏ i, ((formatPow d (1 : ℕ+) i : ℕ))) : NNReal), ?_⟩
    intro T
    show Real.toNNReal (Fspec.toFun (regroupingMap d 1 T))
        ≤ ((∏ i, ((formatPow d (1 : ℕ+) i : ℕ))) : NNReal)
    -- The trivial F_1 boundedness fact (paper tex:534-536): for any
    -- `X : KTensor ℂ d'`, `Fspec X ≤ ∏ d'_i` via `X ≤ₜ unitTensor ⟨∏ d'_i⟩`
    -- (standard-basis decomposition) + `Fspec.mono` + `Fspec.normalize`,
    -- packaged as `Fspec_le_prod_dims`.  Here `d' = formatPow d 1`.
    have hbound := Fspec_le_prod_dims hk Fspec (regroupingMap d 1 T)
    refine (Real.toNNReal_le_toNNReal hbound).trans ?_
    rw [Real.toNNReal_coe_nat]
    push_cast
    rfl
  · -- The defining equality holds definitionally.
    intro n T; rfl

private lemma Fspec_regroupingMap_regularization_eq {k : ℕ} (d : Fin k → ℕ+)
    (Fspec : SpectralPoint k ℂ) (Func : AdmissibleFunctional ℂ (KTensor ℂ d))
    (hFunc : ∀ (n : ℕ+) (T : TensorPower ℂ (n : ℕ) (KTensor ℂ d)),
      Func.toFun n T = Real.toNNReal (Fspec.toFun (regroupingMap d n T))) :
    ∀ T : KTensor ℂ d, Fspec.toFun T = Func.regularize T := by
  /- Narrow helper for paper tex:783 regularization equality.

     With the explicit `hFunc`, the defining infimum for `Func.regularize T`
     is over the values of `Fspec` on regrouped tensor powers.  Paper tex:564
     identifies these regrouped powers with `⊠`-powers, and `Fspec.mult`
     makes every level contribute `(Fspec.toFun T)^n`; taking the `1/n` power
     gives back `Fspec.toFun T`. -/
  classical
  -- The `k = 0` branch is vacuous: spectral points on the zero-leg format
  -- collide on `unitTensor 1` vs `unitTensor 2`, contradicting `Fspec.normalize`.
  by_cases hk : 1 ≤ k
  swap
  · intro T
    have hk0 : k = 0 := by omega
    subst hk0
    have h1 :
        Restricts (unitTensor (F := ℂ) (k := 0) 1)
          (unitTensor (F := ℂ) (k := 0) 2) := by
      refine Restricts.of_eq_cast (fun (i : Fin 0) => i.elim0) ?_
      intro jdx; simp [unitTensor]
    have h2 :
        Restricts (unitTensor (F := ℂ) (k := 0) 2)
          (unitTensor (F := ℂ) (k := 0) 1) := by
      refine Restricts.of_eq_cast (fun (i : Fin 0) => i.elim0) ?_
      intro jdx; simp [unitTensor]
    have h12 := Fspec.mono _ _ h1
    have h21 := Fspec.mono _ _ h2
    have h1eq2 :
        Fspec.toFun (unitTensor (F := ℂ) (k := 0) 1) =
          Fspec.toFun (unitTensor (F := ℂ) (k := 0) 2) := le_antisymm h12 h21
    have hn1 := Fspec.normalize (k := 0) (F := ℂ) (1 : ℕ+)
    have hn2 := Fspec.normalize (k := 0) (F := ℂ) (2 : ℕ+)
    rw [hn1, hn2] at h1eq2
    norm_num at h1eq2
  -- Auxiliary helpers (specializations of the helpers in
  -- `Fspec_regroupingMap_admissible_exists`).
  have Fspec_cast :
      ∀ {d₁ d₂ : Fin k → ℕ+} (hfmt : d₁ = d₂) (T : KTensor ℂ d₁),
        Fspec.toFun (hfmt ▸ T) = Fspec.toFun T := by
    intro d₁ d₂ hfmt T; subst hfmt; rfl
  have zero_Restricts :
      ∀ {dS dT : Fin k → ℕ+} (X : KTensor ℂ dT),
        Restricts (0 : KTensor ℂ dS) X := by
    intro dS dT X
    refine ⟨fun i => (0 : Matrix (Fin (dS i)) (Fin (dT i)) ℂ), ?_⟩
    intro jdx
    change (0 : KTensor ℂ dS) jdx
        = ∑ idx : (∀ i : Fin k, Fin (dT i)),
          (∏ i, (0 : Matrix (Fin (dS i)) (Fin (dT i)) ℂ) (jdx i) (idx i)) * X idx
    have hk_pos : 0 < k := hk
    have h0_mem : (⟨0, hk_pos⟩ : Fin k) ∈ (Finset.univ : Finset (Fin k)) :=
      Finset.mem_univ _
    simp only [Pi.zero_apply]
    apply (Finset.sum_eq_zero _).symm
    intro idx _
    have hprod0 :
        (∏ i, (0 : Matrix (Fin (dS i)) (Fin (dT i)) ℂ) (jdx i) (idx i)) = 0 := by
      apply Finset.prod_eq_zero h0_mem; simp
    rw [hprod0, zero_mul]
  -- `Fspec.toFun (0 : KTensor ℂ d') = 0` (uses k ≥ 1).
  have Fspec_zero :
      ∀ {d' : Fin k → ℕ+}, Fspec.toFun (0 : KTensor ℂ d') = 0 := by
    intro d'
    have hsum_eq_zero :
        (0 : KTensor ℂ d') ⊕ₜ (0 : KTensor ℂ d')
          = (0 : KTensor ℂ (fun i => d' i + d' i)) := by
      funext idx
      unfold directSumTensor
      split_ifs <;> rfl
    have hadd := Fspec.add (dS := d') (dT := d') (0 : KTensor ℂ d') (0 : KTensor ℂ d')
    rw [hsum_eq_zero] at hadd
    have hr1 : Restricts (0 : KTensor ℂ (fun i => d' i + d' i)) (0 : KTensor ℂ d') :=
      zero_Restricts _
    have hr2 : Restricts (0 : KTensor ℂ d') (0 : KTensor ℂ (fun i => d' i + d' i)) :=
      zero_Restricts _
    have heq : Fspec.toFun (0 : KTensor ℂ (fun i => d' i + d' i)) =
        Fspec.toFun (0 : KTensor ℂ d') :=
      le_antisymm (Fspec.mono _ _ hr1) (Fspec.mono _ _ hr2)
    rw [heq] at hadd
    linarith
  have Fspec_nonneg :
      ∀ {d' : Fin k → ℕ+} (X : KTensor ℂ d'), 0 ≤ Fspec.toFun X := by
    intro d' X
    have hz : Fspec.toFun (0 : KTensor ℂ d') ≤ Fspec.toFun X :=
      Fspec.mono _ _ (zero_Restricts X)
    rw [Fspec_zero] at hz; exact hz
  -- Local versions of two private helpers in ZariskiSublevel
  -- (`KTensor_cast_apply`, `val_eq_rec_pi_fin`).
  have KTensor_cast_apply :
      ∀ {d₁ d₂ : Fin k → ℕ+} (h : d₁ = d₂)
        (X : KTensor ℂ d₁) (idx : ∀ i, Fin (d₂ i)),
        (h ▸ X) idx = X (h.symm ▸ idx) := by
    intro d₁ d₂ h X idx; subst h; rfl
  have val_eq_rec_pi_fin :
      ∀ {f g : Fin k → ℕ+} (h : f = g)
        (x : ∀ i : Fin k, Fin ↑(f i)) (i : Fin k),
        ((h ▸ x : ∀ i, Fin ↑(g i)) i).val = (x i).val := by
    intro f g h x i; subst h; rfl
  intro T
  -- Step 1: Inductive identity (paper tex:783, multiplicativity under ⊠).
  --   Fspec(regroupingMap d n (tensorPow n T)) = (Fspec T)^n.
  have hpow : ∀ n : ℕ+,
      Fspec.toFun (regroupingMap d n
        (tensorPow (F := ℂ) (V := KTensor ℂ d) n T)) = (Fspec.toFun T) ^ (n : ℕ) := by
    intro n
    induction n using PNat.recOn with
    | one =>
      -- `regroupingMap d 1 (tensorPow 1 T) = hfmt.symm ▸ T`, then Fspec_cast.
      have hfmt : formatPow d 1 = d := by funext i; simp [formatPow]
      have hreg_eq :
          regroupingMap d (1 : ℕ+)
              (tensorPow (F := ℂ) (V := KTensor ℂ d) (1 : ℕ+) T) =
            hfmt.symm ▸ T := by
        funext jdx
        change regroupingMap d (1 : ℕ+)
            (PiTensorProduct.tprod ℂ (fun _ : Fin ((1 : ℕ+) : ℕ) => T)) jdx
          = (hfmt.symm ▸ T) jdx
        rw [regroupingMap_tprod_apply]
        change (∏ jj : Fin 1, T (sliceFun d 1 jdx jj)) = _
        rw [Fin.prod_univ_one]
        rw [KTensor_cast_apply]
        congr 1
        funext i
        apply Fin.ext
        rw [val_eq_rec_pi_fin]
        rw [sliceFun, powIndexEquiv_one]
      rw [hreg_eq, Fspec_cast]
      simp
    | succ n ih =>
      -- Step case via `regroupingMap_tensorPowerAdd_symm_eq_kron_cast`
      -- + `tensorPowerAdd_symm_tensorPow` + `Fspec.mult`.
      have htP :=
        tensorPowerAdd_symm_tensorPow (F := ℂ) (V := KTensor ℂ d) T n
      have hreg_kron :=
        regroupingMap_tensorPowerAdd_symm_eq_kron_cast (F := ℂ) d n 1
          (tensorPow (F := ℂ) (V := KTensor ℂ d) n T)
          (tensorPow (F := ℂ) (V := KTensor ℂ d) 1 T)
      -- After rewriting, hreg_kron states the ⊠-decomposition of the
      -- regroupingMap at the PNat ⟨n+1, _⟩ (numerically n+1).
      rw [htP] at hreg_kron
      -- hreg_kron :
      --   (formatPow_add_eq_mul d n 1) ▸ regroupingMap d ⟨n+1,_⟩ (tensorPow (n+1) T)
      --   = (regroupingMap d n (tensorPow n T)) ⊠ (regroupingMap d 1 (tensorPow 1 T))
      -- Apply Fspec.toFun, use Fspec_cast on the LHS and Fspec.mult on the RHS.
      set X := regroupingMap d n (tensorPow (F := ℂ) (V := KTensor ℂ d) n T)
      set Y :=
        regroupingMap d (1 : ℕ+) (tensorPow (F := ℂ) (V := KTensor ℂ d) 1 T)
      have hcast :
          Fspec.toFun ((formatPow_add_eq_mul d n 1) ▸
            regroupingMap d ⟨(n : ℕ) + ((1 : ℕ+) : ℕ),
                Nat.add_pos_left n.pos _⟩
              (tensorPow (F := ℂ) (V := KTensor ℂ d) (n + 1) T)) =
          Fspec.toFun
            (regroupingMap d ⟨(n : ℕ) + ((1 : ℕ+) : ℕ),
                Nat.add_pos_left n.pos _⟩
              (tensorPow (F := ℂ) (V := KTensor ℂ d) (n + 1) T)) :=
        Fspec_cast (formatPow_add_eq_mul d n 1) _
      have hPNat :
          (⟨(n : ℕ) + ((1 : ℕ+) : ℕ),
              Nat.add_pos_left n.pos _⟩ : ℕ+) = (n + 1 : ℕ+) := by
        apply PNat.coe_injective
        change (n : ℕ) + ((1 : ℕ+) : ℕ) = ((n + 1 : ℕ+) : ℕ)
        rw [PNat.add_coe]
      -- Apply Fspec.toFun to both sides of hreg_kron, use Fspec_cast on the left.
      have hkey :
          Fspec.toFun
              (regroupingMap d ⟨(n : ℕ) + ((1 : ℕ+) : ℕ),
                  Nat.add_pos_left n.pos _⟩
                (tensorPow (F := ℂ) (V := KTensor ℂ d) (n + 1) T)) =
            Fspec.toFun (X ⊠ Y) := by
        rw [← hcast, hreg_kron]
      -- Use the PNat equality to bridge ⟨n+1,_⟩ vs (n+1).
      have hkey' :
          Fspec.toFun
              (regroupingMap d (n + 1 : ℕ+)
                (tensorPow (F := ℂ) (V := KTensor ℂ d) (n + 1) T)) =
            Fspec.toFun (X ⊠ Y) := by
        cases hPNat; exact hkey
      rw [hkey']
      -- `Fspec.mult` + IH + Y = "tensorPow 1 case".
      rw [Fspec.mult X Y, ih]
      -- Compute Fspec.toFun Y = Fspec.toFun T (the n=1 case, inline).
      have hfmt1 : formatPow d 1 = d := by funext i; simp [formatPow]
      have hY_eq : Y = hfmt1.symm ▸ T := by
        funext jdx
        change regroupingMap d (1 : ℕ+)
            (PiTensorProduct.tprod ℂ (fun _ : Fin ((1 : ℕ+) : ℕ) => T)) jdx
          = (hfmt1.symm ▸ T) jdx
        rw [regroupingMap_tprod_apply]
        change (∏ jj : Fin 1, T (sliceFun d 1 jdx jj)) = _
        rw [Fin.prod_univ_one]
        rw [KTensor_cast_apply]
        congr 1
        funext i
        apply Fin.ext
        rw [val_eq_rec_pi_fin]
        rw [sliceFun, powIndexEquiv_one]
      rw [hY_eq, Fspec_cast]
      -- Goal: (Fspec.toFun T)^n * Fspec.toFun T = (Fspec.toFun T)^((n+1 : ℕ+) : ℕ).
      rw [PNat.add_coe, show ((1 : ℕ+) : ℕ) = 1 from rfl, pow_succ]
  -- Step 2: substitute into the regularization infimum.
  unfold AdmissibleFunctional.regularize
  -- The infimum term at level n is `((Func.toFun n (tensorPow n T)) : ℝ)^(1/n)`.
  -- With hFunc and hpow, this is `((Fspec.toFun T)^n)^(1/n) = Fspec.toFun T`.
  have hFspecT_nn : 0 ≤ Fspec.toFun T := Fspec_nonneg T
  have hterm : ∀ n : ℕ+,
      ((Func.toFun n
          (tensorPow (F := ℂ) (V := KTensor ℂ d) n T)) : ℝ) ^
        ((1 : ℝ) / ((n : ℕ+) : ℕ)) = Fspec.toFun T := by
    intro n
    rw [hFunc n
      (tensorPow (F := ℂ) (V := KTensor ℂ d) n T)]
    rw [hpow n]
    -- Now: ((Real.toNNReal ((Fspec.toFun T)^n)) : ℝ)^(1/n) = Fspec.toFun T.
    have hpow_nn : 0 ≤ (Fspec.toFun T) ^ (n : ℕ) := pow_nonneg hFspecT_nn _
    rw [Real.coe_toNNReal _ hpow_nn]
    -- ((Fspec.toFun T)^n)^(1/n) = Fspec.toFun T.
    have hn_ne : ((n : ℕ+) : ℕ) ≠ 0 := n.pos.ne'
    have hdiv : (1 : ℝ) / ((n : ℕ+) : ℕ) = (((n : ℕ+) : ℕ) : ℝ)⁻¹ := one_div _
    rw [hdiv]
    exact Real.pow_rpow_inv_natCast hFspecT_nn hn_ne
  -- The infimum of a constant is the constant.
  have hcongr :
      (fun n : ℕ+ =>
          ((Func.toFun n (tensorPow (F := ℂ) (V := KTensor ℂ d) n T)) : ℝ) ^
            ((1 : ℝ) / ((n : ℕ+) : ℕ)))
        = fun _ : ℕ+ => Fspec.toFun T := by
    funext n; exact hterm n
  rw [hcongr]
  exact (ciInf_const).symm

private lemma Fspec_admissible_on_format {k : ℕ} (d : Fin k → ℕ+)
    (Fspec : SpectralPoint k ℂ) :
    ∃ Func : AdmissibleFunctional ℂ (KTensor ℂ d),
      (∀ (n : ℕ+) (T : TensorPower ℂ (n : ℕ) (KTensor ℂ d)),
        Func.toFun n T = Real.toNNReal (Fspec.toFun (regroupingMap d n T))) ∧
      ∀ T : KTensor ℂ d, Fspec.toFun T = Func.regularize T := by
  obtain ⟨Func, hFunc⟩ := Fspec_regroupingMap_admissible_exists d Fspec
  exact ⟨Func, hFunc, Fspec_regroupingMap_regularization_eq d Fspec Func hFunc⟩

private lemma Fspec_eq_regularization_per_format {k : ℕ} (d : Fin k → ℕ+)
    (Fspec : SpectralPoint k ℂ) :
    ∃ Func : AdmissibleFunctional ℂ (KTensor ℂ d),
      ∀ T : KTensor ℂ d, Fspec.toFun T = Func.regularize T := by
  rcases Fspec_admissible_on_format d Fspec with ⟨Func, _h_toFun, hreg⟩
  exact ⟨Func, hreg⟩

private lemma Fspec_zariskiLSC_per_format {k : ℕ} (d : Fin k → ℕ+)
    (Fspec : SpectralPoint k ℂ) :
    ZariskiLSC (fun T : KTensor ℂ d => Fspec.toFun T) := by
  rcases Fspec_eq_regularization_per_format d Fspec with ⟨Func, hFunc⟩
  intro r
  have hset :
      { T : KTensor ℂ d | Fspec.toFun T ≤ r } =
        { T : KTensor ℂ d | Func.regularize T ≤ r } := by
    ext T
    simp [hFunc T]
  rw [hset]
  exact sublevel_zariski_closed Func r

/-- Fixed-format spectral-point values are Euclidean-closed.

This is the fixed-format input used in Corollary 4.6.  Paper tex:1257 applies
Corollary 4.5 to a spectral point on a fixed tensor format, using the
Zariski-closed sublevel theorem for regularized admissible functionals from
Corollary 2.4 (paper tex:722-727). -/
lemma Fspec_range_per_format_closed {k : ℕ} (d : Fin k → ℕ+)
    (Fspec : SpectralPoint k ℂ) :
    IsClosed (Set.range (fun T : KTensor ℂ d => Fspec.toFun T)) := by
  exact values_euclidean_closed
    (fun T : KTensor ℂ d => Fspec.toFun T)
    (Fspec_zariskiLSC_per_format d Fspec)

private theorem pair_units_uniform_power_lower_bound_complex {k : ℕ}
    (hk : 3 ≤ k) (Fspec : SpectralPoint k ℂ)
    (hpair : ∀ (i j : Fin k) (hij : i ≠ j),
      1 < Fspec.toFun (unitPairTensor (F := ℂ) 2 i j hij)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (i j : Fin k) (hij : i ≠ j) (r : ℕ+),
        (r : ℝ) ^ c ≤ Fspec.toFun (unitPairTensor (F := ℂ) r i j hij) := by
  classical
  let Pair := {p : Fin k × Fin k // p.1 ≠ p.2}
  let pairExp : Pair → ℝ := fun p =>
    (Real.log (Fspec.toFun
        (unitPairTensor (F := ℂ) 2 p.1.1 p.1.2 p.2)) / Real.log 2) / 2
  have hpairExp_pos : ∀ p : Pair, 0 < pairExp p := by
    intro p
    have hx_gt_one :
        1 < Fspec.toFun (unitPairTensor (F := ℂ) 2 p.1.1 p.1.2 p.2) :=
      hpair p.1.1 p.1.2 p.2
    have hlogx_pos :
        0 < Real.log (Fspec.toFun
          (unitPairTensor (F := ℂ) 2 p.1.1 p.1.2 p.2)) :=
      Real.log_pos hx_gt_one
    have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    exact div_pos (div_pos hlogx_pos hlog2_pos) (by norm_num)
  let p₀ : Pair :=
    ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by
      intro h
      exact zero_ne_one (Fin.ext_iff.mp h)⟩
  let c : ℝ := (Finset.univ : Finset Pair).inf' ⟨p₀, Finset.mem_univ p₀⟩ pairExp
  have hc_pos : 0 < c := by
    change 0 < (Finset.univ : Finset Pair).inf' ⟨p₀, Finset.mem_univ p₀⟩ pairExp
    rw [Finset.lt_inf'_iff]
    intro p _
    exact hpairExp_pos p
  have hc_le_pairExp : ∀ p : Pair, c ≤ pairExp p := by
    intro p
    exact Finset.inf'_le pairExp (Finset.mem_univ p)
  refine ⟨c, hc_pos, ?_⟩
  intro i j hij r
  let p : Pair := ⟨(i, j), hij⟩
  let x : ℝ := Fspec.toFun (unitPairTensor (F := ℂ) 2 i j hij)
  let d : ℝ := Real.log x / Real.log 2
  have hx_gt_one : 1 < x := hpair i j hij
  have hx_pos : 0 < x := zero_lt_one.trans hx_gt_one
  have hlogx_pos : 0 < Real.log x := Real.log_pos hx_gt_one
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hd_pos : 0 < d := div_pos hlogx_pos hlog2_pos
  have hc_le_d_half : c ≤ d / 2 := by
    simpa [p, pairExp, x, d] using hc_le_pairExp p
  have hbase_ge_one : (1 : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast r.2
  have hreduce_exp : (r : ℝ) ^ c ≤ (r : ℝ) ^ (d / 2) :=
    Real.rpow_le_rpow_of_exponent_le hbase_ge_one hc_le_d_half
  have hpow_two_value :
      ∀ a : ℕ,
        Fspec.toFun (unitPairTensor (F := ℂ)
          (⟨2 ^ a, pow_pos (by norm_num : (0 : ℕ) < 2) a⟩ : ℕ+) i j hij) =
          x ^ a := by
    intro a
    induction a with
    | zero =>
        change Fspec.toFun (unitPairTensor (F := ℂ) 1 i j hij) = 1
        simpa [x] using Fspec.unitPair_one i j hij
    | succ a ih =>
        let powTwo : ℕ → ℕ+ :=
          fun n => ⟨2 ^ n, pow_pos (by norm_num : (0 : ℕ) < 2) n⟩
        have hmul := Fspec.unitPair_mul i j hij (powTwo a) (2 : ℕ+)
        have hfmt : powTwo (a + 1) = powTwo a * (2 : ℕ+) := by
          apply PNat.coe_injective
          simp [powTwo, pow_succ, Nat.mul_comm]
        change Fspec.toFun (unitPairTensor (F := ℂ) (powTwo (a + 1)) i j hij) =
          x ^ (a + 1)
        rw [hfmt, hmul]
        rw [ih]
        simp [x, pow_succ]
  by_cases hr_one : (r : ℕ) = 1
  · have hr_eq : r = (1 : ℕ+) := PNat.coe_injective hr_one
    subst r
    simp [Fspec.unitPair_one i j hij]
  · have hr_two_le : 2 ≤ (r : ℕ) := by
      have hr_pos : 0 < (r : ℕ) := r.2
      omega
    let a : ℕ := Nat.log 2 (r : ℕ)
    let powTwo : ℕ → ℕ+ :=
      fun n => ⟨2 ^ n, pow_pos (by norm_num : (0 : ℕ) < 2) n⟩
    have ha_pos : 0 < a := Nat.log_pos (by norm_num : 1 < 2) hr_two_le
    have hlt_pow_succ : (r : ℕ) < 2 ^ (a + 1) := by
      simpa [a] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (r : ℕ)
    have ha_succ_le_two_mul : a + 1 ≤ 2 * a := by omega
    have hpow_succ_le_two_mul : 2 ^ (a + 1) ≤ 2 ^ (2 * a) :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) ha_succ_le_two_mul
    have hr_le_pow_two_mul : (r : ℕ) ≤ 2 ^ (2 * a) :=
      hlt_pow_succ.le.trans hpow_succ_le_two_mul
    have hr_real_le : (r : ℝ) ≤ ((2 ^ (2 * a) : ℕ) : ℝ) := by
      exact_mod_cast hr_le_pow_two_mul
    have hrpow_le :
        (r : ℝ) ^ (d / 2) ≤ (((2 ^ (2 * a) : ℕ) : ℝ)) ^ (d / 2) :=
      Real.rpow_le_rpow (by positivity) hr_real_le (le_of_lt (half_pos hd_pos))
    have hlog_mul_d : Real.log (2 : ℝ) * d = Real.log x := by
      calc
        Real.log (2 : ℝ) * d =
            Real.log (2 : ℝ) * (Real.log x / Real.log (2 : ℝ)) := rfl
        _ = Real.log x := by field_simp [hlog2_pos.ne']
    have htwo_rpow_d : (2 : ℝ) ^ d = x := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), hlog_mul_d,
        Real.exp_log hx_pos]
    have hpow_bound_eq :
        (((2 ^ (2 * a) : ℕ) : ℝ)) ^ (d / 2) = x ^ a := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
      rw [← Real.rpow_natCast (2 : ℝ) (2 * a)]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) ((2 * a : ℕ) : ℝ) (d / 2)]
      have hexp : ((2 * a : ℕ) : ℝ) * (d / 2) = d * (a : ℝ) := by
        norm_num
        ring
      rw [hexp]
      rw [Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2) d a]
      rw [htwo_rpow_d]
    have hpow_le_r : (powTwo a : ℕ) ≤ (r : ℕ) := by
      simpa [powTwo, a] using Nat.pow_log_le_self 2 (PNat.ne_zero r)
    have hmono :
        Fspec.toFun (unitPairTensor (F := ℂ) (powTwo a) i j hij) ≤
          Fspec.toFun (unitPairTensor (F := ℂ) r i j hij) :=
      Fspec.mono
        (unitPairTensor (F := ℂ) (powTwo a) i j hij)
        (unitPairTensor (F := ℂ) r i j hij)
        (unitPairTensor_restricts_of_le (F := ℂ) i j hij hpow_le_r)
    have hx_pow_le :
        x ^ a ≤ Fspec.toFun (unitPairTensor (F := ℂ) r i j hij) := by
      simpa [powTwo] using (hpow_two_value a).symm.le.trans hmono
    exact hreduce_exp.trans (hrpow_le.trans (hpow_bound_eq.le.trans hx_pow_le))

private theorem flatRank_power_le_of_large_subrankPair_complex {k : ℕ}
    (hk : 3 ≤ k) (Fspec : SpectralPoint k ℂ) {cPair : ℝ} (hcPair : 0 < cPair)
    (hunit : ∀ (i j : Fin k) (hij : i ≠ j) (r : ℕ+),
      (r : ℝ) ^ cPair ≤ Fspec.toFun (unitPairTensor (F := ℂ) r i j hij))
    {d : Fin k → ℕ+} (T : KTensor ℂ d) (i j : Fin k) (hij : i ≠ j)
    (hlarge :
      (flatRank T {i} : ℝ) ^ ((1 : ℝ) / ((k : ℝ) - 1)) ≤ subrankPair T i j) :
      (flatRank T {i} : ℝ) ^ (cPair / ((k : ℝ) - 1)) ≤ Fspec.toFun T := by
  classical
  have hk_real : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hkden_pos : 0 < (k : ℝ) - 1 := by linarith
  have hexp_pos : 0 < cPair / ((k : ℝ) - 1) := div_pos hcPair hkden_pos
  have hzero_restricts :
      ∀ {dS dT : Fin k → ℕ+},
        Restricts (F := ℂ) (0 : KTensor ℂ dS) (0 : KTensor ℂ dT) := by
    intro dS dT
    refine ⟨fun _ => 0, ?_⟩
    intro jdx
    simp
  have hF_zero : Fspec.toFun (0 : KTensor ℂ d) = 0 := by
    let dsum : Fin k → ℕ+ := fun ℓ => d ℓ + d ℓ
    have hle₁ :
        Fspec.toFun (0 : KTensor ℂ d) ≤ Fspec.toFun (0 : KTensor ℂ dsum) :=
      Fspec.mono (0 : KTensor ℂ d) (0 : KTensor ℂ dsum) hzero_restricts
    have hle₂ :
        Fspec.toFun (0 : KTensor ℂ dsum) ≤ Fspec.toFun (0 : KTensor ℂ d) :=
      Fspec.mono (0 : KTensor ℂ dsum) (0 : KTensor ℂ d) hzero_restricts
    have hsame :
        Fspec.toFun (0 : KTensor ℂ dsum) = Fspec.toFun (0 : KTensor ℂ d) :=
      le_antisymm hle₂ hle₁
    have hsum_zero :
        (0 : KTensor ℂ d) ⊕ₜ (0 : KTensor ℂ d) = (0 : KTensor ℂ dsum) := by
      ext idx
      simp [directSumTensor, dsum]
    have hadd := Fspec.add (0 : KTensor ℂ d) (0 : KTensor ℂ d)
    have hadd' :
        Fspec.toFun (0 : KTensor ℂ dsum) =
          Fspec.toFun (0 : KTensor ℂ d) + Fspec.toFun (0 : KTensor ℂ d) := by
      rw [← hsum_zero]
      exact hadd
    linarith
  by_cases hflat_zero : flatRank T {i} = 0
  · have hTzero : T = 0 := flatRank_zero_imp_zero T i hflat_zero
    have hleft :
        (flatRank T {i} : ℝ) ^ (cPair / ((k : ℝ) - 1)) = 0 := by
      rw [hflat_zero]
      simpa using Real.zero_rpow (ne_of_gt hexp_pos)
    rw [hleft, hTzero, hF_zero]
  · have hflat_pos_nat : 0 < flatRank T {i} := Nat.pos_of_ne_zero hflat_zero
    have hbase_pos :
        0 < (flatRank T {i} : ℝ) ^ ((1 : ℝ) / ((k : ℝ) - 1)) :=
      Real.rpow_pos_of_pos (by exact_mod_cast hflat_pos_nat) _
    have hsub_pos_real : 0 < (subrankPair T i j : ℝ) :=
      hbase_pos.trans_le hlarge
    have hsub_pos_nat : 0 < subrankPair T i j := by exact_mod_cast hsub_pos_real
    let rSub : ℕ+ := ⟨subrankPair T i j, hsub_pos_nat⟩
    have hsub_witness :
        Restricts (unitPairTensor (F := ℂ) rSub i j hij) T := by
      let S : Set ℕ := { r : ℕ | ∃ hr : 0 < r,
        Restricts (unitPairTensor (F := ℂ) ⟨r, hr⟩ i j hij) T }
      have hsub_eq : subrankPair T i j = sSup S := by
        unfold subrankPair
        simp [hij, S]
      have hS_pos : 0 < sSup S := by
        simpa [hsub_eq] using hsub_pos_nat
      have hS_nonempty : S.Nonempty := by
        by_contra hne
        have hS_empty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
        have hs : sSup S = 0 := by simp [hS_empty]
        omega
      have hS_bdd : BddAbove S := by
        by_contra hbdd
        have hs : sSup S = 0 := Nat.sSup_of_not_bddAbove hbdd
        omega
      obtain ⟨hr, hrest⟩ := Nat.sSup_mem hS_nonempty hS_bdd
      have hrSub_eq : rSub = ⟨sSup S, hr⟩ := by
        apply PNat.coe_injective
        simpa [rSub] using hsub_eq
      rw [hrSub_eq]
      exact hrest
    have hmono :
        Fspec.toFun
            (unitPairTensor (F := ℂ) rSub i j hij) ≤
          Fspec.toFun T :=
      Fspec.mono
        (unitPairTensor (F := ℂ) rSub i j hij) T
        hsub_witness
    have hunit_sub :
        (rSub : ℝ) ^ cPair ≤ Fspec.toFun T :=
      (hunit i j hij rSub).trans hmono
    have hpow_base :
        (flatRank T {i} : ℝ) ^ (cPair / ((k : ℝ) - 1)) ≤
          (rSub : ℝ) ^ cPair := by
      have hleft_eq :
          (flatRank T {i} : ℝ) ^ (cPair / ((k : ℝ) - 1)) =
            ((flatRank T {i} : ℝ) ^ ((1 : ℝ) / ((k : ℝ) - 1))) ^ cPair := by
        rw [← Real.rpow_mul (by positivity)]
        ring_nf
      rw [hleft_eq]
      exact Real.rpow_le_rpow (le_of_lt hbase_pos) (by simpa [rSub] using hlarge)
        (le_of_lt hcPair)
    exact hpow_base.trans hunit_sub

private theorem flatRank_power_le_of_pair_units_complex {k : ℕ}
    (hk : 3 ≤ k) (Fspec : SpectralPoint k ℂ) {cPair : ℝ} (hcPair : 0 < cPair)
    (hunit : ∀ (i j : Fin k) (hij : i ≠ j) (r : ℕ+),
      (r : ℝ) ^ cPair ≤ Fspec.toFun (unitPairTensor (F := ℂ) r i j hij)) :
    ∀ {d : Fin k → ℕ+} (T : KTensor ℂ d) (i : Fin k),
      (flatRank T {i} : ℝ) ^ (cPair / ((k : ℝ) - 1)) ≤ Fspec.toFun T := by
  classical
  intro d T i
  have hFcard : ((flatRank T {i} : ℕ) : Cardinal) < Cardinal.mk ℂ :=
    Cardinal.natCast_lt_aleph0.trans_le (Cardinal.aleph0_le_mk ℂ)
  have hk2 : 2 ≤ k := by omega
  obtain ⟨j, hij, hlarge⟩ :=
    exists_large_subrankPair (F := ℂ) hk2 T i hFcard
  exact flatRank_power_le_of_large_subrankPair_complex
    hk Fspec hcPair hunit T i j hij hlarge

/-- **Corollary 3.3 power lower bound for Case 1** (paper tex:1056-1057,
used at tex:1257).

If all pair units `⟨2⟩_{i,j}` have spectral value strictly larger than `1`,
then Corollary 3.3 (`exists_large_subrankPair`) and monotonicity of the
spectral point give a uniform positive power lower bound for every singleton
flattening rank. -/
private theorem pair_gt_two_implies_flatRank_power_lower_bound_complex {k : ℕ}
    (hk : 3 ≤ k) (Fspec : SpectralPoint k ℂ)
    (hpair : ∀ (i j : Fin k) (hij : i ≠ j),
      1 < Fspec.toFun (unitPairTensor (F := ℂ) 2 i j hij)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {d : Fin k → ℕ+} (T : KTensor ℂ d) (i : Fin k),
        (flatRank T {i} : ℝ) ^ c ≤ Fspec.toFun T := by
  /- Paper tex:1056-1057 / tex:1257.

     For each ordered pair `i ≠ j`, `hpair i j hij` and multiplicativity on
     pair-units give an exponent `c_ij > 0` with
       `F(⟨r⟩_{i,j}) ≥ r^c_ij`.
     Corollary 3.3 (`exists_large_subrankPair`) gives `j ≠ i` with
       `subrankPair T i j ≥ flatRank_i(T)^(1/(k-1))`.
     The restriction witness in the definition of `subrankPair`, plus
     `Fspec.mono`, transfers the pair-unit lower bound to `T`; take the
     finite minimum of the positive `c_ij`.
  -/
  classical
  obtain ⟨cPair, hcPair, hunit⟩ :=
    pair_units_uniform_power_lower_bound_complex hk Fspec hpair
  refine ⟨cPair / ((k : ℝ) - 1), ?_, ?_⟩
  · have hk_real : (3 : ℝ) ≤ k := by exact_mod_cast hk
    exact div_pos hcPair (by linarith)
  · exact flatRank_power_le_of_pair_units_complex hk Fspec hcPair hunit

private lemma le_rpow_one_div_of_rpow_le {a M c : ℝ}
    (ha : 0 ≤ a) (hc : 0 < c) (h : a ^ c ≤ M) :
    a ≤ M ^ ((1 : ℝ) / c) := by
  have hM : 0 ≤ M := (Real.rpow_nonneg ha c).trans h
  have hinv : 0 ≤ (1 : ℝ) / c := by positivity
  have hroot :
      (a ^ c) ^ ((1 : ℝ) / c) ≤ M ^ ((1 : ℝ) / c) :=
    Real.rpow_le_rpow (Real.rpow_nonneg ha c) h hinv
  have hsimp : (a ^ c) ^ ((1 : ℝ) / c) = a := by
    rw [← Real.rpow_mul ha]
    have hcne : c ≠ 0 := ne_of_gt hc
    field_simp [hcne]
    rw [Real.rpow_one]
  rw [hsimp] at hroot
  exact hroot

-- `dif_pos`/`dif_neg` simp args below force dependent `if`-branch reduction and
-- are load-bearing despite the unusedSimpArgs linter flagging them.
set_option linter.unusedSimpArgs false in
/-- Order-two restriction-equivalence to the rank-`r` unit tensor (paper tex:1051).

For a `2`-tensor `T` with `r = flatRank T {0} > 0`, the rank factorization of
`flattenMatrix T {0}` gives a two-way restriction `T ∼ₜ unitTensor ⟨r⟩`.  This is
the `ℂ`-specialization of `tensor_restricts_equiv_unitTensor_k2` from
`SpectrumWellOrdered.lean` (reproduced here because `EuclideanClosed` does not
import that sibling module). -/
private lemma tensor_restricts_equiv_unitTensor_k2_complex {d : Fin 2 → ℕ+}
    (T : KTensor ℂ d) {r : ℕ} (hr : 0 < r) (hrank : flatRank T {0} = r) :
    Restricts (unitTensor ℂ (k := 2) ⟨r, hr⟩) T ∧
      Restricts T (unitTensor ℂ (k := 2) ⟨r, hr⟩) := by
  classical
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  -- Flattening at I = {0}: rows = leg 0, cols = leg 1.
  set M : Matrix _ _ ℂ := flattenMatrix T {(0 : Fin 2)} with hM_def
  have hMrank : M.rank = r := by rw [hM_def]; exact hrank
  set φ : _ →ₗ[ℂ] _ := M.mulVecLin with hφ_def
  have hrange_dim : Module.finrank ℂ (LinearMap.range φ) = r := by
    rw [← hMrank]; rfl
  obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
      (R := ℂ) (M := Fin r → ℂ) (M' := LinearMap.range φ)
      (by rw [Module.finrank_fin_fun]; exact hrange_dim.symm)
  set U : (Fin r → ℂ) →ₗ[ℂ] _ :=
    (LinearMap.range φ).subtype ∘ₗ e.toLinearMap with hU_def
  have hU_inj : Function.Injective U := fun x y hxy =>
    e.injective (Subtype.ext hxy)
  set φ' : _ →ₗ[ℂ] LinearMap.range φ :=
    φ.codRestrict (LinearMap.range φ) (fun v => LinearMap.mem_range_self φ v) with hφ'_def
  set V : _ →ₗ[ℂ] (Fin r → ℂ) := e.symm.toLinearMap ∘ₗ φ' with hV_def
  have hV_surj : Function.Surjective V := by
    refine e.symm.surjective.comp ?_
    intro y
    obtain ⟨v, hv⟩ := y.2
    exact ⟨v, Subtype.ext hv⟩
  have hφ_eq : φ = U ∘ₗ V := by
    apply LinearMap.ext
    intro c
    change φ c = (LinearMap.range φ).subtype (e (e.symm (φ' c)))
    rw [e.apply_symm_apply]
    rfl
  obtain ⟨A_lin, hAU⟩ := LinearMap.exists_leftInverse_of_injective U
    (LinearMap.ker_eq_bot_of_injective hU_inj)
  obtain ⟨B_lin, hVB⟩ := LinearMap.exists_rightInverse_of_surjective V
    (LinearMap.range_eq_top.mpr hV_surj)
  have hkey : (A_lin ∘ₗ φ) ∘ₗ B_lin = LinearMap.id := by
    rw [hφ_eq]
    have h1 : (A_lin ∘ₗ (U ∘ₗ V)) ∘ₗ B_lin = (A_lin ∘ₗ U) ∘ₗ (V ∘ₗ B_lin) := by
      apply LinearMap.ext; intro x; rfl
    rw [h1, hAU, hVB]
    apply LinearMap.ext; intro x; rfl
  -- The four leg matrices.
  set A := LinearMap.toMatrix' A_lin with hA_def     -- Fin r × rows
  set B := LinearMap.toMatrix' B_lin with hB_def     -- cols × Fin r
  set Pu := LinearMap.toMatrix' U with hPu_def       -- rows × Fin r
  set Qv := LinearMap.toMatrix' V with hQv_def       -- Fin r × cols
  have hAMB : A * M * B = (1 : Matrix (Fin r) (Fin r) ℂ) := by
    have heq : A * M * B = LinearMap.toMatrix' ((A_lin ∘ₗ φ) ∘ₗ B_lin) := by
      rw [hA_def, hB_def]
      rw [show (A_lin ∘ₗ φ) ∘ₗ B_lin = A_lin ∘ₗ (φ ∘ₗ B_lin) by
            apply LinearMap.ext; intro x; rfl]
      rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp]
      rw [show LinearMap.toMatrix' φ = M by
            rw [hφ_def]; exact (LinearMap.toMatrix'_toLin' M)]
      exact Matrix.mul_assoc _ _ _
    rw [heq, hkey, LinearMap.toMatrix'_id]
  have hMfac : Pu * Qv = M := by
    rw [hPu_def, hQv_def, ← LinearMap.toMatrix'_comp, ← hφ_eq]
    rw [hφ_def]; exact LinearMap.toMatrix'_toLin' M
  -- Index transport infrastructure for I = {0}.
  have mem0 : (0 : Fin 2) ∈ ({0} : Finset (Fin 2)) := Finset.mem_singleton_self 0
  have notmem1 : (1 : Fin 2) ∉ ({0} : Finset (Fin 2)) := by decide
  have hrowval : ∀ x : { x // x ∈ ({0} : Finset (Fin 2)) }, x.val = 0 :=
    fun x => Finset.mem_singleton.mp x.2
  have hcolval : ∀ x : { x // x ∉ ({0} : Finset (Fin 2)) }, x.val = 1 := by
    rintro ⟨x, hx⟩; rw [Finset.mem_singleton] at hx
    change x = 1
    apply Fin.ext
    have hx2 := x.isLt
    have hx0 : x.val ≠ 0 := fun h => hx (Fin.ext h)
    omega
  -- Row/col reindexers between Fin (d 0)/Fin (d 1) and the flattening index types.
  let rowOf : Fin (d 0) → ((x : { x // x ∈ ({0} : Finset (Fin 2)) }) → Fin (d x.val)) :=
    fun q x => Fin.cast (by rw [hrowval x]) q
  let colOf : Fin (d 1) → ((x : { x // x ∉ ({0} : Finset (Fin 2)) }) → Fin (d x.val)) :=
    fun q x => Fin.cast (by rw [hcolval x]) q
  have hprod2 : ∀ (g : Fin 2 → ℂ), (∏ ℓ, g ℓ) = g 0 * g 1 := by
    intro g; rw [Fin.prod_univ_two]
  -- `unitTensor`'s legs are all `Fin r`; reindex `Fin ((fun _ => r) ℓ)` ↔ `Fin r`.
  have hudim : ∀ ℓ : Fin 2, (((fun _ : Fin 2 => (⟨r, hr⟩ : ℕ+)) ℓ : ℕ+) : ℕ) = r :=
    fun _ => rfl
  -- Transport of the combined-index value at legs 0,1 through the row/col split.
  have hti : ∀ (rowT : (x : { x // x ∈ ({0} : Finset (Fin 2)) }) → Fin (d x.val))
      (colT : (x : { x // x ∉ ({0} : Finset (Fin 2)) }) → Fin (d x.val)),
      ((Equiv.piEquivPiSubtypeProd (· ∈ ({0} : Finset (Fin 2)))
          (fun x => Fin (d x))).symm (rowT, colT)) 0 = rowT ⟨0, mem0⟩ := by
    intro rowT colT
    rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos mem0]
  have htj : ∀ (rowT : (x : { x // x ∈ ({0} : Finset (Fin 2)) }) → Fin (d x.val))
      (colT : (x : { x // x ∉ ({0} : Finset (Fin 2)) }) → Fin (d x.val)),
      ((Equiv.piEquivPiSubtypeProd (· ∈ ({0} : Finset (Fin 2)))
          (fun x => Fin (d x))).symm (rowT, colT)) 1 = colT ⟨1, notmem1⟩ := by
    intro rowT colT
    rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg notmem1]
  have hTval : ∀ (rowT : (x : { x // x ∈ ({0} : Finset (Fin 2)) }) → Fin (d x.val))
      (colT : (x : { x // x ∉ ({0} : Finset (Fin 2)) }) → Fin (d x.val)),
      T ((Equiv.piEquivPiSubtypeProd (· ∈ ({0} : Finset (Fin 2)))
          (fun x => Fin (d x))).symm (rowT, colT)) = M rowT colT := by
    intro rowT colT; rw [hM_def, flattenMatrix]; congr 1
  have hrow : ∀ (rowT : (x : { x // x ∈ ({0} : Finset (Fin 2)) }) → Fin (d x.val)),
      rowOf (rowT ⟨0, mem0⟩) = rowT := by
    intro rowT; funext x; obtain ⟨x, hx⟩ := x
    have hxi : x = 0 := Finset.mem_singleton.mp hx; subst hxi; rfl
  have hcol : ∀ (colT : (x : { x // x ∉ ({0} : Finset (Fin 2)) }) → Fin (d x.val)),
      colOf (colT ⟨1, notmem1⟩) = colT := by
    intro colT; funext x
    have hxj : x.val = 1 := hcolval x
    obtain ⟨x, hx⟩ := x; simp only at hxj; subst hxj; rfl
  -- leg-`ℓ` index of `unitTensor ℂ ⟨r⟩` reindexed to `Fin r`.
  set toFinr : ∀ ℓ : Fin 2, Fin ((fun _ : Fin 2 => (⟨r, hr⟩ : ℕ+)) ℓ) → Fin r :=
    fun ℓ p => Fin.cast (hudim ℓ) p with htoFinr_def
  refine ⟨?_, ?_⟩
  · -- Direction 1: `unitTensor ℂ ⟨r⟩ ≤ₜ T` via leg matrices `A`, `Bᵀ`.
    set C1leg : ∀ ℓ : Fin 2,
        Matrix (Fin ((fun _ : Fin 2 => (⟨r, hr⟩ : ℕ+)) ℓ)) (Fin (d ℓ)) ℂ :=
      fun ℓ => if hℓ : ℓ = 0 then
          (fun p q => A (toFinr ℓ p) (rowOf (hℓ ▸ q)))
        else if hℓ' : ℓ = 1 then
          (fun p q => B (colOf (hℓ' ▸ q)) (toFinr ℓ p))
        else 0 with hC1_def
    refine ⟨C1leg, ?_⟩
    intro jdx
    set a : Fin r := toFinr 0 (jdx 0) with ha_def
    set b : Fin r := toFinr 1 (jdx 1) with hb_def
    have hC1_0 : ∀ q : Fin (d 0), C1leg 0 (jdx 0) q = A a (rowOf q) := by
      intro q; simp only [hC1_def, dif_pos (rfl : (0 : Fin 2) = 0)]; rfl
    have hC1_1 : ∀ q : Fin (d 1), C1leg 1 (jdx 1) q = B (colOf q) b := by
      intro q
      simp only [hC1_def, dif_neg (by decide : (1 : Fin 2) ≠ 0),
        dif_pos (rfl : (1 : Fin 2) = 1)]
      rfl
    have hrhs : (∑ idx, (∏ ℓ, C1leg ℓ (jdx ℓ) (idx ℓ)) * T idx) = (A * M * B) a b := by
      rw [Matrix.mul_apply]
      simp_rw [Matrix.mul_apply, Finset.sum_mul]
      rw [← Equiv.sum_comp (Equiv.piEquivPiSubtypeProd (· ∈ ({0} : Finset (Fin 2)))
              (fun x => Fin (d x))).symm
            (fun idx : (∀ x : Fin 2, Fin (d x)) =>
              (∏ ℓ, C1leg ℓ (jdx ℓ) (idx ℓ)) * T idx)]
      rw [Fintype.sum_prod_type]
      rw [show (∑ k, ∑ k_1, A a k_1 * M k_1 k * B k b)
            = ∑ rowT, ∑ colT, A a rowT * M rowT colT * B colT b from by
          rw [Finset.sum_comm]]
      refine Finset.sum_congr rfl ?_
      intro rowT _
      refine Finset.sum_congr rfl ?_
      intro colT _
      rw [hprod2, hC1_0, hC1_1, hti rowT colT, htj rowT colT, hrow, hcol, hTval]
      ring
    rw [hrhs, hAMB, Matrix.one_apply]
    change (unitTensor ℂ (k := 2) ⟨r, hr⟩) jdx = _
    rw [unitTensor]
    by_cases heq : a = b
    · rw [if_pos heq, if_pos]
      have hv : (jdx 0).val = (jdx 1).val := by
        have := congrArg Fin.val heq
        simpa [ha_def, hb_def, htoFinr_def] using this
      intro x y
      fin_cases x <;> fin_cases y <;>
        first
        | rfl
        | (apply Fin.ext; exact hv)
        | (apply Fin.ext; exact hv.symm)
    · rw [if_neg heq, if_neg]
      intro hall
      apply heq
      apply Fin.ext
      have hxy := hall 0 1
      simp only [ha_def, hb_def, htoFinr_def, Fin.val_cast]
      exact congrArg Fin.val hxy
  · -- Direction 2: `T ≤ₜ unitTensor ℂ ⟨r⟩` via leg matrices `Pu`, `Qvᵀ`.
    set D2leg : ∀ ℓ : Fin 2,
        Matrix (Fin (d ℓ)) (Fin ((fun _ : Fin 2 => (⟨r, hr⟩ : ℕ+)) ℓ)) ℂ :=
      fun ℓ => if hℓ : ℓ = 0 then
          (fun q p => Pu (rowOf (hℓ ▸ q)) (toFinr ℓ p))
        else if hℓ' : ℓ = 1 then
          (fun q p => Qv (toFinr ℓ p) (colOf (hℓ' ▸ q)))
        else 0 with hD2_def
    refine ⟨D2leg, ?_⟩
    intro jdx
    have hD2_0 : ∀ (p : Fin ((fun _ : Fin 2 => (⟨r, hr⟩ : ℕ+)) 0)),
        D2leg 0 (jdx 0) p = Pu (rowOf (jdx 0)) (toFinr 0 p) := by
      intro p; simp only [hD2_def, dif_pos (rfl : (0 : Fin 2) = 0)]
    have hD2_1 : ∀ (p : Fin ((fun _ : Fin 2 => (⟨r, hr⟩ : ℕ+)) 1)),
        D2leg 1 (jdx 1) p = Qv (toFinr 1 p) (colOf (jdx 1)) := by
      intro p
      simp only [hD2_def, dif_neg (by decide : (1 : Fin 2) ≠ 0)]
      rfl
    -- Reduce the RHS sum to `(Pu * Qv) (rowOf (jdx 0)) (colOf (jdx 1))`.
    have hgoal : T jdx = (Pu * Qv) (rowOf (jdx 0)) (colOf (jdx 1)) := by
      have hM0 : (Pu * Qv) (rowOf (jdx 0)) (colOf (jdx 1)) = M (rowOf (jdx 0)) (colOf (jdx 1)) := by
        rw [hMfac]
      rw [hM0, hM_def, flattenMatrix]
      congr 1
      funext ℓ
      fin_cases ℓ
      · simp [rowOf]
      · simp [colOf]
    rw [hgoal, Matrix.mul_apply]
    -- RHS: `∑ idx, (∏ ℓ, D2leg ℓ (jdx ℓ) (idx ℓ)) * unitTensor idx`.
    rw [show (∑ idx, (∏ i, D2leg i (jdx i) (idx i)) * (unitTensor ℂ (k := 2) ⟨r, hr⟩) idx)
          = ∑ pp : Fin r × Fin r,
              (∏ i, D2leg i (jdx i)
                ((piFinTwoEquiv (fun ℓ : Fin 2 => Fin ((fun _ : Fin 2 => (⟨r, hr⟩ : ℕ+)) ℓ))).symm
                  pp i)) *
                (unitTensor ℂ (k := 2) ⟨r, hr⟩)
                  ((piFinTwoEquiv (fun ℓ : Fin 2 => Fin ((fun _ : Fin 2 => (⟨r, hr⟩ : ℕ+)) ℓ))).symm
                    pp)
        from (Equiv.sum_comp
          (piFinTwoEquiv (fun ℓ : Fin 2 => Fin ((fun _ : Fin 2 => (⟨r, hr⟩ : ℕ+)) ℓ))).symm
          (fun idx => (∏ i, D2leg i (jdx i) (idx i)) *
            (unitTensor ℂ (k := 2) ⟨r, hr⟩) idx)).symm]
    rw [Fintype.sum_prod_type]
    -- Evaluate the inner double sum.
    refine Finset.sum_congr rfl ?_
    intro p0 _
    rw [Finset.sum_eq_single p0]
    · -- diagonal term `p1 = p0`.
      have hidx0 : (piFinTwoEquiv (fun ℓ : Fin 2 => Fin ((fun _ : Fin 2 => (⟨r, hr⟩ : ℕ+)) ℓ))).symm
          (p0, p0) 0 = p0 := rfl
      have hidx1 : (piFinTwoEquiv (fun ℓ : Fin 2 => Fin ((fun _ : Fin 2 => (⟨r, hr⟩ : ℕ+)) ℓ))).symm
          (p0, p0) 1 = p0 := rfl
      rw [hprod2, hidx0, hidx1, hD2_0, hD2_1]
      have hunit1 : (unitTensor ℂ (k := 2) ⟨r, hr⟩)
          ((piFinTwoEquiv (fun ℓ : Fin 2 => Fin ((fun _ : Fin 2 => (⟨r, hr⟩ : ℕ+)) ℓ))).symm
            (p0, p0)) = 1 := by
        rw [unitTensor, if_pos]
        intro a b
        fin_cases a <;> fin_cases b <;> rfl
      rw [hunit1, mul_one]
      change Pu (rowOf (jdx 0)) p0 * Qv p0 (colOf (jdx 1))
        = Pu (rowOf (jdx 0)) (toFinr 0 p0) * Qv (toFinr 1 p0) (colOf (jdx 1))
      rfl
    · -- off-diagonal `p1 ≠ p0`: unit factor is 0.
      intro p1 _ hp1
      have hunit0 : (unitTensor ℂ (k := 2) ⟨r, hr⟩)
          ((piFinTwoEquiv (fun ℓ : Fin 2 => Fin ((fun _ : Fin 2 => (⟨r, hr⟩ : ℕ+)) ℓ))).symm
            (p0, p1)) = 0 := by
        rw [unitTensor, if_neg]
        intro hall
        exact hp1 (hall 1 0)
      rw [hunit0, mul_zero]
    · intro hp0; exact absurd (Finset.mem_univ _) hp0

/-- Pointwise integrality of order-two spectral values over `ℂ` (paper tex:1051).

Every spectral point on matrices is ordinary matrix rank, hence every individual
value is a natural number viewed in `ℝ`.  `ℂ`-specialization of
`order_two_spectral_value_mem_natCast_range`. -/
private lemma order_two_spectral_value_mem_natCast_range_complex
    (Fspec : SpectralPoint 2 ℂ) {d : Fin 2 → ℕ+} (T : KTensor ℂ d) :
    Fspec.toFun T ∈ Set.range (fun n : ℕ => (n : ℝ)) := by
  classical
  set r : ℕ := flatRank T {(0 : Fin 2)} with hr_def
  refine ⟨r, ?_⟩
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · -- Zero tensor: `flatRank T {0} = 0 ⟹ T = 0 ⟹ Fspec.toFun T = 0`.
    have hMrank0 : (flattenMatrix T {(0 : Fin 2)}).rank = 0 := hr0
    have hM0 : flattenMatrix T {(0 : Fin 2)} = 0 := by
      have hrange : LinearMap.range (flattenMatrix T {(0 : Fin 2)}).mulVecLin = ⊥ := by
        have hfin : Module.finrank ℂ
            (LinearMap.range (flattenMatrix T {(0 : Fin 2)}).mulVecLin) = 0 := hMrank0
        exact Submodule.finrank_eq_zero.mp hfin
      have hmvl : (flattenMatrix T {(0 : Fin 2)}).mulVecLin = 0 := by
        rw [LinearMap.range_eq_bot] at hrange; exact hrange
      apply Matrix.ext_of_mulVec_single
      intro i
      have heq : (flattenMatrix T {(0 : Fin 2)}).mulVec (Pi.single i 1)
          = (flattenMatrix T {(0 : Fin 2)}).mulVecLin (Pi.single i 1) := rfl
      rw [heq, hmvl]
      ext k
      simp
    have hT0 : T = 0 := by
      funext jdx
      have hflat := congrFun (congrFun hM0
        (fun x => jdx x.val)) (fun x => jdx x.val)
      simp only [flattenMatrix, Matrix.zero_apply, Pi.zero_apply] at hflat ⊢
      rw [← hflat]; congr 1; funext i; split <;> rfl
    -- `Fspec.toFun 0 = 0` via `0 ⊕ₜ 0 ∼ₜ 0` and additivity.
    have hdsum : Restricts ((0 : KTensor ℂ d) ⊕ₜ (0 : KTensor ℂ d)) (0 : KTensor ℂ d) ∧
        Restricts (0 : KTensor ℂ d) ((0 : KTensor ℂ d) ⊕ₜ (0 : KTensor ℂ d)) := by
      constructor
      · refine ⟨fun _ => 0, ?_⟩
        intro jdx; simp [directSumTensor]
      · refine ⟨fun _ => 0, ?_⟩
        intro jdx; simp [directSumTensor]
    have hle1 := Fspec.mono _ _ hdsum.1
    have hle2 := Fspec.mono _ _ hdsum.2
    have hadd := Fspec.add (0 : KTensor ℂ d) (0 : KTensor ℂ d)
    have heqsum : Fspec.toFun ((0 : KTensor ℂ d) ⊕ₜ (0 : KTensor ℂ d))
        = Fspec.toFun (0 : KTensor ℂ d) := le_antisymm hle1 hle2
    rw [hadd] at heqsum
    have hzero : Fspec.toFun (0 : KTensor ℂ d) = 0 := by linarith
    rw [hT0, hzero, hr0]; norm_num
  · -- Positive rank: `T ∼ₜ unitTensor ⟨r⟩`, value `r`.
    obtain ⟨hunit_le, hle_unit⟩ :=
      tensor_restricts_equiv_unitTensor_k2_complex T hrpos hr_def.symm
    have hmono1 := Fspec.mono _ _ hunit_le
    have hmono2 := Fspec.mono _ _ hle_unit
    rw [Fspec.normalize ⟨r, hrpos⟩] at hmono1 hmono2
    have hval : Fspec.toFun T = ((⟨r, hrpos⟩ : ℕ+) : ℕ) := le_antisymm hmono2 hmono1
    change (r : ℝ) = Fspec.toFun T
    rw [hval]

/-- Corollary 4.6, base case `k = 2`.

Paper tex:1253: spectral points on matrices are matrix rank, so the value set is
`ℕ` (real-coerced), hence Euclidean-closed. -/
private lemma order_two_spectral_values_eq_natCast_range (Fspec : SpectralPoint 2 ℂ) :
    (⋃ d : Fin 2 → ℕ+, Set.range (fun T : KTensor ℂ d => Fspec.toFun T)) =
      Set.range (fun n : ℕ => (n : ℝ)) := by
  -- Classical k=2 spectrum classification (Strassen): every spectral point is
  -- ordinary matrix rank, so the value set is exactly the nonnegative integer
  -- matrix ranks (real-coerced).
  classical
  apply Set.eq_of_subset_of_subset
  · -- (⊆) every value is a natural number via the matrix-rank classification.
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_range] at hx
    obtain ⟨d, T, rfl⟩ := hx
    exact order_two_spectral_value_mem_natCast_range_complex Fspec T
  · -- (⊇) every `(n : ℝ)` is achieved: `n = 0` by the zero tensor, `n ≥ 1` by
    -- the `(n,n)` unit tensor (normalized to value `n`).
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    simp only [Set.mem_iUnion, Set.mem_range]
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · -- `n = 0`: zero tensor in format `(1,1)` has value `0`.
      refine ⟨fun _ : Fin 2 => (1 : ℕ+),
        (0 : KTensor ℂ (fun _ : Fin 2 => (1 : ℕ+))), ?_⟩
      have hadd := Fspec.add (0 : KTensor ℂ (fun _ : Fin 2 => (1 : ℕ+)))
        (0 : KTensor ℂ (fun _ : Fin 2 => (1 : ℕ+)))
      have hdsum :
          Restricts ((0 : KTensor ℂ (fun _ : Fin 2 => (1 : ℕ+))) ⊕ₜ
              (0 : KTensor ℂ (fun _ : Fin 2 => (1 : ℕ+))))
              (0 : KTensor ℂ (fun _ : Fin 2 => (1 : ℕ+))) ∧
            Restricts (0 : KTensor ℂ (fun _ : Fin 2 => (1 : ℕ+)))
              ((0 : KTensor ℂ (fun _ : Fin 2 => (1 : ℕ+))) ⊕ₜ
                (0 : KTensor ℂ (fun _ : Fin 2 => (1 : ℕ+)))) := by
        constructor
        · exact ⟨fun _ => 0, fun jdx => by simp [directSumTensor]⟩
        · exact ⟨fun _ => 0, fun jdx => by simp [directSumTensor]⟩
      have hle1 := Fspec.mono _ _ hdsum.1
      have hle2 := Fspec.mono _ _ hdsum.2
      have heqsum :
          Fspec.toFun ((0 : KTensor ℂ (fun _ : Fin 2 => (1 : ℕ+))) ⊕ₜ
              (0 : KTensor ℂ (fun _ : Fin 2 => (1 : ℕ+))))
            = Fspec.toFun (0 : KTensor ℂ (fun _ : Fin 2 => (1 : ℕ+))) := le_antisymm hle1 hle2
      rw [hadd] at heqsum
      have hzero : Fspec.toFun (0 : KTensor ℂ (fun _ : Fin 2 => (1 : ℕ+))) = 0 := by linarith
      rw [hzero, hn0]; norm_num
    · -- `n ≥ 1`: the `(n,n)` unit tensor has value `n` by `Fspec.normalize`.
      refine ⟨fun _ => ⟨n, hnpos⟩, unitTensor ℂ (k := 2) ⟨n, hnpos⟩, ?_⟩
      rw [Fspec.normalize ⟨n, hnpos⟩]
      norm_cast

private lemma asympSpectrum_values_euclidean_closed_order_two {k : ℕ}
    (hk : 2 ≤ k) (hnk : ¬ 3 ≤ k) (Fspec : SpectralPoint k ℂ) :
    IsClosed (⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor ℂ d => Fspec.toFun T)) := by
  have hk_eq : k = 2 := by omega
  subst hk_eq
  rw [order_two_spectral_values_eq_natCast_range Fspec]
  exact Nat.isClosedEmbedding_coe_real.isClosed_range

/-- Corollary 4.6, descent branch.

If some pair unit has value `1`, paper tex:1254-1256 permutes that pair to the
last two legs, applies Lemma 3.8 (`spec_descend`) to descend to `(k-1)`-tensors,
and invokes the induction hypothesis.

The leg permutation is realized via `SpectralPoint.reindex`:
build `σ : Equiv.Perm (Fin k)` carrying the witness pair `(i, j)` to the last
two legs, set `Gspec := Fspec.reindex σ` (same value set as `Fspec` by
`reindex_iUnion_range`, last-pair value `= 1` by `reindex_toFun_unitPairTensor`),
run the `spec_descend` descent on `Gspec`, and transfer `IsClosed` back. -/
private lemma asympSpectrum_values_euclidean_closed_pair_eq_one {k : ℕ}
    (hk : 3 ≤ k) (Fspec : SpectralPoint k ℂ)
    (hpair : ∃ (i j : Fin k) (hij : i ≠ j),
      Fspec.toFun (unitPairTensor (F := ℂ) 2 i j hij) = 1)
    (hIH : ∀ Fspec' : SpectralPoint (k - 1) ℂ,
      IsClosed
        (⋃ e : Fin (k - 1) → ℕ+,
          Set.range (fun U : KTensor ℂ e => Fspec'.toFun U))) :
    IsClosed (⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor ℂ d => Fspec.toFun T)) := by
  classical
  obtain ⟨i, j, hij, hval⟩ := hpair
  let last₀ : Fin k := ⟨k - 2, by omega⟩
  let last₁ : Fin k := ⟨k - 1, by omega⟩
  have hlast_ne : last₀ ≠ last₁ := by
    intro h
    exact (by omega : ¬ (k - 2 = k - 1)) (Fin.ext_iff.mp h)
  -- A permutation carrying the witness pair `(i, j)` to the last two legs.
  obtain ⟨σ, hσi, hσj⟩ := exists_perm_mapping_pair i j hij last₀ last₁ hlast_ne
  have hsymm₀ : σ.symm last₀ = i := by rw [← hσi, Equiv.symm_apply_apply]
  have hsymm₁ : σ.symm last₁ = j := by rw [← hσj, Equiv.symm_apply_apply]
  subst hsymm₀
  subst hsymm₁
  -- Pulled-back spectral point: same value set, free pair now at the last legs.
  set Gspec : SpectralPoint k ℂ := Fspec.reindex σ with hGspec
  have hlast : Gspec.toFun (unitPairTensor (F := ℂ) 2 last₀ last₁ hlast_ne) = 1 := by
    rw [hGspec, SpectralPoint.reindex_toFun_unitPairTensor (F := ℂ)
      Fspec σ 2 last₀ last₁ hlast_ne hij]
    exact hval
  -- Descend `Gspec` to a `(k-1)`-tensor spectral point and identify value sets.
  obtain ⟨Gspec', hphi, hgamma⟩ := spec_descend (F := ℂ) hk Gspec hlast_ne hlast
  have hsets :
      (⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor ℂ d => Gspec.toFun T)) =
        (⋃ e : Fin (k - 1) → ℕ+,
          Set.range (fun U : KTensor ℂ e => Gspec'.toFun U)) := by
    ext x
    constructor
    · intro hx
      simp only [Set.mem_iUnion, Set.mem_range] at hx ⊢
      obtain ⟨d, T, hT⟩ := hx
      refine ⟨dGamma hk d, gammaMap (F := ℂ) hk T, ?_⟩
      rw [← hT]
      exact (hgamma T).symm
    · intro hx
      simp only [Set.mem_iUnion, Set.mem_range] at hx ⊢
      obtain ⟨e, U, hU⟩ := hx
      refine ⟨dPhi hk e, phiMap (F := ℂ) hk U, ?_⟩
      rw [← hU]
      exact (hphi U).symm
  -- `IsClosed (⋃ range Gspec)` from the descent + IH, then transfer to `Fspec`.
  have hclosed : IsClosed
      (⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor ℂ d => Gspec.toFun T)) := by
    rw [hsets]; exact hIH Gspec'
  rwa [hGspec, SpectralPoint.reindex_iUnion_range] at hclosed

-- The `dOne`/`a` local-let unfolds below are flagged unused by the
-- unusedSimpArgs linter but keep the proof robust to definitional unfolding.
set_option linter.unusedSimpArgs false in
set_option linter.flexible false in
/-- Corollary 4.6, bounded-format branch.

If every pair unit has value strictly larger than `1`, the Corollary 3.3 growth
bound gives a finite-format reduction for convergent value sequences; the
finite union is closed by `Fspec_range_per_format_closed`. -/
private lemma asympSpectrum_values_euclidean_closed_all_pairs_gt {k : ℕ}
    (hk : 3 ≤ k) (Fspec : SpectralPoint k ℂ)
    (hpair : ∀ (i j : Fin k) (hij : i ≠ j),
      1 < Fspec.toFun (unitPairTensor (F := ℂ) 2 i j hij)) :
    IsClosed (⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor ℂ d => Fspec.toFun T)) := by
  classical
  let S : Set ℝ :=
    ⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor ℂ d => Fspec.toFun T)
  have hbounded_format_reduction :
      ∀ M : ℝ, ∃ N : ℕ, 0 < N ∧
        S ∩ Set.Iic M ⊆
          ⋃ a : Fin k → Fin N,
            Set.range (fun T : KTensor ℂ
              (fun j => (⟨(a j).val + 1, Nat.succ_pos _⟩ : ℕ+)) =>
              Fspec.toFun T) := by
    intro M
    -- Paper tex:1256-1260.  Corollary 3.3 gives a uniform `c > 0` with
    -- `(flatRank T {j} : ℝ)^c ≤ Fspec.toFun T` under `hpair`.  Together with
    -- monotonicity and `exists_concise_restriction`, every witness with
    -- `Fspec.toFun T ≤ M` has a restriction-equivalent concise witness whose
    -- format coordinates are bounded by one natural number depending only on
    -- `M`; re-embedding into the corresponding bounded format preserves
    -- `Fspec.toFun` by monotonicity in both restriction directions.
    obtain ⟨c, hcpos, hpower⟩ :=
      pair_gt_two_implies_flatRank_power_lower_bound_complex hk Fspec hpair
    set B : ℝ := max 1 (M ^ ((1 : ℝ) / c)) with hB_def
    set N : ℕ := Nat.ceil B with hN_def
    have hB_ge_one : (1 : ℝ) ≤ B := by simp [hB_def]
    have hN_pos : 0 < N := by
      have hceil_ge_one : (1 : ℕ) ≤ Nat.ceil B := by
        exact_mod_cast hB_ge_one.trans (Nat.le_ceil B)
      simpa [hN_def] using hceil_ge_one
    refine ⟨N, hN_pos, ?_⟩
    rintro x ⟨hxS, hxM⟩
    simp only [S, Set.mem_iUnion, Set.mem_range] at hxS ⊢
    obtain ⟨d, T, hxT⟩ := hxS
    have hxT_le_M : Fspec.toFun T ≤ M := by
      simpa [hxT] using hxM
    by_cases hTzero : T = 0
    · set dOne : Fin k → ℕ+ := fun _ => (1 : ℕ+) with hdOne_def
      let TOne : KTensor ℂ dOne := 0
      have hle_one_d : ∀ j, (dOne j : ℕ) ≤ (d j : ℕ) := by
        intro j
        simp [dOne, hdOne_def]
        exact (d j).2
      have hre_zero : reembed hle_one_d TOne = T := by
        funext idx
        rw [hTzero]
        simp [reembed, TOne]
      have hval_eq : Fspec.toFun TOne = Fspec.toFun T := by
        have hle₁ := Fspec.mono TOne (reembed hle_one_d TOne)
          (reembed_restricts_to hle_one_d TOne)
        have hle₂ := Fspec.mono (reembed hle_one_d TOne) TOne
          (restricts_reembed hle_one_d TOne)
        exact le_antisymm (by simpa [hre_zero] using hle₁)
          (by simpa [hre_zero] using hle₂)
      set a : Fin k → Fin N := fun j => ⟨0, hN_pos⟩ with ha_def
      refine ⟨a, TOne, ?_⟩
      rw [← hxT, ← hval_eq]
    · obtain ⟨d', T', hT'_T, hT_T', hflat⟩ := exists_concise_restriction T hTzero
      have hval_eq : Fspec.toFun T' = Fspec.toFun T := by
        have hle₁ := Fspec.mono T' T hT'_T
        have hle₂ := Fspec.mono T T' hT_T'
        exact le_antisymm hle₁ hle₂
      have hdim_le_N : ∀ j, (d' j : ℕ) ≤ N := by
        intro j
        have hdim_eq : ((d' j : ℕ) : ℝ) = (flatRank T' {j} : ℝ) := by
          exact_mod_cast hflat j
        have hpow : ((d' j : ℕ) : ℝ) ^ c ≤ M := by
          calc
            ((d' j : ℕ) : ℝ) ^ c = (flatRank T' {j} : ℝ) ^ c := by rw [hdim_eq]
            _ ≤ Fspec.toFun T' := hpower T' j
            _ = Fspec.toFun T := hval_eq
            _ ≤ M := hxT_le_M
        have hroot :
            ((d' j : ℕ) : ℝ) ≤ M ^ ((1 : ℝ) / c) :=
          le_rpow_one_div_of_rpow_le (by positivity) hcpos hpow
        have hleB : ((d' j : ℕ) : ℝ) ≤ B :=
          hroot.trans (le_max_right _ _)
        exact_mod_cast hleB.trans (Nat.le_ceil B)
      set a : Fin k → Fin N :=
        fun j => ⟨(d' j : ℕ) - 1, by
          have hdpos : 1 ≤ (d' j : ℕ) := (d' j).2
          have hle := hdim_le_N j
          omega⟩ with ha_def
      have hfmt :
          (fun j => (⟨(a j).val + 1, Nat.succ_pos _⟩ : ℕ+)) = d' := by
        funext j
        apply PNat.coe_injective
        have hdpos : 1 ≤ (d' j : ℕ) := (d' j).2
        simp [a, ha_def]
        omega
      refine ⟨a, ?_⟩
      rw [hfmt]
      exact ⟨T', by simpa [hxT] using hval_eq⟩
  have hfinite_union_closed :
      ∀ N : ℕ,
        IsClosed
          (⋃ a : Fin k → Fin N,
            Set.range (fun T : KTensor ℂ
              (fun j => (⟨(a j).val + 1, Nat.succ_pos _⟩ : ℕ+)) =>
              Fspec.toFun T)) := by
    intro N
    apply isClosed_iUnion_of_finite
    intro a
    exact Fspec_range_per_format_closed
      (fun j => (⟨(a j).val + 1, Nat.succ_pos _⟩ : ℕ+)) Fspec
  rw [← isSeqClosed_iff_isClosed]
  intro x r hxS hxlim
  have hx_bdd : BddAbove (Set.range x) := hxlim.bddAbove_range
  obtain ⟨M, hM⟩ := hx_bdd
  obtain ⟨N, _hNpos, hsubN⟩ := hbounded_format_reduction M
  have hxN :
      ∀ n, x n ∈
        ⋃ a : Fin k → Fin N,
          Set.range (fun T : KTensor ℂ
            (fun j => (⟨(a j).val + 1, Nat.succ_pos _⟩ : ℕ+)) =>
            Fspec.toFun T) := by
    intro n
    exact hsubN ⟨by simpa [S] using hxS n, hM ⟨n, rfl⟩⟩
  have hrN :
      r ∈
        ⋃ a : Fin k → Fin N,
          Set.range (fun T : KTensor ℂ
            (fun j => (⟨(a j).val + 1, Nat.succ_pos _⟩ : ℕ+)) =>
            Fspec.toFun T) :=
    (hfinite_union_closed N).mem_of_tendsto hxlim (Filter.Eventually.of_forall hxN)
  simp only [Set.mem_iUnion, Set.mem_range] at hrN ⊢
  rcases hrN with ⟨a, T, hT⟩
  exact ⟨fun j => (⟨(a j).val + 1, Nat.succ_pos _⟩ : ℕ+), T, hT⟩

private lemma Fspec_pair_two_ge_one {k : ℕ} (Fspec : SpectralPoint k ℂ)
    (i j : Fin k) (hij : i ≠ j) :
    (1 : ℝ) ≤ Fspec.toFun (unitPairTensor (F := ℂ) 2 i j hij) := by
  have hmono := Fspec.mono
    (unitPairTensor (F := ℂ) (k := k) 1 i j hij)
    (unitPairTensor (F := ℂ) (k := k) 2 i j hij)
    (unitPairTensor_restricts_of_le (F := ℂ) i j hij (by norm_num))
  simpa [Fspec.unitPair_one i j hij] using hmono

/-- Global Euclidean closedness of all values of a spectral point.

This is the paper's Corollary 4.6 argument (tex:1250-1260).  The proof is by
induction on `k`.  For `k = 2` it reduces to matrix rank.  For `k > 2`, either
all pair units satisfy `F(⟨2⟩_{i,j}) > 1`, in which case the Corollary 3.3
growth bound forces any convergent value sequence to live in a finite union of
fixed formats and `Fspec_range_per_format_closed` closes the finite union; or
some pair unit has value `1`, in which case Lemma 3.8 (`spec_descend`,
tex:1038-1045) descends to a spectral point in order `k - 1` and the induction
hypothesis applies. -/
lemma asympSpectrum_values_euclidean_closed_core {k : ℕ} (hk : 2 ≤ k)
    (Fspec : SpectralPoint k ℂ) :
    IsClosed (⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor ℂ d => Fspec.toFun T)) := by
  classical
  revert hk Fspec
  refine Nat.strong_induction_on k ?_
  intro k ih hk Fspec
  by_cases hk3 : 3 ≤ k
  · by_cases hpair : ∃ (i j : Fin k) (hij : i ≠ j),
        Fspec.toFun (unitPairTensor (F := ℂ) 2 i j hij) = 1
    · refine asympSpectrum_values_euclidean_closed_pair_eq_one hk3 Fspec hpair ?_
      intro Fspec'
      exact ih (k - 1) (by omega) (by omega) Fspec'
    · refine asympSpectrum_values_euclidean_closed_all_pairs_gt hk3 Fspec ?_
      intro i j hij
      have hne : Fspec.toFun (unitPairTensor (F := ℂ) 2 i j hij) ≠ 1 := by
        intro h
        exact hpair ⟨i, j, hij, h⟩
      exact lt_of_le_of_ne (Fspec_pair_two_ge_one Fspec i j hij) hne.symm
  · exact asympSpectrum_values_euclidean_closed_order_two hk hk3 Fspec

/-- **Corollary 4.6** (tex:1250-1260, `\label{cor:spec-eucl-closed}`).

For any `F ∈ Δ(ℂ, k)` (with `k ≥ 2`), the set
`⋃ d : Fin k → ℕ+, {F(T) : T ∈ ℂ^{d_1} ⊗ ⋯ ⊗ ℂ^{d_k}}` is Euclidean-closed in ℝ. -/
theorem asympSpectrum_values_euclidean_closed {k : ℕ} (hk : 2 ≤ k)
    (Fspec : SpectralPoint k ℂ) :
    IsClosed (⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor ℂ d => Fspec.toFun T)) := by
  exact asympSpectrum_values_euclidean_closed_core hk Fspec

end Semicontinuity
