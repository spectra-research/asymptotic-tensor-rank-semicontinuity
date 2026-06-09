/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Rank-One Matrix Lemmas

This file contains the declarations from the underlying matrix-theoretic
development that this repository uses.
-/

namespace Matrix

open Matrix

variable {K : Type*} [Field K]
variable {m n : ℕ}

/-! ## Decomposition of rank-≤-1 matrices -/

/-- A matrix of rank at most one is an outer product `u * vᵀ`. -/
lemma exists_vecMulVec_of_rank_le_one
    {X : Matrix (Fin m) (Fin n) K} (h : X.rank ≤ 1) :
    ∃ u : Fin m → K, ∃ v : Fin n → K, X = vecMulVec u v := by
  have hfr : Module.finrank K ↥(Submodule.span K (Set.range X.col)) ≤ 1 := by
    rw [← Matrix.rank_eq_finrank_span_cols]; exact h
  haveI hP : (Submodule.span K (Set.range X.col)).IsPrincipal :=
    (Submodule.finrank_le_one_iff_isPrincipal _).mp hfr
  classical
  set u₀ : Fin m → K :=
    Submodule.IsPrincipal.generator (Submodule.span K (Set.range X.col))
  have hspan : Submodule.span K (Set.range X.col) = K ∙ u₀ :=
    (Submodule.IsPrincipal.span_singleton_generator _).symm
  have hcol_choose : ∀ j : Fin n, ∃ c : K, c • u₀ = X.col j := by
    intro j
    have hmem : X.col j ∈ K ∙ u₀ := by
      rw [← hspan]; exact Submodule.subset_span (Set.mem_range_self j)
    exact Submodule.mem_span_singleton.mp hmem
  let v : Fin n → K := fun j => (hcol_choose j).choose
  have hv : ∀ j, v j • u₀ = X.col j := fun j => (hcol_choose j).choose_spec
  refine ⟨u₀, v, ?_⟩
  ext i j
  have hij : (v j • u₀) i = X.col j i := congrFun (hv j) i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at hij
  simp [Matrix.vecMulVec_apply, ← hij, mul_comm]

/-! ## Pair lemma: linear dependence from vanishing minors -/

/-- If every 2×2 "minor" of the pair `(v, v')` vanishes and `v ≠ 0`, then
    `v'` is a scalar multiple of `v`. -/
lemma exists_smul_eq_of_minors_zero
    {v v' : Fin n → K} (hv : v ≠ 0)
    (h : ∀ j₁ j₂ : Fin n, v j₁ * v' j₂ - v j₂ * v' j₁ = 0) :
    ∃ c : K, v' = c • v := by
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, v j₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hv (funext hall)
  refine ⟨v' j₀ / v j₀, funext fun j => ?_⟩
  have hkey : v j * v' j₀ = v j₀ * v' j := by linear_combination h j j₀
  rw [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination -hkey

/-- The "Cauchy-Binet" identity: the 2×2 minor of a sum of two outer products
    factors as a product of two 2×2 minors. -/
lemma vecMulVec_add_vecMulVec_minor
    (u u' : Fin m → K) (v v' : Fin n → K)
    (i₁ i₂ : Fin m) (j₁ j₂ : Fin n) :
    (vecMulVec u v + vecMulVec u' v') i₁ j₁ *
        (vecMulVec u v + vecMulVec u' v') i₂ j₂ -
      (vecMulVec u v + vecMulVec u' v') i₁ j₂ *
        (vecMulVec u v + vecMulVec u' v') i₂ j₁ =
    (u i₁ * u' i₂ - u i₂ * u' i₁) *
      (v j₁ * v' j₂ - v j₂ * v' j₁) := by
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply]
  ring

/-- Every 2×2 minor of a rank-≤-1 matrix vanishes. -/
lemma minor_zero_of_rank_le_one
    {M : Matrix (Fin m) (Fin n) K} (h : M.rank ≤ 1)
    (i₁ i₂ : Fin m) (j₁ j₂ : Fin n) :
    M i₁ j₁ * M i₂ j₂ - M i₁ j₂ * M i₂ j₁ = 0 := by
  have hfr : Module.finrank K ↥(Submodule.span K (Set.range M.col)) ≤ 1 := by
    rw [← Matrix.rank_eq_finrank_span_cols]; exact h
  haveI hP : (Submodule.span K (Set.range M.col)).IsPrincipal :=
    (Submodule.finrank_le_one_iff_isPrincipal _).mp hfr
  set g : Fin m → K :=
    Submodule.IsPrincipal.generator (Submodule.span K (Set.range M.col))
  have hgsp : Submodule.span K (Set.range M.col) = K ∙ g :=
    (Submodule.IsPrincipal.span_singleton_generator _).symm
  have h1 : M.col j₁ ∈ K ∙ g := by
    rw [← hgsp]; exact Submodule.subset_span (Set.mem_range_self _)
  have h2 : M.col j₂ ∈ K ∙ g := by
    rw [← hgsp]; exact Submodule.subset_span (Set.mem_range_self _)
  obtain ⟨c₁, hc₁⟩ := Submodule.mem_span_singleton.mp h1
  obtain ⟨c₂, hc₂⟩ := Submodule.mem_span_singleton.mp h2
  have e1 : ∀ i, M i j₁ = c₁ * g i := fun i => by
    have := congrFun hc₁ i
    simpa [Pi.smul_apply, smul_eq_mul, Matrix.col_apply] using this.symm
  have e2 : ∀ i, M i j₂ = c₂ * g i := fun i => by
    have := congrFun hc₂ i
    simpa [Pi.smul_apply, smul_eq_mul, Matrix.col_apply] using this.symm
  rw [e1 i₁, e1 i₂, e2 i₁, e2 i₂]; ring

/-! ## Sub-claim: rank-1 sum -/

/-- **Sub-claim.** If `vecMulVec u v + vecMulVec u' v'` has rank at most one,
    and `u`, `v` are nonzero, then `u'` is a scalar multiple of `u` or `v'` is
    a scalar multiple of `v`. -/
lemma rank_one_sum_pair
    {u u' : Fin m → K} {v v' : Fin n → K}
    (hu : u ≠ 0) (hv : v ≠ 0)
    (h : (vecMulVec u v + vecMulVec u' v').rank ≤ 1) :
    u' ∈ K ∙ u ∨ v' ∈ K ∙ v := by
  by_cases hu_minors : ∀ i₁ i₂ : Fin m, u i₁ * u' i₂ - u i₂ * u' i₁ = 0
  · left
    obtain ⟨c, hc⟩ := exists_smul_eq_of_minors_zero hu hu_minors
    rw [hc]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self u)
  · right
    push_neg at hu_minors
    obtain ⟨i₁, i₂, hne⟩ := hu_minors
    have hv_minors : ∀ j₁ j₂ : Fin n, v j₁ * v' j₂ - v j₂ * v' j₁ = 0 := by
      intro j₁ j₂
      have hzero := minor_zero_of_rank_le_one h i₁ i₂ j₁ j₂
      rw [vecMulVec_add_vecMulVec_minor] at hzero
      rcases mul_eq_zero.mp hzero with h1 | h2
      · exact absurd h1 hne
      · exact h2
    obtain ⟨c, hc⟩ := exists_smul_eq_of_minors_zero hv hv_minors
    rw [hc]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v)

/-! ## Pivot lemma: orthogonal vector exists in dimension ≥ 2 -/

/-- For any nonzero `u : Fin n → K` with `n ≥ 2`, there is a nonzero
    `w : Fin n → K` with `dotProduct w u = 0`. -/
lemma exists_dotProduct_eq_zero
    {u : Fin n → K} (hu : u ≠ 0) (hn : 2 ≤ n) :
    ∃ w : Fin n → K, w ≠ 0 ∧ dotProduct w u = 0 := by
  classical
  -- Find a coordinate where `u` is nonzero.
  obtain ⟨j₀, hj₀⟩ : ∃ j, u j ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hu (funext hall)
  -- Find another coordinate distinct from `j₀`.
  obtain ⟨j₁, hj₁⟩ : ∃ j₁ : Fin n, j₁ ≠ j₀ := by
    by_contra hall
    push_neg at hall
    -- All elements of `Fin n` equal `j₀`. Card-2 lower bound prevents this.
    have hcard : Fintype.card (Fin n) ≤ 1 := by
      refine Fintype.card_le_one_iff.mpr ?_
      intro a b
      exact (hall a).trans (hall b).symm
    simp at hcard
    omega
  -- Define `w = u j₀ • e_{j₁} - u j₁ • e_{j₀}` componentwise.
  refine ⟨fun j => if j = j₀ then -(u j₁) else if j = j₁ then u j₀ else 0,
    ?_, ?_⟩
  · -- w ≠ 0: at coordinate j₁ it equals u j₀ ≠ 0.
    intro hw
    have := congrFun hw j₁
    simp only [hj₁, ↓reduceIte, Pi.zero_apply] at this
    exact hj₀ this
  · -- dotProduct: ∑_j w_j u_j = -u_{j₁} u_{j₀} + u_{j₀} u_{j₁} = 0.
    classical
    -- The sum is supported on {j₀, j₁}.
    have hpair : (Finset.univ : Finset (Fin n)) =
        {j₀, j₁} ∪ (Finset.univ \ {j₀, j₁}) := by
      rw [Finset.union_sdiff_of_subset (Finset.subset_univ _)]
    unfold dotProduct
    rw [hpair, Finset.sum_union Finset.disjoint_sdiff]
    have hzero_outside : ∑ j ∈ Finset.univ \ {j₀, j₁},
        (if j = j₀ then -(u j₁) else if j = j₁ then u j₀ else 0) * u j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
        not_or] at hj
      obtain ⟨_, hjne0, hjne1⟩ := hj
      rw [if_neg hjne0, if_neg hjne1]
      ring
    rw [hzero_outside, add_zero]
    -- Now reduce ∑ j ∈ {j₀, j₁} to the two-term sum.
    rw [Finset.sum_insert (by simp [Ne.symm hj₁]), Finset.sum_singleton]
    -- Beta-reduce and apply if-then-else: at j₀ get -(u j₁), at j₁ get u j₀.
    change (if (j₀ : Fin n) = j₀ then -(u j₁) else if j₀ = j₁ then u j₀ else 0)
        * u j₀ +
      (if (j₁ : Fin n) = j₀ then -(u j₁) else if j₁ = j₁ then u j₀ else 0)
        * u j₁ = 0
    rw [if_pos rfl, if_neg hj₁, if_pos rfl]
    ring

end Matrix
