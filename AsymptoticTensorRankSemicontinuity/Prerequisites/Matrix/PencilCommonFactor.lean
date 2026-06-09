/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.Matrix.RankOnePencil

/-!
# Rectangular Rank-One Common Factor Lemma

This file contains the declarations from the underlying matrix-theoretic
development that this repository uses.
-/

namespace Matrix

open Matrix

variable {K : Type*} [Field K]

/-- Strong rank-one classification (rectangular). Same content as
    `common_factor_strong_of_rank_le_one` in `AtkinsonR1.lean`, but for
    `Mat(m, n, K)` with `m` and `n` possibly distinct. -/
lemma common_factor_strong_of_rank_le_one_rect
    {m n : ℕ} (V : Submodule K (Matrix (Fin m) (Fin n) K))
    (hV : ∀ M ∈ V, M.rank ≤ 1) :
    (∀ M ∈ V, M = 0) ∨
    (∃ uA : Fin m → K, uA ≠ 0 ∧ ∀ M ∈ V,
        ∃ u : Fin m → K, ∃ v : Fin n → K,
          M = vecMulVec u v ∧ u ∈ Submodule.span K {uA}) ∨
    (∃ vA : Fin n → K, vA ≠ 0 ∧ ∀ M ∈ V,
        ∃ u : Fin m → K, ∃ v : Fin n → K,
          M = vecMulVec u v ∧ v ∈ Submodule.span K {vA}) := by
  classical
  by_cases hV_zero : ∀ M ∈ V, M = 0
  · exact Or.inl hV_zero
  push_neg at hV_zero
  obtain ⟨A, hA_mem, hA_ne⟩ := hV_zero
  obtain ⟨uA, vA, hA_eq⟩ := exists_vecMulVec_of_rank_le_one (hV A hA_mem)
  have hA_eq' : vecMulVec uA vA ≠ 0 := hA_eq ▸ hA_ne
  have huA : uA ≠ 0 := fun hu => hA_eq' (by
    rw [hu]; ext i j; simp [Matrix.vecMulVec_apply])
  have hvA : vA ≠ 0 := fun hv => hA_eq' (by
    rw [hv]; ext i j; simp [Matrix.vecMulVec_apply])
  by_cases h_all_v : ∀ B ∈ V, ∀ uB : Fin m → K, ∀ vB : Fin n → K,
      B = vecMulVec uB vB → uB ≠ 0 → vB ≠ 0 → uB ∈ Submodule.span K {uA}
  · right; left
    refine ⟨uA, huA, fun M hM => ?_⟩
    obtain ⟨u, v, hM_eq⟩ := exists_vecMulVec_of_rank_le_one (hV M hM)
    by_cases hM_zero : M = 0
    · refine ⟨0, 0, ?_, ?_⟩
      · rw [hM_zero]; ext i j; simp [Matrix.vecMulVec_apply]
      · exact Submodule.zero_mem _
    · have hM_eq' : vecMulVec u v ≠ 0 := hM_eq ▸ hM_zero
      have hu_ne : u ≠ 0 := fun h => hM_eq' (by
        rw [h]; ext i j; simp [Matrix.vecMulVec_apply])
      have hv_ne : v ≠ 0 := fun h => hM_eq' (by
        rw [h]; ext i j; simp [Matrix.vecMulVec_apply])
      exact ⟨u, v, hM_eq, h_all_v M hM u v hM_eq hu_ne hv_ne⟩
  · push_neg at h_all_v
    obtain ⟨B, hB_mem, uB, vB, hB_eq, huB, hvB, h_uB_nin⟩ := h_all_v
    right; right
    refine ⟨vA, hvA, fun M hM => ?_⟩
    obtain ⟨u, v, hM_eq⟩ := exists_vecMulVec_of_rank_le_one (hV M hM)
    by_cases hM_zero : M = 0
    · refine ⟨0, 0, ?_, ?_⟩
      · rw [hM_zero]; ext i j; simp [Matrix.vecMulVec_apply]
      · exact Submodule.zero_mem _
    · have hM_eq' : vecMulVec u v ≠ 0 := hM_eq ▸ hM_zero
      have hu_ne : u ≠ 0 := fun h => hM_eq' (by
        rw [h]; ext i j; simp [Matrix.vecMulVec_apply])
      have hv_ne : v ≠ 0 := fun h => hM_eq' (by
        rw [h]; ext i j; simp [Matrix.vecMulVec_apply])
      refine ⟨u, v, hM_eq, ?_⟩
      by_contra h_v_nin
      have h_AB_rank : (vecMulVec uA vA + vecMulVec uB vB).rank ≤ 1 := by
        have h_eq : vecMulVec uA vA + vecMulVec uB vB = A + B := by
          rw [hA_eq, hB_eq]
        rw [h_eq]; exact hV _ (Submodule.add_mem _ hA_mem hB_mem)
      have h_vB_in : vB ∈ Submodule.span K {vA} := by
        rcases rank_one_sum_pair huA hvA h_AB_rank with h1 | h2
        · exact absurd h1 h_uB_nin
        · exact h2
      obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.mp h_vB_in
      have hβ_ne : β ≠ 0 := by
        intro hβ0
        apply hvB; rw [← hβ, hβ0, zero_smul]
      have hB_alt : B = vecMulVec (β • uB) vA := by
        rw [hB_eq, ← hβ]
        ext i j; simp [Matrix.vecMulVec_apply, mul_comm, mul_left_comm]
      have hβuB : β • uB ≠ 0 := by simp [hβ_ne, huB]
      have h_BM_rank : (vecMulVec (β • uB) vA + vecMulVec u v).rank ≤ 1 := by
        have h_eq : vecMulVec (β • uB) vA + vecMulVec u v = B + M := by
          rw [← hB_alt, hM_eq]
        rw [h_eq]; exact hV _ (Submodule.add_mem _ hB_mem hM)
      rcases rank_one_sum_pair hβuB hvA h_BM_rank with h_u_in | h_v_in
      · have h_AM_rank : (vecMulVec uA vA + vecMulVec u v).rank ≤ 1 := by
          have h_eq : vecMulVec uA vA + vecMulVec u v = A + M := by
            rw [hA_eq, hM_eq]
          rw [h_eq]; exact hV _ (Submodule.add_mem _ hA_mem hM)
        rcases rank_one_sum_pair huA hvA h_AM_rank with h_u_inA | h_v_inA
        · obtain ⟨γ, hγ⟩ := Submodule.mem_span_singleton.mp h_u_inA
          have hγ_ne : γ ≠ 0 := by
            intro hγ0; apply hu_ne; rw [← hγ, hγ0, zero_smul]
          obtain ⟨δ, hδ⟩ := Submodule.mem_span_singleton.mp h_u_in
          have hδβ : (γ : K) • uA = (δ * β) • uB := by
            rw [SemigroupAction.mul_smul, hδ, hγ]
          apply h_uB_nin
          have hδβ_ne : δ * β ≠ 0 := by
            intro hzero
            rw [hzero, zero_smul] at hδβ
            exact huA ((smul_eq_zero.mp hδβ).resolve_left hγ_ne)
          rw [Submodule.mem_span_singleton]
          refine ⟨(δ * β)⁻¹ * γ, ?_⟩
          rw [SemigroupAction.mul_smul, hδβ, ← SemigroupAction.mul_smul,
            inv_mul_cancel₀ hδβ_ne, one_smul]
        · exact h_v_nin h_v_inA
      · exact h_v_nin h_v_in

end Matrix
