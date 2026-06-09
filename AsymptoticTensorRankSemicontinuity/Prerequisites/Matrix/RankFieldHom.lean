/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.Matrix.SubmatrixDet
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank

set_option linter.style.longLine false

/-!
# Matrix Rank Invariance Under Injective Field Homomorphisms

This file contains the declarations from the underlying matrix-theoretic
development that this repository uses.
-/

namespace Matrix

/-- **Matrix rank invariance under injective ring hom of fields**.

For an injective ring hom `f : K₁ →+* K₂` of fields, `(M.map f).rank = M.rank`. -/
theorem rank_map_of_injective_fieldHom
    {K₁ K₂ : Type*} [Field K₁] [Field K₂]
    {m₀ n₀ : ℕ} (f : K₁ →+* K₂) (hf : Function.Injective f)
    (M : Matrix (Fin m₀) (Fin n₀) K₁) :
    (M.map f).rank = M.rank := by
  classical
  -- Direction M.rank ≤ (M.map f).rank.
  have h1 : M.rank ≤ (M.map f).rank := by
    by_cases hr0 : M.rank = 0
    · rw [hr0]; exact Nat.zero_le _
    have hge : (M.rank - 1) + 1 ≤ M.rank := by omega
    obtain ⟨σ, τ, hdet⟩ :=
      Matrix.exists_submatrix_det_ne_zero_of_le_rank M (M.rank - 1) hge
    have h_submatrix_map :
        (M.map f).submatrix σ τ = (M.submatrix σ τ).map f := by
      ext i j; simp [Matrix.map_apply, Matrix.submatrix]
    have h_det_ne : ((M.map f).submatrix σ τ).det ≠ 0 := by
      rw [h_submatrix_map]
      have h_det_eq : ((M.submatrix σ τ).map f).det = f ((M.submatrix σ τ).det) := by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      rw [h_det_eq]
      intro h0; exact hdet (hf (by rw [h0, map_zero]))
    have h_sub_li : LinearIndependent K₂ ((M.map f).submatrix σ τ).row :=
      Matrix.linearIndependent_rows_of_det_ne_zero h_det_ne
    have h_full_li : LinearIndependent K₂ (fun i => (M.map f).row (σ i)) := by
      have h_restr : ((M.map f).submatrix σ τ).row =
          (fun v : Fin n₀ → K₂ => v ∘ τ) ∘ (fun i => (M.map f).row (σ i)) := by
        ext i j; simp [Matrix.submatrix, Matrix.row, Function.comp]
      rw [h_restr] at h_sub_li
      exact LinearIndependent.of_comp (LinearMap.funLeft K₂ K₂ τ) h_sub_li
    have h_sub_rank :
        ((M.map f).submatrix σ (Equiv.refl _)).rank = M.rank := by
      have h_row_eq : ((M.map f).submatrix σ (Equiv.refl _)).row =
          fun i => (M.map f).row (σ i) := by
        ext i j; simp [Matrix.submatrix, Matrix.row, Equiv.refl]
      rw [← h_row_eq] at h_full_li
      have := h_full_li.rank_matrix
      rw [this, Fintype.card_fin]
      omega
    have h_le : ((M.map f).submatrix σ (Equiv.refl _)).rank ≤ (M.map f).rank :=
      Matrix.rank_submatrix_le σ (Equiv.refl _) (M.map f)
    omega
  -- Reverse direction: (M.map f).rank ≤ M.rank.
  have h2 : (M.map f).rank ≤ M.rank := by
    by_cases hr0 : (M.map f).rank = 0
    · rw [hr0]; exact Nat.zero_le _
    have hge : ((M.map f).rank - 1) + 1 ≤ (M.map f).rank := by omega
    obtain ⟨σ, τ, hdet⟩ :=
      Matrix.exists_submatrix_det_ne_zero_of_le_rank (M.map f)
        ((M.map f).rank - 1) hge
    have h_submatrix_map :
        (M.map f).submatrix σ τ = (M.submatrix σ τ).map f := by
      ext i j; simp [Matrix.map_apply, Matrix.submatrix]
    rw [h_submatrix_map] at hdet
    have h_det_eq : ((M.submatrix σ τ).map f).det = f ((M.submatrix σ τ).det) := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h_det_eq] at hdet
    -- f(det M_sub) ≠ 0 ⇒ det M_sub ≠ 0 (f maps zero to zero).
    have h_base_det_ne : (M.submatrix σ τ).det ≠ 0 :=
      fun h0 => hdet (by rw [h0]; exact map_zero _)
    have h_sub_li : LinearIndependent K₁ (M.submatrix σ τ).row :=
      Matrix.linearIndependent_rows_of_det_ne_zero h_base_det_ne
    have h_full_li : LinearIndependent K₁ (fun i => M.row (σ i)) := by
      have h_restr : (M.submatrix σ τ).row =
          (fun v : Fin n₀ → K₁ => v ∘ τ) ∘ (fun i => M.row (σ i)) := by
        ext i j; simp [Matrix.submatrix, Matrix.row, Function.comp]
      rw [h_restr] at h_sub_li
      exact LinearIndependent.of_comp (LinearMap.funLeft K₁ K₁ τ) h_sub_li
    have h_sub_rank :
        (M.submatrix σ (Equiv.refl _)).rank = (M.map f).rank := by
      have h_row_eq : (M.submatrix σ (Equiv.refl _)).row =
          fun i => M.row (σ i) := by
        ext i j; simp [Matrix.submatrix, Matrix.row, Equiv.refl]
      rw [← h_row_eq] at h_full_li
      have := h_full_li.rank_matrix
      rw [this, Fintype.card_fin]
      omega
    have h_le : (M.submatrix σ (Equiv.refl _)).rank ≤ M.rank :=
      Matrix.rank_submatrix_le σ (Equiv.refl _) M
    omega
  exact le_antisymm h2 h1

end Matrix
