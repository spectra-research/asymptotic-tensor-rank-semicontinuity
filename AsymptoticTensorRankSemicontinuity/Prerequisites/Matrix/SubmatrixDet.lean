/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Nonzero minors from rank lower bounds

Nonzero minors from rank lower bounds, and rank monotonicity under taking
submatrices.
-/

open Matrix Module

namespace Matrix

/-- If the rank of a matrix over a field is at least s+1, then there exist embeddings
    f : Fin (s+1) ↪ m and g : Fin (s+1) ↪ n such that the corresponding
    (s+1)×(s+1) submatrix has nonzero determinant.

    This is the matrix-theoretic content: rank >= s+1 implies some (s+1)-minor is nonzero.
    The proof extracts linearly independent rows from the row space (using the
    fact that a maximal linearly independent subset of a spanning set has cardinality
    equal to the dimension), then extracts linearly independent columns similarly,
    giving an (s+1)x(s+1) square submatrix with independent rows, hence nonzero det. -/
theorem exists_submatrix_det_ne_zero_of_le_rank {K : Type*} [Field K]
    {m n : Type*} [Finite m] [Fintype n] (M : Matrix m n K) (s : ℕ)
    (hs : s + 1 ≤ M.rank) :
    ∃ (f : Fin (s + 1) ↪ m) (g : Fin (s + 1) ↪ n),
      (M.submatrix f g).det ≠ 0 := by
  haveI := Fintype.ofFinite m
  -- Step 1: Extract s+1 linearly independent rows
  have hrank_row : s + 1 ≤ finrank K (Submodule.span K (Set.range M.row)) := by
    rwa [← M.rank_eq_finrank_span_row]
  obtain ⟨b, hb_sub, hb_span, hb_li⟩ := exists_linearIndependent K (Set.range M.row)
  have hb_finite : b.Finite := hb_li.setFinite
  haveI : Fintype b := hb_finite.fintype
  have hb_card : Fintype.card b = finrank K (Submodule.span K (Set.range M.row)) := by
    have h1 := linearIndependent_iff_card_eq_finrank_span.mp hb_li
    rw [Set.finrank, Subtype.range_coe_subtype, Set.setOf_mem_eq, hb_span] at h1
    exact h1
  have hb_ge : s + 1 ≤ Fintype.card b := hb_card ▸ hrank_row
  obtain ⟨ι_emb⟩ : Nonempty (Fin (s + 1) ↪ b) :=
    Function.Embedding.nonempty_of_card_le (by rwa [Fintype.card_fin])
  have hb_mem : ∀ (x : b), ↑x ∈ Set.range M.row := fun x => hb_sub x.property
  choose row_idx hrow_idx using fun x : b => hb_mem x
  let f_fun : Fin (s + 1) → m := fun i => row_idx (ι_emb i)
  have hf_li : LinearIndependent K (fun i : Fin (s + 1) => M.row (f_fun i)) := by
    have : (fun i : Fin (s + 1) => M.row (f_fun i)) =
        (fun x : b => (x : n → K)) ∘ ι_emb := by
      ext i
      exact congrFun (hrow_idx (ι_emb i)) _
    rw [this]
    exact hb_li.comp (↑ι_emb) ι_emb.injective
  have hf_inj : Function.Injective f_fun := by
    intro i j hij
    have : M.row (f_fun i) = M.row (f_fun j) := by rw [hij]
    exact hf_li.injective this
  let f : Fin (s + 1) ↪ m := ⟨f_fun, hf_inj⟩
  -- Step 2: The submatrix N = M.submatrix f id has rank s+1
  set N := M.submatrix f (Equiv.refl n) with hN_def
  have hN_li : LinearIndependent K N.row := by
    have : N.row = (fun i : Fin (s + 1) => M.row (f i)) := by
      ext i j
      simp [N, Matrix.row, Matrix.submatrix]
    rw [this]
    exact hf_li
  have hN_rank : N.rank = s + 1 := by
    rw [hN_li.rank_matrix, Fintype.card_fin]
  -- Step 3: Extract s+1 linearly independent columns from N
  have hNt_rank : Nᵀ.rank = s + 1 := by rw [rank_transpose]; exact hN_rank
  have hNt_row_rank : s + 1 ≤ finrank K (Submodule.span K (Set.range Nᵀ.row)) := by
    rw [← Nᵀ.rank_eq_finrank_span_row, hNt_rank]
  obtain ⟨c, hc_sub, hc_span, hc_li⟩ := exists_linearIndependent K (Set.range Nᵀ.row)
  have hc_finite : c.Finite := hc_li.setFinite
  haveI : Fintype c := hc_finite.fintype
  have hc_card : Fintype.card c = finrank K (Submodule.span K (Set.range Nᵀ.row)) := by
    have h1 := linearIndependent_iff_card_eq_finrank_span.mp hc_li
    rw [Set.finrank, Subtype.range_coe_subtype, Set.setOf_mem_eq, hc_span] at h1
    exact h1
  have hc_ge : s + 1 ≤ Fintype.card c := hc_card ▸ hNt_row_rank
  obtain ⟨κ_emb⟩ : Nonempty (Fin (s + 1) ↪ c) :=
    Function.Embedding.nonempty_of_card_le (by rwa [Fintype.card_fin])
  have hc_mem : ∀ (x : c), ↑x ∈ Set.range Nᵀ.row := fun x => hc_sub x.property
  choose col_idx hcol_idx using fun x : c => hc_mem x
  let g_fun : Fin (s + 1) → n := fun j => col_idx (κ_emb j)
  have hg_li : LinearIndependent K (fun j : Fin (s + 1) => Nᵀ.row (g_fun j)) := by
    have : (fun j : Fin (s + 1) => Nᵀ.row (g_fun j)) =
        (fun x : c => (x : Fin (s + 1) → K)) ∘ κ_emb := by
      ext j
      exact congrFun (hcol_idx (κ_emb j)) _
    rw [this]
    exact hc_li.comp (↑κ_emb) κ_emb.injective
  have hg_inj : Function.Injective g_fun := by
    intro i j hij
    have : Nᵀ.row (g_fun i) = Nᵀ.row (g_fun j) := by rw [hij]
    exact hg_li.injective this
  let g : Fin (s + 1) ↪ n := ⟨g_fun, hg_inj⟩
  -- Step 4: The (s+1)×(s+1) submatrix M.submatrix f g has linearly independent rows
  refine ⟨f, g, ?_⟩
  have hdet_li : LinearIndependent K (M.submatrix f g)ᵀ.row := by
    have : (M.submatrix f g)ᵀ.row = (fun j => Nᵀ.row (g j)) := by
      ext j i
      simp [Matrix.row, Matrix.submatrix, Matrix.transpose, N]
    rw [this]
    exact hg_li
  obtain ⟨u, hu⟩ := linearIndependent_rows_iff_isUnit.mp hdet_li
  have hdet_t_ne : (M.submatrix f g)ᵀ.det ≠ 0 :=
    det_ne_zero_of_right_inverse (u.mul_inv_of_eq hu)
  rwa [det_transpose] at hdet_t_ne

/-- Selecting columns does not increase the rank. -/
private theorem rank_submatrix_id_le {K : Type*} [Field K] {m n n' : Type*}
    [Finite m] [Fintype n] [Fintype n'] (M : Matrix m n K) (g : n' → n) :
    (M.submatrix id g).rank ≤ M.rank := by
  haveI := Fintype.ofFinite m
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  apply Submodule.finrank_mono
  rw [Submodule.span_le]
  rintro _ ⟨col, rfl⟩
  exact Submodule.subset_span ⟨g col, by ext r; simp [Matrix.submatrix]⟩

/-- The rank of any submatrix (rows and columns selected by arbitrary
functions) is at most the rank of the matrix. -/
theorem rank_submatrix_le' {K : Type*} [Field K] {m n m' n' : Type*}
    [Finite m] [Fintype n] [Finite m'] [Fintype n']
    (M : Matrix m n K) (f : m' → m) (g : n' → n) :
    (M.submatrix f g).rank ≤ M.rank := by
  haveI := Fintype.ofFinite m
  haveI := Fintype.ofFinite m'
  have hrows : ((M.submatrix f id).rank : ℕ) ≤ M.rank := by
    rw [← Matrix.rank_transpose (M.submatrix f id), ← Matrix.rank_transpose M]
    have : (M.submatrix f id)ᵀ = Mᵀ.submatrix id f := rfl
    rw [this]
    exact rank_submatrix_id_le Mᵀ f
  calc (M.submatrix f g).rank
      = ((M.submatrix f id).submatrix id g).rank := by
        rw [Matrix.submatrix_submatrix]; rfl
    _ ≤ (M.submatrix f id).rank := rank_submatrix_id_le _ g
    _ ≤ M.rank := hrows

end Matrix
