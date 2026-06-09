/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.MaxRankBound
import AsymptoticTensorRankSemicontinuity.TensorSemiring

/-!
# Corollary 3.5, Ingredient 1 — the pair-unit Kronecker restriction

Source: the semicontinuity manuscript,
lines 982–986 (proof of Corollary 3.5).

Verbatim (tex:983-985):
"Let `q_{i,j} = subrank_{i,j}(T)` for every `i,j ∈ [k]` with `i < j`. Then
`T^{⊠(k(k-1)/2)} ≥ ⊠_{i<j} ⟨q_{i,j}⟩_{i,j}`."

Here `⟨q⟩_{i,j}` is the rank-`q` pair-unit (GHZ-type) tensor supported on legs
`i, j` (`unitPairTensor`), `⊠` is the Kronecker product (`kroneckerTensor`), and
`≥` is restriction (`Restricts S T`, read `S ≤ₜ T`, i.e. `S` restricts to `T`).

This file formalizes **ingredient 1** of that proof:

* `subrankPair_unitPair_restricts` — for `i ≠ j` with `0 < subrankPair T i j`, the
  rank-`subrankPair T i j` pair-unit on legs `i, j` restricts to `T`. This is the
  attainment of the `sSup` defining `subrankPair` (tex:836).
* `Restricts.kronFoldl` — iterating `Restricts.kron_congr` along a list of
  leg-wise restrictions gives a restriction of the corresponding left-nested
  Kronecker folds (the engine of "`⊠_p S_p ≤ ⊠_p T`").
* `kronPowNat_eq_foldl` — `kronPowNat T n` is the left-nested Kronecker fold of
  `n` copies of `T` over a base copy of `T` (`(List.replicate n T).foldl (⊠) T`).
* `pairUnitKron_restricts_kronPow` — **the headline**: the Kronecker fold of the
  pair-units `⟨subrankPair T iₚ jₚ⟩_{iₚ,jₚ}` over a nonempty list `p₀ :: ps` of
  distinct, positive-subrank pairs (`N = ps.length + 1` pairs) restricts to
  `kronPowNat T ps.length`, which is the `N`-fold Kronecker power `T^{⊠N}` of the
  paper (recall `kronPowNat T 0 = T`, so `kronPowNat T n` has `n+1` factors). This
  is exactly tex:984-985 once `p₀ :: ps` enumerates the pairs `i < j`
  (`N = k(k-1)/2`).
-/

namespace Semicontinuity

universe u

variable {F : Type u} [Field F]

/-! ## Ingredient 1a — attainment of the `subrankPair` supremum (tex:836).

`subrankPair` is the `sSup` of the set of positive `r` with `⟨r⟩_{i,j} ≤ₜ T`. To
conclude that this supremum is *attained* we need the set to be bounded above.
The bound — a restricting rank-`r` pair-unit forces `r ≤ flatRank T {i}` — is the
private lemma `pairUnit_restricts_le_flatRank` of `MaxRankBound.lean`; we reprove
it here from the public API (`Restricts.flatRank_le`, `flattenMatrix`,
`unitPairTensor`) so it is usable across files. -/

/-- **Pair-unit flattening bound** (tex:836, 880-899; reproof of the private
    `pairUnit_restricts_le_flatRank` of `MaxRankBound.lean`).

For distinct legs `i ≠ j` of any `k`-tensor `T`, a rank-`r` pair-unit `⟨r⟩_{i,j}`
that restricts to `T` forces `r ≤ flatRank T {i}`. The pair-unit's `{i}`-flattening
is the rank-`r` identity, and `flatRank` is monotone under restriction
(`Restricts.flatRank_le`). -/
private lemma pairUnit_restricts_le_flatRank' {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (i j : Fin k) (hij : i ≠ j) {r : ℕ} (hr : 0 < r)
    (hres : Restricts (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) T) :
    r ≤ flatRank T {i} := by
  classical
  -- `flatRank (⟨r⟩_{i,j}) {i} ≤ flatRank T {i}` by restriction-monotonicity.
  have hmono := hres.flatRank_le {i}
  -- The pair-unit's `{i}`-flattening has rank exactly `r`.
  have hrank_eq : flatRank (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) {i} = r := by
    have memi : i ∈ ({i} : Finset (Fin k)) := Finset.mem_singleton_self i
    have memj : j ∉ ({i} : Finset (Fin k)) := by
      rw [Finset.mem_singleton]; exact hij.symm
    have hrowval : ∀ x : { x // x ∈ ({i} : Finset (Fin k)) }, x.val = i :=
      fun x => Finset.mem_singleton.mp x.2
    have hnpf_i : ((naturalPairFormat (⟨r, hr⟩ : ℕ+) i j i : ℕ+) : ℕ) = r := by
      unfold naturalPairFormat; rw [if_pos (Or.inl rfl)]; rfl
    have hnpf_j : ((naturalPairFormat (⟨r, hr⟩ : ℕ+) i j j : ℕ+) : ℕ) = r := by
      unfold naturalPairFormat; rw [if_pos (Or.inr rfl)]; rfl
    let eRow : Fin r ≃ ((x : { x // x ∈ ({i} : Finset (Fin k)) })
        → Fin (naturalPairFormat (⟨r, hr⟩ : ℕ+) i j x.val)) :=
      { toFun := fun m x => Fin.cast (by rw [hrowval x, hnpf_i]) m
        invFun := fun row => Fin.cast (by rw [hnpf_i]) (row ⟨i, memi⟩)
        left_inv := by intro m; simp
        right_inv := by
          intro row; funext x
          obtain ⟨x, hx⟩ := x
          have hxi : x = i := Finset.mem_singleton.mp hx; subst hxi; simp }
    let eCol : Fin r ≃ ((x : { x // x ∉ ({i} : Finset (Fin k)) })
        → Fin (naturalPairFormat (⟨r, hr⟩ : ℕ+) i j x.val)) :=
      { toFun := fun m x =>
          if hxj : x.val = j then Fin.cast (by rw [hxj, hnpf_j]) m
          else ⟨0, by
            have : ((naturalPairFormat (⟨r, hr⟩ : ℕ+) i j x.val : ℕ+) : ℕ) = 1 := by
              unfold naturalPairFormat
              rw [if_neg]
              · rfl
              · rintro (h | h)
                · exact x.2 (by rw [Finset.mem_singleton]; exact h)
                · exact hxj h
            omega⟩
        invFun := fun col => Fin.cast (by rw [hnpf_j]) (col ⟨j, memj⟩)
        left_inv := by intro m; simp
        right_inv := by
          intro col; funext x
          by_cases hxj : x.val = j
          · obtain ⟨x, hx⟩ := x
            simp only at hxj; subst hxj
            simp
          · simp only [dif_neg hxj]
            have hone : ((naturalPairFormat (⟨r, hr⟩ : ℕ+) i j x.val : ℕ+) : ℕ) = 1 := by
              unfold naturalPairFormat
              rw [if_neg]
              · rfl
              · rintro (h | h)
                · exact x.2 (by rw [Finset.mem_singleton]; exact h)
                · exact hxj h
            apply Fin.ext
            have h1 := (col x).isLt
            have h2 : (⟨0, by omega⟩ : Fin (naturalPairFormat (⟨r, hr⟩ : ℕ+) i j x.val)).val = 0 :=
              rfl
            omega }
    have hid : flattenMatrix (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) {i}
        = Matrix.reindex eRow eCol (1 : Matrix (Fin r) (Fin r) F) := by
      ext rowS colS
      rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]
      change (unitPairTensor (F := F) ⟨r, hr⟩ i j hij)
          (fun x => if h : x ∈ ({i} : Finset (Fin k)) then rowS ⟨x, h⟩
            else colS ⟨x, h⟩) = _
      rw [unitPairTensor]
      rw [dif_pos memi, dif_neg memj]
      by_cases heq : eRow.symm rowS = eCol.symm colS
      · rw [if_pos heq]
        have : (rowS ⟨i, memi⟩).val = (colS ⟨j, memj⟩).val := by
          have hr' : (eRow.symm rowS).val = (rowS ⟨i, memi⟩).val := by
            change (Fin.cast (by rw [hnpf_i]) (rowS ⟨i, memi⟩)).val = _; rfl
          have hc' : (eCol.symm colS).val = (colS ⟨j, memj⟩).val := by
            change (Fin.cast (by rw [hnpf_j]) (colS ⟨j, memj⟩)).val = _; rfl
          rw [← hr', ← hc', heq]
        rw [if_pos this]
      · rw [if_neg heq]
        rw [if_neg]
        intro hcontra
        apply heq
        apply Fin.ext
        have hr' : (eRow.symm rowS).val = (rowS ⟨i, memi⟩).val := by
          change (Fin.cast (by rw [hnpf_i]) (rowS ⟨i, memi⟩)).val = _; rfl
        have hc' : (eCol.symm colS).val = (colS ⟨j, memj⟩).val := by
          change (Fin.cast (by rw [hnpf_j]) (colS ⟨j, memj⟩)).val = _; rfl
        rw [hr', hc', hcontra]
    rw [flatRank, hid, Matrix.rank_reindex, Matrix.rank_one, Fintype.card_fin]
  rw [hrank_eq] at hmono
  exact hmono

/-- **`subrankPair` supremum set is bounded above** (tex:836). The set of positive
    `r` with `⟨r⟩_{i,j} ≤ₜ T` is bounded above by `flatRank T {i}`. -/
private lemma subrankPair_bddAbove' {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (i j : Fin k) (hij : i ≠ j) :
    BddAbove { r : ℕ | ∃ hr : 0 < r,
      Restricts (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) T } := by
  refine ⟨flatRank T {i}, ?_⟩
  rintro s ⟨hs, hres⟩
  exact pairUnit_restricts_le_flatRank' T i j hij hs hres

/-- **`subrankPair` attainment** (tex:836).

For distinct legs `i ≠ j` of a `k`-tensor `T`, if `0 < subrankPair T i j` then the
rank-`subrankPair T i j` pair-unit `⟨subrankPair T i j⟩_{i,j}` restricts to `T`.

`subrankPair T i j` is defined as the `sSup` (over `ℕ`) of the set of positive `r`
with `⟨r⟩_{i,j} ≤ₜ T`. That set is bounded above (`subrankPair_bddAbove'`); if the
supremum is positive then the set is nonempty, so `Nat.sSup_mem` puts the supremum
itself in the set, which is precisely the desired restriction. -/
lemma subrankPair_unitPair_restricts {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (i j : Fin k) (hij : i ≠ j)
    (hpos : 0 < subrankPair T i j) :
    Restricts
      (unitPairTensor (F := F) ⟨subrankPair T i j, hpos⟩ i j hij) T := by
  classical
  set s : Set ℕ := { r : ℕ | ∃ hr : 0 < r,
      Restricts (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) T } with hs_def
  have hval : subrankPair T i j = sSup s := by
    unfold subrankPair
    rw [dif_neg hij]
  have hne : s.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    rw [hval, hempty] at hpos
    simp at hpos
  have hmem : sSup s ∈ s :=
    Nat.sSup_mem hne (subrankPair_bddAbove' T i j hij)
  rw [← hval] at hmem
  obtain ⟨hr, hres⟩ := hmem
  exact hres

/-! ## Ingredient 1b — iterated Kronecker product as a left-nested fold.

We package tensors heterogeneously (each carries its own format) using the
existing total type `TT F k := Σ d, KTensor F d` (from `TensorSemiring.lean`). -/

/-- Kronecker product on the bundled total type `TT F k`. -/
noncomputable def TT.kron {k : ℕ} (S T : TT F k) : TT F k :=
  ⟨fun i => S.1 i * T.1 i, kroneckerTensor S.2 T.2⟩

/-- Left-nested Kronecker fold of a list of bundled tensors over a base.

`kronFoldl T₀ [] = T₀` and
`kronFoldl T₀ (Ts ++ [Tn]) = (kronFoldl T₀ Ts).kron Tn`,
mirroring the left nesting of `kronPowNat`. -/
noncomputable def kronFoldl {k : ℕ} (T₀ : TT F k) (Ts : List (TT F k)) : TT F k :=
  Ts.foldl TT.kron T₀

@[simp] lemma kronFoldl_nil {k : ℕ} (T₀ : TT F k) :
    kronFoldl T₀ ([] : List (TT F k)) = T₀ := rfl

@[simp] lemma kronFoldl_cons {k : ℕ} (T₀ T : TT F k) (Ts : List (TT F k)) :
    kronFoldl T₀ (T :: Ts) = kronFoldl (T₀.kron T) Ts := rfl

lemma kronFoldl_concat {k : ℕ} (T₀ : TT F k) (Ts : List (TT F k)) (Tn : TT F k) :
    kronFoldl T₀ (Ts ++ [Tn]) = (kronFoldl T₀ Ts).kron Tn := by
  simp [kronFoldl, List.foldl_append]

/-- **`Restricts` on the total type**: `S ≤ₜ T` ignoring the bundled format. -/
def TTRestricts {k : ℕ} (S T : TT F k) : Prop := Restricts S.2 T.2

/-- `TT.kron` is monotone for `TTRestricts` (bundled `Restricts.kron_congr`). -/
lemma TTRestricts.kron {k : ℕ} {S₁ T₁ S₂ T₂ : TT F k}
    (h₁ : TTRestricts S₁ T₁) (h₂ : TTRestricts S₂ T₂) :
    TTRestricts (S₁.kron S₂) (T₁.kron T₂) :=
  Restricts.kron_congr h₁ h₂

/-- **Iterating `Restricts.kron_congr` along a list** (engine of ingredient 1).

If the base tensors satisfy `S₀ ≤ₜ T₀` and the two lists are pointwise related by
`TTRestricts` (`List.Forall₂`), then the left-nested Kronecker folds satisfy
`kronFoldl S₀ Ss ≤ₜ kronFoldl T₀ Ts`.

Proved by induction on `List.Forall₂` with the base tensors generalized, applying
`TTRestricts.kron` at each `cons` step. -/
lemma Restricts.kronFoldl {k : ℕ} :
    ∀ {S₀ T₀ : TT F k} {Ss Ts : List (TT F k)},
      TTRestricts S₀ T₀ → List.Forall₂ TTRestricts Ss Ts →
      TTRestricts (kronFoldl S₀ Ss) (kronFoldl T₀ Ts) := by
  intro S₀ T₀ Ss Ts h₀ h
  induction h generalizing S₀ T₀ with
  | nil => simpa using h₀
  | @cons s t Ss' Ts' hst _ ih =>
      rw [kronFoldl_cons, kronFoldl_cons]
      exact ih (h₀.kron hst)

/-! ## Ingredient 1c — `kronPowNat` as a left-nested fold. -/

/-- Bundle a `k`-tensor as an element of the total type `TT F k`. -/
def TT.of {k : ℕ} {d : Fin k → ℕ+} (T : KTensor F d) : TT F k := ⟨d, T⟩

/-- **`kronPowNat` as a left-nested Kronecker fold** of `n` copies of `T` over a
    base copy of `T`: `kronPowNat T n` (bundled) equals
    `kronFoldl (TT.of T) (List.replicate n (TT.of T))`.

`kronPowNat T 0 = T` (the base, `0` extra copies) and
`kronPowNat T (n+1) = kronPowNat T n ⊠ T` (one more copy), which is exactly the
left-nested fold accumulating over `List.replicate n (TT.of T)`. -/
lemma kronPowNat_eq_foldl {k : ℕ} {d : Fin k → ℕ+} (T : KTensor F d) (n : ℕ) :
    TT.of (kronPowNat T n) = kronFoldl (TT.of T) (List.replicate n (TT.of T)) := by
  induction n with
  | zero => simp [kronPowNat]
  | succ n ih =>
      rw [List.replicate_succ', kronFoldl_concat, ← ih]
      rfl

/-! ## Ingredient 1 — the headline pair-unit Kronecker restriction (tex:984-985). -/

/-- **Corollary 3.5, ingredient 1** (tex:983-985).

Let `p₀ :: ps : List (Fin k × Fin k)` enumerate distinct pairs of legs, each with
`0 < subrankPair T p.1 p.2` (witnessed by `hpos`) and `p.1 ≠ p.2` (witnessed by
`hne`), and write `N = ps.length + 1` (`= k(k-1)/2` for the full enumeration of
pairs `i < j`). For each pair `p = (i, j)` form the rank-`subrankPair T i j`
pair-unit `⟨subrankPair T i j⟩_{i,j}`, bundle it via `TT.of`, and take the
left-nested Kronecker fold over `p₀ :: ps` (with base the pair-unit at `p₀`). Then
this fold restricts to `kronPowNat T ps.length`, the `N`-fold Kronecker power
`T^{⊠N}` of the paper (note `kronPowNat T 0 = T`, so `kronPowNat T ps.length` has
`ps.length + 1 = N` factors).

This is exactly tex:984-985: `T^{⊠(k(k-1)/2)} ≥ ⊠_{i<j} ⟨q_{i,j}⟩_{i,j}` with
`q_{i,j} = subrank_{i,j}(T)`.

The proof: each pair-unit restricts to `T` (`subrankPair_unitPair_restricts`), so
`List.Forall₂ TTRestricts` holds between the pair-unit list and the all-`T` list;
iterating `Restricts.kron_congr` (`Restricts.kronFoldl`) folds these into
`⊠ pair-units ≤ₜ ⊠ (N copies of T)`, and the all-`T` fold is `kronPowNat T (N-1)`
(`kronPowNat_eq_foldl`). -/
theorem pairUnitKron_restricts_kronPow {k : ℕ} {d : Fin k → ℕ+} (T : KTensor F d)
    (p₀ : Fin k × Fin k) (ps : List (Fin k × Fin k))
    (hne : ∀ p ∈ p₀ :: ps, p.1 ≠ p.2)
    (hpos : ∀ p ∈ p₀ :: ps, 0 < subrankPair T p.1 p.2) :
    TTRestricts
      (kronFoldl
        (TT.of (unitPairTensor (F := F)
          ⟨subrankPair T p₀.1 p₀.2, hpos p₀ (List.mem_cons_self ..)⟩
          p₀.1 p₀.2 (hne p₀ (List.mem_cons_self ..))))
        (ps.attach.map (fun p =>
          TT.of (unitPairTensor (F := F)
            ⟨subrankPair T p.1.1 p.1.2,
              hpos p.1 (List.mem_cons_of_mem _ p.2)⟩
            p.1.1 p.1.2 (hne p.1 (List.mem_cons_of_mem _ p.2))))))
      (TT.of (kronPowNat T ps.length)) := by
  classical
  -- Each pair-unit restricts to `T`.
  have hbase : TTRestricts
      (TT.of (unitPairTensor (F := F)
        ⟨subrankPair T p₀.1 p₀.2, hpos p₀ (List.mem_cons_self ..)⟩
        p₀.1 p₀.2 (hne p₀ (List.mem_cons_self ..))))
      (TT.of T) :=
    subrankPair_unitPair_restricts T p₀.1 p₀.2
      (hne p₀ (List.mem_cons_self ..)) (hpos p₀ (List.mem_cons_self ..))
  -- The pair-unit list (over `ps.attach`) is pointwise `≤ₜ` the all-`T` list of
  -- the same length `ps.length`.
  have hforall : List.Forall₂ TTRestricts
      (ps.attach.map (fun p =>
        TT.of (unitPairTensor (F := F)
          ⟨subrankPair T p.1.1 p.1.2,
            hpos p.1 (List.mem_cons_of_mem _ p.2)⟩
          p.1.1 p.1.2 (hne p.1 (List.mem_cons_of_mem _ p.2)))))
      (List.replicate ps.length (TT.of T)) := by
    -- Rewrite the all-`T` list as `ps.attach.map (fun _ => TT.of T)`, then both
    -- sides are maps over `ps.attach`; pointwise each pair-unit restricts to `T`.
    have hlen : ps.length = ps.attach.length := (List.length_attach (l := ps)).symm
    rw [hlen, ← List.map_const' (l := ps.attach) (b := TT.of T)]
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr ?_
    intro p _
    exact subrankPair_unitPair_restricts T p.1.1 p.1.2
      (hne p.1 (List.mem_cons_of_mem _ p.2)) (hpos p.1 (List.mem_cons_of_mem _ p.2))
  -- Fold the restrictions; rewrite the all-`T` fold as `kronPowNat`.
  have hfold := Restricts.kronFoldl hbase hforall
  rw [← kronPowNat_eq_foldl] at hfold
  exact hfold


end Semicontinuity
