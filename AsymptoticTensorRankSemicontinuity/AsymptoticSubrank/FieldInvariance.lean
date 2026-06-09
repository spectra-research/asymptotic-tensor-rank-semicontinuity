/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import AsymptoticTensorRankSemicontinuity.MaxRankBound
import AsymptoticTensorRankSemicontinuity.FieldExtension
import AsymptoticTensorRankSemicontinuity.SpectralPointExtension
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.UnitOverhead
import AsymptoticTensorRankSemicontinuity.Prerequisites.Matrix.RankFieldHom

/-!
# Field-extension invariance of the asymptotic subrank (INGREDIENT 3 of Cor 3.5)

Source: **Semicontinuity paper** (Christandl–Hoeberechts–Nieuwboer–Vrana–Zuiddam),
proof of Corollary 3.5, ingredient 3 (paper tex:991-992): the asymptotic subrank
is invariant under field extension [Strassen 1988, Theorem 3.10], so one may assume
`F` is infinite.

This file formalizes that invariance: for an *algebraic* field extension `K / F`,
the asymptotic subrank `Q̃` of a `k`-tensor `T` over `F` is unchanged by base
change to `K` (**Strassen 1988, Theorem 3.10**, `strassen1988.tex:1264`, applied
to subrank).  Specializing `K = AlgebraicClosure F` (algebraic and infinite over
`F`) is what lets the Cor 3.5 proof "assume `F` is infinite": over an infinite
field the cardinality hypothesis of Theorem 3.2 (`subrankPair_prod_ge_flatRank`)
is automatic, and the asymptotic-subrank bound descends back to arbitrary `F`.

## Architecture

`MaxRankBound` (which defines `subrank` / `asympSubrank` / `kronPowNat` /
`unitTensor`) and `SpectralPointExtension` (which proves the Strassen-1988
restriction descent `restricts_descend_to_intermediateField` /
`finiteExt_restricts_descent`) are *independent* modules.  This file imports
both, establishing the downstream home where Cor 3.5 itself will eventually live.

## A note on the single-copy statement

At the **single-copy** level subrank is in general only *monotone* under base
change, NOT invariant: `subrank T ≤ subrank (T.baseChange K)` (easy direction),
but the descent of a `K`-restriction `⟨r⟩ ≤ T_K` over `K` to `F` carries a
Strassen overhead `⟨q⟩` (a finite scalar-restriction cost; `q = [K':F]^k` for
the finite subextension `K'` confining the restriction's structure constants),
yielding only `⟨r⟩ ≤ ⟨q⟩ ⊠ T` over `F`, not `⟨r⟩ ≤ T`.  This is genuinely why
Strassen 1988 Theorem 3.10 is a statement about the *asymptotic* subrank: the
overhead `q` is a fixed constant, so `q^{1/n} → 1` washes it out in the limit
`Q̃(T) = sup_n subrank(T^{⊠n})^{1/n}`.  Accordingly the headline of this file is
the *asymptotic* equality `asympSubrank_baseChange`; the single-copy
`subrank_baseChange_le` is only the easy `≤`.

## Main results

* `KTensor.baseChange_kronPowNat` — base change commutes with the Kronecker power.
* `subrank_baseChange_le` — easy direction: `subrank T ≤ subrank (T.baseChange K)`.
* `asympSubrank_baseChange` — **Strassen 1988 Theorem 3.10** for subrank:
  `asympSubrank (T.baseChange K) = asympSubrank T` for algebraic `K / F`.
* `asympSubrank_baseChange_algClosure` — the `K = AlgebraicClosure F` specialization
  used directly by the Cor 3.5 proof.
-/

namespace Semicontinuity

open Filter

universe u

variable {F : Type u} [Field F] {k : ℕ}

/-! ## Base change commutes with the Kronecker power. -/

/-- Base change commutes with the `n`-fold Kronecker power `kronPowNat`.
    Both sides have format `kronPowFormat d n` (which depends only on `d`),
    so the equation typechecks directly.  By induction on `n`, using
    `KTensor.baseChange_kron`. -/
theorem KTensor.baseChange_kronPowNat {K : Type u} [Field K] [Algebra F K]
    {d : Fin k → ℕ+} (T : KTensor F d) :
    ∀ n : ℕ, (kronPowNat T n).baseChange (K := K)
        = kronPowNat (T.baseChange (K := K)) n
  | 0 => rfl
  | n + 1 => by
      change (kroneckerTensor (kronPowNat T n) T).baseChange (K := K)
          = kroneckerTensor (kronPowNat (T.baseChange (K := K)) n) (T.baseChange (K := K))
      rw [KTensor.baseChange_kron, KTensor.baseChange_kronPowNat T n]

/-- flatRank does not increase under base change along a field extension. -/
theorem flatRank_baseChange_le {K : Type u} [Field K] [Algebra F K]
    {d : Fin k → ℕ+} (T : KTensor F d) (I : Finset (Fin k)) :
    flatRank (T.baseChange (K := K)) I ≤ flatRank T I := by
  classical
  let M := flattenMatrix T I
  have hMatrix : (M.map (algebraMap F K)).rank ≤ M.rank := by
    rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
    obtain ⟨b, _hb_mem, hb_span, _hb_li⟩ :=
      Submodule.exists_fun_fin_finrank_span_eq F (Set.range M.col)
    have hle :
        Submodule.span K (Set.range (M.map (algebraMap F K)).col) ≤
          Submodule.span K (Set.range fun i =>
            (algebraMap F K) ∘ b i) := by
      rw [Submodule.span_le]
      rintro _ ⟨col, rfl⟩
      have hcol_mem : M.col col ∈ Submodule.span F (Set.range b) := by
        rw [hb_span]
        exact Submodule.subset_span ⟨col, rfl⟩
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hcol_mem
      refine (Submodule.mem_span_range_iff_exists_fun K).mpr ⟨fun i => algebraMap F K (c i), ?_⟩
      ext row
      have hc_row : (∑ i, c i * b i row) = M row col := by
        simpa [Matrix.col_apply, Finset.sum_apply, smul_eq_mul] using congr_fun hc row
      calc
        (∑ x, algebraMap F K (c x) • ((algebraMap F K) ∘ b x)) row
            = ∑ x, algebraMap F K (c x * b x row) := by
                simp [Function.comp_apply, Algebra.smul_def, map_mul]
        _ = algebraMap F K (∑ x, c x * b x row) := (map_sum (algebraMap F K) _ _).symm
        _ = algebraMap F K (M row col) := by rw [hc_row]
        _ = M.map (algebraMap F K) row col := rfl
    exact (Submodule.finrank_mono hle).trans <| by
      calc Module.finrank K (Submodule.span K (Set.range fun i =>
                (algebraMap F K) ∘ b i))
          ≤ (Set.range (fun i => (algebraMap F K) ∘ b i)).toFinset.card :=
              finrank_span_le_card _
        _ ≤ Fintype.card (Fin (Module.finrank F (Submodule.span F (Set.range M.col)))) := by
              convert Fintype.card_range_le (fun i => (algebraMap F K) ∘ b i)
              rw [Set.toFinset_card]
        _ = Module.finrank F (Submodule.span F (Set.range M.col)) := Fintype.card_fin _
  have hflat :
      flattenMatrix (T.baseChange (K := K)) I = (flattenMatrix T I).map (algebraMap F K) := by
    ext row col
    rfl
  rw [flatRank, flatRank, hflat]
  exact hMatrix

/-- Matrix rank does not decrease after applying an injective field hom. -/
theorem Matrix.rank_le_rank_map_injective_fieldHom
    {K₁ K₂ : Type*} [Field K₁] [Field K₂]
    {m n : Type*} [Finite m] [Fintype n]
    (f : K₁ →+* K₂) (hf : Function.Injective f) (M : Matrix m n K₁) :
    M.rank ≤ (M.map f).rank := by
  classical
  have : Fintype m := Fintype.ofFinite m
  let em : m ≃ Fin (Fintype.card m) := Fintype.equivFin m
  let en : n ≃ Fin (Fintype.card n) := Fintype.equivFin n
  set Mfin : Matrix (Fin (Fintype.card m)) (Fin (Fintype.card n)) K₁ :=
    M.submatrix em.symm en.symm with hMfin
  have hM_rank : M.rank = Mfin.rank := (M.rank_submatrix em.symm en.symm).symm
  have hmap_rank : (M.map f).rank = (Mfin.map f).rank := by
    have hsub :
        (M.map f).submatrix em.symm en.symm = Mfin.map f := by
      ext i j
      simp [Mfin]
    rw [← hsub]
    exact ((M.map f).rank_submatrix em.symm en.symm).symm
  rw [hM_rank, hmap_rank]
  exact le_of_eq (Matrix.rank_map_of_injective_fieldHom f hf Mfin).symm

/-- Matrix rank does not decrease under extension of scalars along `F ⊆ K`. -/
theorem Matrix.rank_le_rank_map_algebraMap {K : Type u} [Field K] [Algebra F K]
    {m n : Type*} [Finite m] [Fintype n] (M : Matrix m n F) :
    M.rank ≤ (M.map (algebraMap F K)).rank :=
  Matrix.rank_le_rank_map_injective_fieldHom (algebraMap F K) (algebraMap F K).injective M

/-- `flatRank` is invariant under base change along a field extension. -/
theorem flatRank_baseChange_eq {K : Type u} [Field K] [Algebra F K]
    {d : Fin k → ℕ+} (T : KTensor F d) (I : Finset (Fin k)) :
    flatRank (T.baseChange (K := K)) I = flatRank T I := by
  classical
  refine le_antisymm (flatRank_baseChange_le T I) ?_
  have hflat :
      flattenMatrix (T.baseChange (K := K)) I = (flattenMatrix T I).map (algebraMap F K) := by
    ext row col
    rfl
  rw [flatRank, flatRank, hflat]
  exact Matrix.rank_le_rank_map_algebraMap (K := K) (flattenMatrix T I)

/-! ## Boundedness of the subrank set.

For `k ≥ 2`, a restriction `⟨r⟩ ≤ T` forces `r ≤ flatRank T {i₀}` for a leg
`i₀` admitting a *distinct* column leg `i₁ ≠ i₀`, because the `{i₀}`-flattening
of the unit tensor contains an `r × r` identity submatrix (the rank-`r` lower
bound, read off the legs `i₀` and `i₁`), and `flatRank` is monotone under
restriction (`Restricts.flatRank_le`).  Hence the subrank set is bounded above.
(For `k ≤ 1` the unit tensor is the all-ones tensor independently of `r`, so the
set is *not* bounded — boundedness genuinely needs `k ≥ 2`; the Cor 3.5 setting
has `k ≥ 2`.) -/

/-- A rank-`r` unit `k`-tensor `⟨r⟩` whose `{i₀}`-flattening contains the `r × r`
    identity submatrix, read off two distinct legs `i₀ ≠ i₁`, so
    `r ≤ flatRank ⟨r⟩ {i₀}`. -/
private lemma unitTensor_flatRank_singleton_ge
    (i₀ i₁ : Fin k) (hne : i₁ ≠ i₀) {r : ℕ} (hr : 0 < r) :
    r ≤ flatRank (unitTensor F (k := k) ⟨r, hr⟩) {i₀} := by
  classical
  set U : KTensor F (fun _ : Fin k => (⟨r, hr⟩ : ℕ+)) := unitTensor F (k := k) ⟨r, hr⟩
  have memi : i₀ ∈ ({i₀} : Finset (Fin k)) := Finset.mem_singleton_self i₀
  have memj : i₁ ∉ ({i₀} : Finset (Fin k)) := by rwa [Finset.mem_singleton]
  -- Row reindex `eRow : Fin r ≃ RowType` (the row type `∀ x ∈ {i₀}, Fin r` is a
  -- singleton-indexed tuple, hence `≃ Fin r`): `m ↦ (constant tuple m)`.
  let eRow : Fin r ≃ ((x : {x // x ∈ ({i₀} : Finset (Fin k))}) → Fin r) :=
    { toFun := fun m _ => m
      invFun := fun row => row ⟨i₀, memi⟩
      left_inv := fun m => rfl
      right_inv := fun row => by
        funext x
        obtain ⟨x, hx⟩ := x
        have : x = i₀ := Finset.mem_singleton.mp hx
        subst this
        rfl }
  -- Column map: `v ↦ (constant tuple v)`.
  let cmap : Fin r → ((x : {x // x ∉ ({i₀} : Finset (Fin k))}) → Fin r) :=
    fun v _ => v
  -- The flattening submatrix at these maps is the identity matrix on `Fin r`.
  have hsub : (flattenMatrix U {i₀}).submatrix eRow cmap = (1 : Matrix (Fin r) (Fin r) F) := by
    ext m v
    rw [Matrix.submatrix_apply, Matrix.one_apply]
    simp only [flattenMatrix, U, unitTensor]
    -- Abbreviate the merged tuple.
    set g : Fin k → Fin r := fun x => if h : x ∈ ({i₀} : Finset (Fin k))
      then (eRow m ⟨x, h⟩ : Fin r) else (cmap v ⟨x, h⟩ : Fin r) with hg
    change (if ∀ i j : Fin k, g i = g j then (1 : F) else 0) = if m = v then 1 else 0
    -- Every merged coordinate equals `m` (row) or `v` (column).
    have hmerge : ∀ a : Fin k, g a = if a ∈ ({i₀} : Finset (Fin k)) then m else v := by
      intro a
      simp only [hg]
      by_cases ha : a ∈ ({i₀} : Finset (Fin k))
      · rw [dif_pos ha, if_pos ha]; rfl
      · rw [dif_neg ha, if_neg ha]
    have hval_i0 : g i₀ = m := by rw [hmerge i₀, if_pos memi]
    have hval_i1 : g i₁ = v := by rw [hmerge i₁, if_neg memj]
    -- The all-equal predicate holds iff `m = v`.
    have hpred : (∀ i j : Fin k, g i = g j) ↔ m = v := by
      constructor
      · intro hall
        have h2 := hall i₀ i₁
        rw [hval_i0, hval_i1] at h2
        exact h2
      · intro hmv a b
        rw [hmerge a, hmerge b, hmv]
        split <;> split <;> rfl
    by_cases hmv : m = v
    · rw [if_pos (hpred.mpr hmv), if_pos hmv]
    · rw [if_neg (fun h => hmv (hpred.mp h)), if_neg hmv]
  -- `flatRank U {i₀} = rank (flattenMatrix U {i₀}) ≥ rank (its identity submatrix) = r`.
  -- Reindex rows by the equiv `eRow`, columns by the arbitrary `cmap`; the
  -- submatrix is the identity (`hsub`), and rank only drops under submatrices
  -- (`Matrix.rank_submatrix_le`, applied to the transpose so the equiv is on
  -- the column slot).
  have hsubr : ((flattenMatrix U {i₀}).submatrix eRow cmap).rank
      ≤ (flattenMatrix U {i₀}).rank := by
    rw [← Matrix.rank_transpose ((flattenMatrix U {i₀}).submatrix eRow cmap),
        ← Matrix.rank_transpose (flattenMatrix U {i₀}), Matrix.transpose_submatrix]
    exact Matrix.rank_submatrix_le _ eRow _
  rw [hsub, Matrix.rank_one, Fintype.card_fin] at hsubr
  exact hsubr

/-- For `k ≥ 2`, the subrank set `{r | 0 < r ∧ ⟨r⟩ ≤ T}` is bounded above (by
    `flatRank T {i₀}` for a leg `i₀` admitting a distinct leg `i₁ ≠ i₀`). -/
private lemma subrank_set_bddAbove {d : Fin k → ℕ+}
    (i₀ i₁ : Fin k) (hne : i₁ ≠ i₀) (T : KTensor F d) :
    BddAbove { r : ℕ | ∃ hr : 0 < r, Restricts (unitTensor F (k := k) ⟨r, hr⟩) T } := by
  classical
  refine ⟨flatRank T {i₀}, ?_⟩
  rintro r ⟨hr, hres⟩
  calc r ≤ flatRank (unitTensor F (k := k) ⟨r, hr⟩) {i₀} :=
        unitTensor_flatRank_singleton_ge i₀ i₁ hne hr
    _ ≤ flatRank T {i₀} := hres.flatRank_le {i₀}

/-! ## Easy direction: `subrank` is monotone under base change. -/

/-- **Strassen 1988 Theorem 3.10, easy direction, for subrank** (paper tex:991-992).

    `subrank T ≤ subrank (T.baseChange K)`: a restriction `⟨r⟩ ≤ T` over `F`
    base-changes to `⟨r⟩ ≤ T_K` over `K` (`KTensor.baseChange_restricts`), using
    that the unit tensor is preserved by base change
    (`KTensor.baseChange_unitTensor`).  Hence every member of the `F`-subrank set
    is a member of the `K`-subrank set, and `sSup` is monotone. -/
theorem subrank_baseChange_le {K : Type u} [Field K] [Algebra F K]
    (i₀ i₁ : Fin k) (hne : i₁ ≠ i₀) {d : Fin k → ℕ+} (T : KTensor F d) :
    subrank T ≤ subrank (T.baseChange (K := K)) := by
  classical
  unfold subrank
  apply csSup_le_csSup'
  · -- The `K`-subrank set is bounded above.
    exact subrank_set_bddAbove i₀ i₁ hne _
  · -- Subset: a witness over `F` is a witness over `K`.
    rintro r ⟨hr, hres⟩
    refine ⟨hr, ?_⟩
    have hbc := KTensor.baseChange_restricts (K := K) _ _ hres
    rwa [KTensor.baseChange_unitTensor] at hbc

/-! ## Hard direction: descent of a `K`-restriction to `F` (Strassen 1988 Thm 3.10).

A restriction `⟨r⟩ ≤ T_K` over `K` descends, for algebraic `K / F`, to a
restriction `⟨r⟩ ≤ ⟨q⟩ ⊠ T` over `F` for some finite overhead `q : ℕ+`
(`q = [K':F]^k` for the finite subextension `K'` confining the witness's
structure constants).  This is the composition of the two Strassen-1988 descent
steps proved in `SpectralPointExtension`:

* `restricts_descend_to_intermediateField` (P1): confine the `K`-restriction to a
  finite subextension `K' / F`.
* `finiteExt_restricts_descent` (P2): descend a `K'`-restriction of base-changed
  `F`-tensors to `F`, at the cost of the finite overhead `⟨q⟩`.

Both are proved in `SpectralPointExtension`, and both hypotheses hold for
`K = AlgebraicClosure F` (which is algebraic over `F`). -/
theorem restricts_baseChange_descent {K : Type u} [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K] {dS dT : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT)
    (h : Restricts (S.baseChange (K := K)) (T.baseChange (K := K))) :
    ∃ q : ℕ+, Restricts S (unitTensor F (k := k) q ⊠ T) := by
  -- (P1) confine to a finite subextension `K'`.
  obtain ⟨K', hfin, hK'⟩ := restricts_descend_to_intermediateField (K := K) S T h
  haveI : FiniteDimensional F K' := hfin
  -- (P2) descend the `K'`-restriction of base-changed `F`-tensors to `F`.
  obtain ⟨q, hq⟩ := finiteExt_restricts_descent (F := F) (k := k) K'
  exact ⟨q, hq S T hK'⟩

/-! ## Lifting to the asymptotic subrank.

The per-power single-copy equality `subrank (kronPowNat (T_K) n) = subrank
(kronPowNat T n)` is FALSE in general (the descent overhead `⟨q⟩` survives, see
the module docstring), so `asympSubrank_baseChange` is NOT obtained by a
term-wise equality of the two `sSup` ranges.  Instead it is the genuine
*asymptotic* statement: the `≥` direction is term-wise (`subrank_baseChange_le`
on each power), and the `≤` direction is the Strassen-1988 limit argument — the
finite overhead `q_n` from `restricts_baseChange_descent` is washed out by the
`n`-th root, `q_n^{1/n} → 1`, exactly as in the `AsympRel` descent of
`SpectralPointExtension.tensorClass_hord` (`SpectralPointExtension.lean:907-1100`). -/

/-- `kronPowNat` of a base change is the base change of `kronPowNat`, transported
    along `KTensor.baseChange_kronPowNat`. -/
private lemma subrank_kronPowNat_baseChange_eq {K : Type u} [Field K] [Algebra F K]
    {d : Fin k → ℕ+} (T : KTensor F d) (n : ℕ) :
    subrank (kronPowNat (T.baseChange (K := K)) n)
      = subrank ((kronPowNat T n).baseChange (K := K)) := by
  rw [KTensor.baseChange_kronPowNat]

/-! ### Uniform bound on `subrank` of Kronecker powers (`BddAbove` ingredient).

For `k ≥ 2`, the subrank set is bounded by `flatRank · {i₀}` (the local lemma
`subrank_set_bddAbove`), and `flatRank T {i₀}` is the rank of a matrix whose row
type has cardinality `d i₀`, hence `flatRank T {i₀} ≤ d i₀`.  Composing, every
`subrank T ≤ d i₀`.  Specialized to `kronPowNat T n` (whose `i₀`-leg dimension is
`(d i₀)^(n+1)`), this bounds the `asympSubrank` range and makes both
`csSup`-monotonicity directions available. -/

/-- `flatRank T {i₀} ≤ d i₀`: the `{i₀}`-flattening is a matrix with `d i₀` rows,
    and `Matrix.rank ≤` (number of rows). -/
private lemma flatRank_singleton_le_dim {d : Fin k → ℕ+} (i₀ : Fin k)
    (T : KTensor F d) :
    flatRank T {i₀} ≤ (d i₀ : ℕ) := by
  classical
  rw [flatRank]
  refine (Matrix.rank_le_card_height _).trans_eq ?_
  simp [Fintype.card_pi]

/-- For `k ≥ 2` (via the two distinct legs `i₀ ≠ i₁`), `subrank T ≤ d i₀`:
    `subrank` is the `sSup` of the subrank set, which `subrank_set_bddAbove`
    bounds member-wise by `flatRank T {i₀} ≤ d i₀`. -/
private lemma subrank_le_dim {d : Fin k → ℕ+}
    (i₀ i₁ : Fin k) (hne : i₁ ≠ i₀) (T : KTensor F d) :
    subrank T ≤ (d i₀ : ℕ) := by
  classical
  refine le_trans ?_ (flatRank_singleton_le_dim i₀ T)
  unfold subrank
  apply csSup_le'
  rintro r ⟨hr, hres⟩
  calc r ≤ flatRank (unitTensor F (k := k) ⟨r, hr⟩) {i₀} :=
        unitTensor_flatRank_singleton_ge i₀ i₁ hne hr
    _ ≤ flatRank T {i₀} := hres.flatRank_le {i₀}

/-- The `i₀`-leg dimension of the `n`-fold Kronecker power is `(d i₀)^(n+1)`
    (`kronPowFormat d 0 = d`, `kronPowFormat d (n+1) i = kronPowFormat d n i · d i`). -/
private lemma kronPowFormat_apply_val {d : Fin k → ℕ+} (n : ℕ) (i₀ : Fin k) :
    (kronPowFormat d n i₀ : ℕ) = (d i₀ : ℕ) ^ (n + 1) := by
  induction n with
  | zero => simp [kronPowFormat]
  | succ m ih => simp only [kronPowFormat, PNat.mul_coe, ih]; ring

/-- `subrank (kronPowNat T n) ≤ (d i₀)^(n+1)`: the subrank of the `n`-th Kronecker
    power is bounded by its `i₀`-leg dimension `(d i₀)^(n+1)`.  This is the
    uniform bound underlying `BddAbove` of the `asympSubrank` range. -/
private lemma subrank_kronPowNat_le {d : Fin k → ℕ+}
    (i₀ i₁ : Fin k) (hne : i₁ ≠ i₀) (T : KTensor F d) (n : ℕ) :
    subrank (kronPowNat T n) ≤ (d i₀ : ℕ) ^ (n + 1) := by
  have h := subrank_le_dim i₀ i₁ hne (kronPowNat T n)
  rwa [kronPowFormat_apply_val n i₀] at h

/-- **`BddAbove` of the `asympSubrank` range** (paper tex:974, `BddAbove`
    ingredient).  Each term `subrank (kronPowNat T n)^{1/(n+1)} ≤ d i₀`:
    `subrank (kronPowNat T n) ≤ (d i₀)^(n+1)` (`subrank_kronPowNat_le`), and
    `((d i₀)^(n+1))^{1/(n+1)} = d i₀`. -/
private lemma asympSubrank_range_bddAbove {d : Fin k → ℕ+}
    (i₀ i₁ : Fin k) (hne : i₁ ≠ i₀) (T : KTensor F d) :
    BddAbove (Set.range (fun n : ℕ =>
      (subrank (kronPowNat T n) : ℝ) ^ ((1 : ℝ) / ((n : ℝ) + 1)))) := by
  refine ⟨(d i₀ : ℝ), ?_⟩
  rintro y ⟨n, rfl⟩
  simp only
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hd1 : (1 : ℝ) ≤ (d i₀ : ℝ) := by
    have : (1 : ℕ) ≤ (d i₀ : ℕ) := (d i₀).one_le
    exact_mod_cast this
  -- `subrank (kronPowNat T n) ≤ (d i₀)^(n+1)` over `ℝ`.
  have hsr : (subrank (kronPowNat T n) : ℝ) ≤ (d i₀ : ℝ) ^ (n + 1) := by
    have := subrank_kronPowNat_le i₀ i₁ hne T n
    calc (subrank (kronPowNat T n) : ℝ) ≤ (((d i₀ : ℕ) ^ (n + 1) : ℕ) : ℝ) := by
            exact_mod_cast this
      _ = (d i₀ : ℝ) ^ (n + 1) := by push_cast; ring
  -- Raise to the `1/(n+1)` power (monotone since base ≥ 0 and exponent ≥ 0).
  calc (subrank (kronPowNat T n) : ℝ) ^ ((1 : ℝ) / ((n : ℝ) + 1))
      ≤ ((d i₀ : ℝ) ^ (n + 1)) ^ ((1 : ℝ) / ((n : ℝ) + 1)) :=
        Real.rpow_le_rpow (by positivity) hsr (by positivity)
    _ = (d i₀ : ℝ) := by
        rw [← Real.rpow_natCast (d i₀ : ℝ) (n + 1), ← Real.rpow_mul (by positivity)]
        rw [show ((n + 1 : ℕ) : ℝ) * ((1 : ℝ) / ((n : ℝ) + 1)) = 1 by
              push_cast; field_simp]
        rw [Real.rpow_one]

/-! ## Hard direction: spectral argument and field-general packaging.

The `≤` direction `asympSubrank (T.baseChange K) ≤ asympSubrank T` is the
Strassen-1988 spectral argument.  Over an infinite base field, the concrete
base-change theorem below splits on whether `mk ⟨d,T⟩` is gapped:

* **Gapped**: every concrete spectral point `φ` over `F`
  extends to a concrete spectral point `ψ` over `K` agreeing on base-changed
  tensors (`exists_spectralPoint_extension_bridge`, itself the asymptotic-preorder
  descent `tensorClass_hord`, `SpectralPointExtension.lean:907-1100`).  Hence
  `asympSubrank (T_K) ≤ ψ(T_K) = φ(T)` for every `φ`, so
  `asympSubrank (T_K) ≤ ⨅_φ φ(T) ≤ asympSubrank T` (last step is the gapped
  duality `iInf_concrete_le_asympSubrank`).  The unit-overhead is handled at the
  *spectral* level, never via the FALSE `subrank (⟨q⟩ ⊠ S) ≤ q·subrank S`.

* **Non-gapped** over an infinite field is handled by the flattening-rank-one
  argument below.  The field-general asymptotic-preorder package at the end of this
  file is deliberately stated with the explicit gapped hypotheses needed for the
  spectrum-duality formula. -/

open AsymptoticSpectrumDuality

/-- **Regularization idempotence for asymptotic subrank.**

Passing from a Strassen preorder to its asymptotic preorder does not change the
regularized subrank. -/
private lemma asympSubrank_le_asympPreorder_asympSubrank
    {S : Type*} [CommSemiring S] (p : StrassenPreorder S) (a : S) :
    p.asympSubrank a ≤ (asympPreorder p).asympSubrank a := by
  unfold StrassenPreorder.asympSubrank
  apply csSup_le (p.asympSubrankSet_nonempty a)
  intro x hx
  simp only [StrassenPreorder.asympSubrankSet, Set.mem_image, Set.mem_Ici] at hx ⊢
  obtain ⟨n, hn, rfl⟩ := hx
  have hsubrank :
      p.subrank (a ^ n) ≤ (asympPreorder p).subrank (a ^ n) := by
    rw [(asympPreorder p).le_subrank_iff]
    exact AsympRel.of_le (p.rel_subrank (a ^ n))
  have hmem :
      ((asympPreorder p).subrank (a ^ n) : ℝ) ^ (1 / (n : ℝ)) ∈
        (asympPreorder p).asympSubrankSet a := by
    exact ⟨n, hn, rfl⟩
  apply le_csSup_of_le ((asympPreorder p).asympSubrankSet_bddAbove a) hmem
  apply Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hsubrank)
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr
    (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn))
  exact div_nonneg (by norm_num) (le_of_lt hn_pos)

private lemma iInf_spectrum_asympPreorder_eq
    {S : Type*} [CommSemiring S] (p : StrassenPreorder S) (a : S)
    [Nonempty (AsymptoticSpectrum p)]
    [Nonempty (AsymptoticSpectrum (asympPreorder p))] :
    (⨅ φ : AsymptoticSpectrum (asympPreorder p),
        AsymptoticSpectrum.eval (asympPreorder p) a φ)
      =
    (⨅ φ : AsymptoticSpectrum p, AsymptoticSpectrum.eval p a φ) := by
  classical
  have hbdd_asymp :
      BddBelow (Set.range (AsymptoticSpectrum.eval (asympPreorder p) a)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨φ, rfl⟩
    exact AsymptoticSpectrum.eval_nonneg (asympPreorder p) φ a
  have hbdd_p : BddBelow (Set.range (AsymptoticSpectrum.eval p a)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨φ, rfl⟩
    exact AsymptoticSpectrum.eval_nonneg p φ a
  apply le_antisymm
  · apply le_ciInf
    intro φ
    calc
      (⨅ ψ : AsymptoticSpectrum (asympPreorder p),
          AsymptoticSpectrum.eval (asympPreorder p) a ψ)
          ≤ AsymptoticSpectrum.eval (asympPreorder p) a (upgrade p φ) :=
            ciInf_le hbdd_asymp (upgrade p φ)
      _ = AsymptoticSpectrum.eval p a φ := rfl
  · apply le_ciInf
    intro ψ
    calc
      (⨅ φ : AsymptoticSpectrum p, AsymptoticSpectrum.eval p a φ)
          ≤ AsymptoticSpectrum.eval p a (downgrade p ψ) :=
            ciInf_le hbdd_p (downgrade p ψ)
      _ = AsymptoticSpectrum.eval (asympPreorder p) a ψ := rfl

private lemma isGapped_asympPreorder_of_isGapped
    {S : Type*} [CommSemiring S] {p : StrassenPreorder S} {a : S}
    (ha : p.IsGapped a) :
    (asympPreorder p).IsGapped a := by
  rcases ha with ⟨n, hn, hrel⟩ | hzero | ⟨φ₀, hφ₀⟩
  · exact Or.inl ⟨n, hn, AsympRel.of_le hrel⟩
  · exact Or.inr (Or.inl (AsympRel.of_le hzero))
  · -- disjunct (iii): `upgrade` carries φ₀ to a spectral point of `asympPreorder p`
    -- with the same evaluation (it shares `toFun`), so φ₀(a) = 1 is preserved.
    exact Or.inr (Or.inr ⟨upgrade p φ₀, hφ₀⟩)

private lemma isGapped_map_of_rel_mono
    {S₁ S₂ : Type*} [CommSemiring S₁] [CommSemiring S₂]
    (p₁ : StrassenPreorder S₁) (p₂ : StrassenPreorder S₂)
    (i : S₁ →+* S₂)
    (hmono : ∀ a b : S₁, p₁.rel a b → p₂.rel (i a) (i b))
    (hspec : ∀ φ₁ : AsymptoticSpectrum p₁, ∃ φ₂ : AsymptoticSpectrum p₂,
      ∀ x, AsymptoticSpectrum.eval p₂ (i x) φ₂ = AsymptoticSpectrum.eval p₁ x φ₁)
    {a : S₁} (ha : p₁.IsGapped a) :
    p₂.IsGapped (i a) := by
  rcases ha with ⟨n, hn, hrel⟩ | hzero | ⟨φ₀, hφ₀⟩
  · refine Or.inl ⟨n, hn, ?_⟩
    have h := hmono (2 : S₁) (a ^ n) hrel
    have htwo : i (2 : S₁) = (2 : S₂) := by
      simpa using map_ofNat i 2
    simpa [map_pow, htwo] using h
  · exact Or.inr (Or.inl (by simpa using hmono a 0 hzero))
  · -- disjunct (iii): push φ₀ forward to a spectral point φ₂ of p₂ (via hspec) with
    -- φ₂(i a) = φ₀(a) = 1.  `hspec` is supplied by `restriction_surjective` (Thm A.2).
    obtain ⟨φ₂, hφ₂⟩ := hspec φ₀
    exact Or.inr (Or.inr ⟨φ₂, by rw [hφ₂ a]; exact hφ₀⟩)

/-- Reverse direction in regularization idempotence for gapped elements.

The proof uses Strassen's spectrum-duality formula for `p` and for
`asympPreorder p`.  The two spectra have the same evaluations via the existing
`upgrade`/`downgrade` maps, so the two spectral infima coincide.  This avoids the
false finite scalar-overhead estimate
`subrank ((c : S) * b) ≤ c * subrank b`. -/
private lemma asympPreorder_asympSubrank_le_asympSubrank
    {S : Type*} [CommSemiring S] (p : StrassenPreorder S) (a : S)
    [Nonempty (AsymptoticSpectrum p)]
    [Nonempty (AsymptoticSpectrum (asympPreorder p))]
    (ha : p.IsGapped a) (harch : ∀ x : S, p.rel x 0 ∨ p.rel 1 x) :
    (asympPreorder p).asympSubrank a ≤ p.asympSubrank a := by
  have ha_asymp : (asympPreorder p).IsGapped a :=
    isGapped_asympPreorder_of_isGapped ha
  have harch_asymp : ∀ x : S, (asympPreorder p).rel x 0 ∨ (asympPreorder p).rel 1 x :=
    fun x => (harch x).imp AsympRel.of_le AsympRel.of_le
  rw [StrassenPreorder.asympSubrank_eq_iInf_spectrum (asympPreorder p) a ha_asymp harch_asymp,
    StrassenPreorder.asympSubrank_eq_iInf_spectrum p a ha harch]
  exact le_of_eq (iInf_spectrum_asympPreorder_eq p a)

lemma asympSubrank_asympPreorder_eq
    {S : Type*} [CommSemiring S] (p : StrassenPreorder S) (a : S)
    [Nonempty (AsymptoticSpectrum p)]
    [Nonempty (AsymptoticSpectrum (asympPreorder p))]
    (ha : p.IsGapped a) (harch : ∀ x : S, p.rel x 0 ∨ p.rel 1 x) :
    p.asympSubrank a = (asympPreorder p).asympSubrank a := by
  exact le_antisymm
    (asympSubrank_le_asympPreorder_asympSubrank p a)
    (asympPreorder_asympSubrank_le_asympSubrank p a ha harch)

/-- If a semiring homomorphism identifies two Strassen-preorder relations on its
image, then it preserves subrank. -/
private lemma subrank_map_eq_of_rel_iff
    {S₁ S₂ : Type*} [CommSemiring S₁] [CommSemiring S₂]
    (p₁ : StrassenPreorder S₁) (p₂ : StrassenPreorder S₂)
    (i : S₁ →+* S₂)
    (hord : ∀ a b : S₁, p₁.rel a b ↔ p₂.rel (i a) (i b))
    (a : S₁) :
    p₂.subrank (i a) = p₁.subrank a := by
  apply le_antisymm
  · rw [p₁.le_subrank_iff]
    apply (hord _ a).mpr
    simpa using p₂.rel_subrank (i a)
  · rw [p₂.le_subrank_iff]
    have hrel : p₂.rel (i ((p₁.subrank a : ℕ) : S₁)) (i a) :=
      (hord _ a).mp (p₁.rel_subrank a)
    simpa using hrel

/-- If a semiring homomorphism identifies two Strassen-preorder relations on its
image, then it preserves asymptotic subrank. -/
private lemma asympSubrank_map_eq_of_rel_iff
    {S₁ S₂ : Type*} [CommSemiring S₁] [CommSemiring S₂]
    (p₁ : StrassenPreorder S₁) (p₂ : StrassenPreorder S₂)
    (i : S₁ →+* S₂)
    (hord : ∀ a b : S₁, p₁.rel a b ↔ p₂.rel (i a) (i b))
    (a : S₁) :
    p₂.asympSubrank (i a) = p₁.asympSubrank a := by
  have hsubrank_pow :
      ∀ n : ℕ, p₂.subrank ((i a) ^ n) = p₁.subrank (a ^ n) := by
    intro n
    simpa only [map_pow] using subrank_map_eq_of_rel_iff p₁ p₂ i hord (a ^ n)
  have hset : p₂.asympSubrankSet (i a) = p₁.asympSubrankSet a := by
    ext x
    constructor
    · intro hx
      simp only [StrassenPreorder.asympSubrankSet, Set.mem_image, Set.mem_Ici] at hx ⊢
      obtain ⟨n, hn, rfl⟩ := hx
      exact ⟨n, hn, by rw [← hsubrank_pow n]⟩
    · intro hx
      simp only [StrassenPreorder.asympSubrankSet, Set.mem_image, Set.mem_Ici] at hx ⊢
      obtain ⟨n, hn, rfl⟩ := hx
      exact ⟨n, hn, by rw [hsubrank_pow n]⟩
  unfold StrassenPreorder.asympSubrank
  rw [hset]

/-- **Gapped abstract regularization package for `asympSubrank`.**

If a semiring homomorphism identifies the asymptotic preorders on its image, then
the asymptotic subrank of a gapped image point is unchanged.  The proof first
identifies the exact subranks after replacing both preorders by their asymptotic
preorders, then uses the gapped spectrum-duality idempotence above. -/
lemma asympSubrank_map_eq_of_asympPreorder_rel_iff
    {S₁ S₂ : Type*} [CommSemiring S₁] [CommSemiring S₂]
    (p₁ : StrassenPreorder S₁) (p₂ : StrassenPreorder S₂)
    [Nonempty (AsymptoticSpectrum p₁)]
    [Nonempty (AsymptoticSpectrum (asympPreorder p₁))]
    [Nonempty (AsymptoticSpectrum p₂)]
    [Nonempty (AsymptoticSpectrum (asympPreorder p₂))]
    (i : S₁ →+* S₂)
    (hord : ∀ a b : S₁,
      (asympPreorder p₁).rel a b ↔
        (asympPreorder p₂).rel (i a) (i b))
    (a : S₁) (ha : p₁.IsGapped a) (hia : p₂.IsGapped (i a))
    (harch₁ : ∀ x : S₁, p₁.rel x 0 ∨ p₁.rel 1 x)
    (harch₂ : ∀ x : S₂, p₂.rel x 0 ∨ p₂.rel 1 x) :
    p₂.asympSubrank (i a) = p₁.asympSubrank a := by
  calc
    p₂.asympSubrank (i a)
        = (asympPreorder p₂).asympSubrank (i a) :=
            asympSubrank_asympPreorder_eq p₂ (i a) hia harch₂
    _ = (asympPreorder p₁).asympSubrank a :=
            asympSubrank_map_eq_of_rel_iff
              (asympPreorder p₁) (asympPreorder p₂) i hord a
    _ = p₁.asympSubrank a :=
            (asympSubrank_asympPreorder_eq p₁ a ha harch₁).symm

/-- **Strassen 1988 Theorem 3.10** for the asymptotic subrank (paper tex:991-992).

    For an algebraic field extension `K / F`, the asymptotic subrank is invariant
    under base change: `asympSubrank (T.baseChange K) = asympSubrank T`.

    The `≥` direction is term-wise monotonicity of `subrank` under base change
    (`subrank_baseChange_le` on each Kronecker power).

    The `≤` direction `asympSubrank (T.baseChange K) ≤ asympSubrank T` is the
    Strassen-1988 spectral argument, via a **gapped / non-gapped case split** on
    `mk ⟨d, T⟩`:

    * **Gapped** `T`.  Every concrete spectral point
      `φ : SpectralPoint k F` extends to a concrete spectral point `ψ` over `K`
      agreeing on base-changed tensors (`exists_spectralPoint_extension_bridge`,
      itself the asymptotic-preorder descent `tensorClass_hord`,
      `SpectralPointExtension.lean:907-1100`).
      Hence `asympSubrank (T_K) ≤ ψ(T_K) = φ(T)` for every `φ`
      (`asympSubrank_le_spectralPoint` + the bridge `asympSubrank_eq_abstract`), so
      `asympSubrank (T_K) ≤ ⨅_φ φ(T) ≤ asympSubrank T`, the last step being the
      gapped Strassen-1988 duality `iInf_concrete_le_asympSubrank` (the only place
      gappedness is used).  The unit-overhead is handled at the *spectral* level,
      NOT via the FALSE finite bound `subrank (⟨q⟩ ⊠ S) ≤ q·subrank S`; the
      corrected overhead lemma `subrank_of_restricts_unit_overhead`
      (`AsymptoticSubrank/UnitOverhead.lean`) has `asympSubrank` on its right-hand side.

    * **Non-gapped** `T`: the field-general
      "subrank-1-stable ⟹ flattening-rank-one cut" argument applies; it is
      NOT the false `(★)` finite-overhead bound, and every `(★)`-shaped
      finite-subrank overhead bound has been removed.

    The two legs `i₀ ≠ i₁` (existing since `k ≥ 2`, re-derived as `hk : 2 ≤ k`)
    provide the flattening witnesses making the per-power subrank sets bounded
    above and supply the `2 ≤ k` hypothesis of the spectral bridge. -/
theorem asympSubrank_baseChange [Infinite F] {K : Type u} [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K]
    (i₀ i₁ : Fin k) (hne : i₁ ≠ i₀) {d : Fin k → ℕ+} (T : KTensor F d) :
    asympSubrank (T.baseChange (K := K)) = asympSubrank T := by
  classical
  -- Abbreviate the two per-power root sequences (root index `n+1`).
  set gK : ℕ → ℝ := fun n =>
    (subrank (kronPowNat (T.baseChange (K := K)) n) : ℝ) ^ ((1 : ℝ) / ((n : ℝ) + 1)) with hgK
  set gF : ℕ → ℝ := fun n =>
    (subrank (kronPowNat T n) : ℝ) ^ ((1 : ℝ) / ((n : ℝ) + 1)) with hgF
  have hKdef : asympSubrank (T.baseChange (K := K)) = sSup (Set.range gK) := rfl
  have hFdef : asympSubrank T = sSup (Set.range gF) := rfl
  have hbddK : BddAbove (Set.range gK) := asympSubrank_range_bddAbove i₀ i₁ hne _
  -- Term-wise `gF n ≤ gK n` from single-copy monotonicity of `subrank` under base change.
  have hterm : ∀ n : ℕ, gF n ≤ gK n := by
    intro n
    simp only [hgF, hgK]
    apply Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    have hle : subrank (kronPowNat T n)
        ≤ subrank (kronPowNat (T.baseChange (K := K)) n) := by
      rw [subrank_kronPowNat_baseChange_eq]
      exact subrank_baseChange_le i₀ i₁ hne (kronPowNat T n)
    exact_mod_cast hle
  rw [hKdef, hFdef]
  refine le_antisymm ?_ ?_
  · -- `≤` direction: gapped spectral argument plus the non-gapped flattening argument.
    -- `k ≥ 2` from the two distinct legs.
    have hk : 2 ≤ k := by
      have hi₀ : (i₀ : ℕ) < k := i₀.2
      have hi₁ : (i₁ : ℕ) < k := i₁.2
      by_contra hklt
      push_neg at hklt
      have hval : (i₀ : ℕ) = (i₁ : ℕ) := by omega
      exact hne (Fin.ext hval).symm
    haveI : NeZero k := ⟨by omega⟩
    set pF := tensorStrassenPreorder (F := F) hk with hpF
    set aF : TensorClass F k := TensorClass.mk ⟨d, T⟩ with haF
    by_cases hgapF : pF.IsGapped aF
    · -- GAPPED: spectral-point extension bridge + gapped duality.
      have hhard_concrete : asympSubrank (T.baseChange (K := K)) ≤ asympSubrank T := by
        classical
        -- For every concrete `φ` over `F`: `asympSubrank (T_K) ≤ φ(T)` (via its `K`-extension).
        have hle_each : ∀ φ : SpectralPoint k F,
            asympSubrank (T.baseChange (K := K)) ≤ φ.toFun T := by
          intro φ
          obtain ⟨ψ, hψ⟩ := exists_spectralPoint_extension_bridge (F := F) (K := K) hk φ
          set pK := tensorStrassenPreorder (F := K) hk with hpK
          set aK : TensorClass K k := TensorClass.mk ⟨d, T.baseChange (K := K)⟩ with haK
          have habstract :=
            AsymptoticSpectrumDuality.StrassenPreorder.asympSubrank_le_spectralPoint
              (p := pK) (toAbstractSpectralPoint (F := K) hk ψ) aK
          have hbridgeK : asympSubrank (T.baseChange (K := K)) = pK.asympSubrank aK := by
            rw [haK, hpK, asympSubrank_eq_abstract hk (T.baseChange (K := K))]
          have hval : (toAbstractSpectralPoint (F := K) hk ψ).toFun aK = φ.toFun T := by
            rw [haK]
            change ψ.toFun (T.baseChange (K := K)) = φ.toFun T
            exact hψ T
          rw [hbridgeK]
          change pK.asympSubrank aK ≤ (toAbstractSpectralPoint (F := K) hk ψ).toFun aK
            at habstract
          rwa [hval] at habstract
        haveI : Nontrivial (TensorClass F k) := tensorClass_nontrivial hk
        haveI hneSpec : Nonempty
            (AsymptoticSpectrumDuality.AsymptoticSpectrum
              (tensorStrassenPreorder (F := F) hk)) :=
          AsymptoticSpectrumDuality.AsymptoticSpectrum.nonempty _
        haveI : Nonempty (SpectralPoint k F) :=
          ⟨ofAbstractSpectralPoint (K := F) hk hneSpec.some⟩
        have hinf_le : asympSubrank (T.baseChange (K := K))
            ≤ ⨅ φ : SpectralPoint k F, φ.toFun T :=
          le_ciInf hle_each
        have hbridgeF : (⨅ φ : SpectralPoint k F, φ.toFun T) ≤ asympSubrank T := by
          have hgapF' : (tensorStrassenPreorder (F := F) hk).IsGapped
              (TensorClass.mk ⟨d, T⟩) := by
            simpa only [hpF, haF] using hgapF
          exact iInf_concrete_le_asympSubrank hk T hgapF'
        exact le_trans hinf_le hbridgeF
      rw [hKdef, hFdef] at hhard_concrete
      exact hhard_concrete
    · -- Non-gapped case via field-general Lemma A / flattening, survey
      -- tex:2286-2297.  Non-gappedness gives "subrank-1-stable"; Lemma A's
      -- contrapositive then forces a flattening rank `≤ 1`, which bounds the whole
      -- `T_K`-asymptotic-subrank range by `1`, while `1 ≤ asympSubrank T` (nonzero `T`).
      -- `hno_strict m : ¬ pF.rel ⟨2⟩ (aF^m)` (no positive power restricts `⟨2⟩`).
      have hno_strict : ∀ m : ℕ, 0 < m → ¬ pF.rel (2 : TensorClass F k) (aF ^ m) := by
        intro m hm h2
        exact hgapF (Or.inl ⟨m, hm, h2⟩)
      have hnot_zero : ¬ pF.rel aF (0 : TensorClass F k) := by
        intro h0
        exact hgapF (Or.inr (Or.inl h0))
      -- (1) subrank-1-stability over `F`: `subrank (kronPowNat T n) ≤ 1` for all `n`.
      have hstable : ∀ n : ℕ, subrank (kronPowNat T n) ≤ 1 := by
        intro n
        -- `¬ pF.rel ⟨2⟩ (aF^(n+1))` and `aF^(n+1) = mk (kronPowNat T n)`.
        have hns := hno_strict (n + 1) (Nat.succ_pos n)
        rw [mkPow T n] at hns
        -- `¬ pF.rel ⟨2⟩ (mk ⟨_, kronPowNat T n⟩)`  ↔  `¬ 2 ≤ pF.subrank (…)`.
        have h2cast : (2 : TensorClass F k) = ((2 : ℕ) : TensorClass F k) := by
          norm_cast
        rw [h2cast] at hns
        have hnle : ¬ (2 : ℕ) ≤ pF.subrank (TensorClass.mk ⟨_, kronPowNat T n⟩) := by
          intro hle
          exact hns ((pF.le_subrank_iff _ 2).mp hle)
        -- bridge `pF.subrank (mk …) = subrank (kronPowNat T n)`.
        have hbridge : pF.subrank (TensorClass.mk ⟨_, kronPowNat T n⟩)
            = subrank (kronPowNat T n) :=
          (subrank_eq_abstract hk (kronPowNat T n)).symm
        rw [hbridge] at hnle
        omega
      -- (2) Corrected Lemma A contrapositive: some *bipartition* cut `Scut` has
      --     `flatRank T Scut ≤ 1` (survey:2286-2297).
      obtain ⟨Scut, hScut_ne, hScut_univ, hflat⟩ :=
        exists_flatRank_cut_le_one_of_subrank_stable hk T hstable
      obtain ⟨a₀, ha₀⟩ := hScut_ne
      obtain ⟨a₁, ha₁⟩ : ∃ a₁, a₁ ∉ Scut := by
        by_contra hc; push_neg at hc
        exact hScut_univ (Finset.eq_univ_of_forall hc)
      -- (3) `flatRank (T_K) Scut ≤ 1` (base change does not increase flattening rank).
      have hflatK : flatRank (T.baseChange (K := K)) Scut ≤ 1 :=
        le_trans (flatRank_baseChange_le T Scut) hflat
      -- (4) Each `gK n ≤ 1`: `subrank (kronPowNat T_K n) ≤ flatRank (…) Scut
      --     ≤ (flatRank (T_K) Scut)^(n+1) ≤ 1`.
      have hgK_le_one : ∀ n : ℕ, gK n ≤ 1 := by
        intro n
        simp only [hgK]
        have hsub_le : subrank (kronPowNat (T.baseChange (K := K)) n)
            ≤ flatRank (kronPowNat (T.baseChange (K := K)) n) Scut :=
          subrank_le_flatRank_cut Scut ha₀ ha₁ _
        -- `flatRank (kronPowNat T_K n) Scut ≤ (flatRank (T_K) Scut)^(n+1) ≤ 1`
        -- (Kronecker submultiplicativity of flatRank, general cut).
        have hflat_pow : flatRank (kronPowNat (T.baseChange (K := K)) n) Scut
            ≤ 1 := by
          have hpow : ∀ m : ℕ, flatRank (kronPowNat (T.baseChange (K := K)) m) Scut
              ≤ (flatRank (T.baseChange (K := K)) Scut) ^ (m + 1) := by
            intro m
            induction m with
            | zero => simp [kronPowNat]
            | succ p ih =>
                have hstep : kronPowNat (T.baseChange (K := K)) (p + 1)
                    = kronPowNat (T.baseChange (K := K)) p ⊠ (T.baseChange (K := K)) := rfl
                calc flatRank (kronPowNat (T.baseChange (K := K)) (p + 1)) Scut
                    ≤ flatRank (kronPowNat (T.baseChange (K := K)) p) Scut
                        * flatRank (T.baseChange (K := K)) Scut := by
                      rw [hstep]; exact flatRank_kron_mul_ge _ _ Scut
                  _ ≤ (flatRank (T.baseChange (K := K)) Scut) ^ (p + 1)
                        * flatRank (T.baseChange (K := K)) Scut :=
                      Nat.mul_le_mul_right _ ih
                  _ = (flatRank (T.baseChange (K := K)) Scut) ^ (p + 1 + 1) := by ring
          calc flatRank (kronPowNat (T.baseChange (K := K)) n) Scut
              ≤ (flatRank (T.baseChange (K := K)) Scut) ^ (n + 1) := hpow n
            _ ≤ 1 ^ (n + 1) := Nat.pow_le_pow_left hflatK (n + 1)
            _ = 1 := one_pow _
        have hsub_le_one : subrank (kronPowNat (T.baseChange (K := K)) n) ≤ 1 :=
          le_trans hsub_le hflat_pow
        have hbase_le : (subrank (kronPowNat (T.baseChange (K := K)) n) : ℝ) ≤ 1 := by
          exact_mod_cast hsub_le_one
        calc (subrank (kronPowNat (T.baseChange (K := K)) n) : ℝ)
              ^ ((1 : ℝ) / ((n : ℝ) + 1))
            ≤ (1 : ℝ) ^ ((1 : ℝ) / ((n : ℝ) + 1)) :=
              Real.rpow_le_rpow (by positivity) hbase_le (by positivity)
          _ = 1 := Real.one_rpow _
      -- (5) `1 ≤ sSup (range gF)`: `gF 0 = subrank T ≥ 1` (nonzero `T`).
      have haF_ne : (TensorClass.mk ⟨d, T⟩ : TensorClass F k) ≠ 0 := by
        intro h0
        exact hnot_zero (by rw [haF, h0]; exact pF.refl 0)
      have hone_sub : 1 ≤ subrank T := by
        have hres : Restricts (unitTensor F (k := k) 1) T :=
          unitTensor_one_restricts_of_ne_zero T haF_ne
        have hmem : (1 : ℕ) ∈ { r : ℕ | ∃ hr : 0 < r,
            Restricts (unitTensor F (k := k) ⟨r, hr⟩) T } := ⟨one_pos, by simpa using hres⟩
        have hbdd : BddAbove { r : ℕ | ∃ hr : 0 < r,
            Restricts (unitTensor F (k := k) ⟨r, hr⟩) T } :=
          subrank_set_bddAbove i₀ i₁ hne T
        exact le_csSup hbdd hmem
      have hone_le_gF : (1 : ℝ) ≤ sSup (Set.range gF) := by
        have hgF0 : gF 0 = (subrank T : ℝ) := by
          simp [hgF, kronPowNat]
        have h1le : (1 : ℝ) ≤ gF 0 := by
          rw [hgF0]; exact_mod_cast hone_sub
        have hbddF : BddAbove (Set.range gF) := by
          simpa only [hgF] using (asympSubrank_range_bddAbove i₀ i₁ hne T)
        exact le_trans h1le (le_csSup hbddF ⟨0, rfl⟩)
      -- Assemble: `sSup (range gK) ≤ 1 ≤ sSup (range gF)`.
      refine le_trans (csSup_le (Set.range_nonempty gK) ?_) hone_le_gF
      rintro _ ⟨n, rfl⟩
      exact hgK_le_one n
  · -- `≥` direction (EASY): term-wise `subrank`-monotonicity under base change.
    refine csSup_le (Set.range_nonempty gF) ?_
    rintro _ ⟨n, rfl⟩
    exact le_trans (hterm n) (le_csSup hbddK ⟨n, rfl⟩)

/-- **Abstract bridge from Strassen 1988 Theorem 3.10 to asymptotic subrank**
    (semicontinuity tex:991-992; Strassen 1988, `strassen1988.tex:1264`).

`tensorClass_hord` proves field invariance of the asymptotic preorder on
`TensorClass` (the `⟨r⟩ ≲ T` level).  This lemma is the remaining packaging step:
identify the abstract asymptotic subrank as the supremum of the unit classes
asymptotically below the tensor class, and transport that supremum through
`tensorClass_hord`. -/
theorem abstract_asympSubrank_baseChange_of_hord {K : Type u} [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K] (hk : 2 ≤ k)
    {d : Fin k → ℕ+} (T : KTensor F d)
    (hgap :
      haveI : NeZero k := ⟨by omega⟩
      (tensorStrassenPreorder (F := F) hk).IsGapped (TensorClass.mk ⟨d, T⟩)) :
    haveI : NeZero k := ⟨by omega⟩
    (tensorStrassenPreorder (F := K) hk).asympSubrank
        (TensorClass.mk ⟨d, T.baseChange (K := K)⟩)
      =
    (tensorStrassenPreorder (F := F) hk).asympSubrank
        (TensorClass.mk ⟨d, T⟩) := by
  classical
  haveI : NeZero k := ⟨by omega⟩
  set pF := tensorStrassenPreorder (F := F) hk with hpF
  set pK := tensorStrassenPreorder (F := K) hk with hpK
  set i := tensorClassBaseChange (F := F) (K := K) (k := k) with hi
  haveI : Nontrivial (TensorClass F k) := tensorClass_nontrivial hk
  haveI : Nontrivial (TensorClass K k) := tensorClass_nontrivial hk
  haveI : Nonempty (AsymptoticSpectrum pF) := AsymptoticSpectrum.nonempty pF
  haveI : Nonempty (AsymptoticSpectrum (asympPreorder pF)) :=
    AsymptoticSpectrum.nonempty (asympPreorder pF)
  haveI : Nonempty (AsymptoticSpectrum pK) := AsymptoticSpectrum.nonempty pK
  haveI : Nonempty (AsymptoticSpectrum (asympPreorder pK)) :=
    AsymptoticSpectrum.nonempty (asympPreorder pK)
  have hhord : ∀ a b : TensorClass F k,
      (asympPreorder pF).rel a b ↔
        (asympPreorder pK).rel (i a) (i b) := by
    simpa [pF, pK, i] using tensorClass_hord (F := F) (K := K) hk hk
  have hmono : ∀ a b : TensorClass F k, pF.rel a b → pK.rel (i a) (i b) := by
    intro a b hab
    simpa [pF, pK, i] using
      tensorClassBaseChange_rel_mono (F := F) (K := K) hk hk a b hab
  have hgapF : pF.IsGapped (TensorClass.mk ⟨d, T⟩) := by
    simpa [pF] using hgap
  have hspec : ∀ φF : AsymptoticSpectrum pF, ∃ φK : AsymptoticSpectrum pK,
      ∀ x, AsymptoticSpectrum.eval pK (i x) φK =
        AsymptoticSpectrum.eval pF x φF := by
    intro φF
    obtain ⟨ψK, hψK⟩ :=
      restriction_surjective (asympPreorder pF) (asympPreorder pK) i hhord
        (upgrade pF φF)
    refine ⟨downgrade pK ψK, ?_⟩
    intro x
    change ψK.toFun (i x) = φF.toFun x
    exact hψK x
  have harchF : ∀ x : TensorClass F k, pF.rel x 0 ∨ pF.rel 1 x := by
    simpa [pF] using tensor_strong_archimedean (F := F) hk
  have harchK : ∀ x : TensorClass K k, pK.rel x 0 ∨ pK.rel 1 x := by
    simpa [pK] using tensor_strong_archimedean (F := K) hk
  have hgapK : pK.IsGapped (i (TensorClass.mk ⟨d, T⟩)) :=
    isGapped_map_of_rel_mono pF pK i hmono hspec hgapF
  change pK.asympSubrank (i (TensorClass.mk ⟨d, T⟩))
      = pF.asympSubrank (TensorClass.mk ⟨d, T⟩)
  exact asympSubrank_map_eq_of_asympPreorder_rel_iff
    pF
    pK
    i
    hhord
    (TensorClass.mk ⟨d, T⟩)
    hgapF
    hgapK
    harchF
    harchK

/-- **Strassen 1988 Theorem 3.10**, field-general asymptotic-subrank invariance
    (semicontinuity tex:991-992; Strassen 1988, `strassen1988.tex:1264`).

This version uses the field-general asymptotic-preorder descent
`tensorClass_hord` and therefore has no `[Infinite F]` hypothesis.  It is stated
with the explicit gapped hypothesis needed by the spectrum-duality packaging. -/
theorem asympSubrank_baseChange_general {K : Type u} [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K]
    (hk : 2 ≤ k) {d : Fin k → ℕ+} (T : KTensor F d)
    (hgap :
      haveI : NeZero k := ⟨by omega⟩
      (tensorStrassenPreorder (F := F) hk).IsGapped (TensorClass.mk ⟨d, T⟩)) :
    asympSubrank (T.baseChange (K := K)) = asympSubrank T := by
  classical
  haveI : NeZero k := ⟨by omega⟩
  calc
    asympSubrank (T.baseChange (K := K))
        = (tensorStrassenPreorder (F := K) hk).asympSubrank
            (TensorClass.mk ⟨d, T.baseChange (K := K)⟩) :=
          asympSubrank_eq_abstract hk (T.baseChange (K := K))
    _ = (tensorStrassenPreorder (F := F) hk).asympSubrank
            (TensorClass.mk ⟨d, T⟩) :=
          abstract_asympSubrank_baseChange_of_hord (F := F) (K := K) hk T hgap
    _ = asympSubrank T :=
          (asympSubrank_eq_abstract hk T).symm

/-- **Strassen 1988 Theorem 3.10**, `K = AlgebraicClosure F` specialization
    (paper tex:991-992).  The algebraic closure is algebraic (and infinite) over
    `F`, so the asymptotic subrank is unchanged passing to it — this is what lets
    the Cor 3.5 proof "assume `F` is infinite". -/
theorem asympSubrank_baseChange_algClosure
    (hk : 2 ≤ k) {d : Fin k → ℕ+} (T : KTensor F d)
    (hgap :
      haveI : NeZero k := ⟨by omega⟩
      (tensorStrassenPreorder (F := F) hk).IsGapped (TensorClass.mk ⟨d, T⟩)) :
    asympSubrank (T.baseChange (K := AlgebraicClosure F)) = asympSubrank T :=
  asympSubrank_baseChange_general hk T hgap

end Semicontinuity
