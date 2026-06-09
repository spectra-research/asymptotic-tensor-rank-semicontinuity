/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.MaxRankBound
import AsymptoticTensorRankSemicontinuity.SpectralPointExtension
import AsymptoticTensorRankSemicontinuity.Prerequisites.AsymptoticSpectrumDuality.SpectrumDuality

/-!
# Concrete ↔ abstract asymptotic-spectrum duality bridge for `KTensor`

This file builds the bridge identifying the *concrete* tensor `subrank` /
`asympSubrank` (`MaxRankBound.lean`) with the *abstract* Strassen-preorder
`subrank` / `asympSubrank` (`AsymptoticSpectrumDuality.RankSubrank`) under
`tensorStrassenPreorder hk : StrassenPreorder (TensorClass F k)`.

Source: Strassen 1988 (the asymptotic spectrum of tensors), the
asymptotic-spectrum duality / completeness theorem, as packaged abstractly in
`AsymptoticSpectrumDuality.SpectrumDuality.asympSubrank_eq_iInf_spectrum`.

## Main results

* `mkPow` — `(TensorClass.mk ⟨d, T⟩) ^ (n+1) = TensorClass.mk ⟨_, kronPowNat T n⟩`
  (the `kronPowNat` off-by-one: `kronPowNat T n = T^{⊠(n+1)}`).
* `subrank_eq_abstract` — **(a)** `subrank S = pF.subrank (mk ⟨d, S⟩)`.
* `asympSubrank_eq_abstract` — **(b)** `asympSubrank S = pF.asympSubrank (mk ⟨d, S⟩)`.
* `iInf_concrete_le_asympSubrank_of_gapped` — the HARD duality direction at
  `KTensor` for gapped `S`: `(⨅ φ : SpectralPoint k F, φ.toFun S) ≤ asympSubrank S`.
-/

namespace Semicontinuity

open AsymptoticSpectrumDuality

universe u

variable {F : Type u} [Field F] {k : ℕ} [NeZero k]

attribute [local instance] Classical.propDecidable

/-! ## The `mk`-power ↔ `kronPowNat` correspondence (the `n+1` off-by-one). -/

/-- `(mk ⟨d, T⟩) ^ (n+1) = mk ⟨_, kronPowNat T n⟩`.

The semiring power on `TensorClass` is `npowRec` (`a^0 = 1`, `a^(n+1) = a^n * a`),
and `mk` of a Kronecker product is the product of classes (`mk_mul`), so this is a
clean induction matching `kronPowNat T (n+1) = kronPowNat T n ⊠ T`.  The shift by
`1` is the `kronPowNat T 0 = T` convention. -/
lemma mkPow {d : Fin k → ℕ+} (T : KTensor F d) (n : ℕ) :
    (TensorClass.mk ⟨d, T⟩ : TensorClass F k) ^ (n + 1)
      = TensorClass.mk ⟨_, kronPowNat T n⟩ := by
  induction n with
  | zero =>
    change (TensorClass.mk ⟨d, T⟩ : TensorClass F k) ^ 1 = TensorClass.mk ⟨_, kronPowNat T 0⟩
    rw [pow_one]; rfl
  | succ n ih =>
    rw [pow_succ, ih]
    -- `kronPowNat T (n+1) = kronPowNat T n ⊠ T`, and `mk_mul`.
    change TensorClass.mk ⟨_, kronPowNat T n⟩ * TensorClass.mk ⟨d, T⟩
      = TensorClass.mk ⟨_, kronPowNat T (n + 1)⟩
    rw [TensorClass.mk_mul]
    rfl

/-! ## Bridge (a) — concrete `subrank` = abstract `subrank`. -/

/-- The abstract relation `pF.rel (n : TensorClass) (mk ⟨d, S⟩)` for `n > 0` is exactly
the concrete restriction `Restricts (unitTensor ⟨n, hn⟩) S`. -/
lemma rel_natCast_mk_iff_restricts (hk : 2 ≤ k) {d : Fin k → ℕ+} (S : KTensor F d)
    {n : ℕ} (hn : 0 < n) :
    (tensorStrassenPreorder (F := F) hk).rel ((n : ℕ) : TensorClass F k)
        (TensorClass.mk ⟨d, S⟩)
      ↔ Restricts (unitTensor F (k := k) ⟨n, hn⟩) S := by
  rw [natCast_eq_unitClass, unitClass, dif_pos hn]
  rfl

/-- The abstract relation `pF.rel (0 : TensorClass) (mk ⟨d, S⟩)` always holds. -/
lemma rel_zero_mk (hk : 2 ≤ k) {d : Fin k → ℕ+} (S : KTensor F d) :
    (tensorStrassenPreorder (F := F) hk).rel ((0 : ℕ) : TensorClass F k)
      (TensorClass.mk ⟨d, S⟩) := by
  simpa using (tensorStrassenPreorder (F := F) hk).zero_le (TensorClass.mk ⟨d, S⟩)

/-- **Bridge (a)** — the concrete tensor `subrank` agrees with the abstract
Strassen-preorder `subrank` of the class `mk ⟨d, S⟩`.

Both are the largest `r` with `⟨r⟩ ≤ₜ S` (abstractly: `(r : TensorClass) ≤_P mk S`),
the only subtlety being that the concrete `sSup`-set ranges over *positive* `r`
while the abstract one includes `0` (which is `≤_P` everything). -/
lemma subrank_eq_abstract (hk : 2 ≤ k) {d : Fin k → ℕ+} (S : KTensor F d) :
    (subrank S : ℕ) = (tensorStrassenPreorder (F := F) hk).subrank (TensorClass.mk ⟨d, S⟩) := by
  classical
  set pF := tensorStrassenPreorder (F := F) hk with hpF
  -- Every concrete witness `r` gives an abstract witness, hence
  -- `r ≤ pF.subrank (mk S)`.  This is both the `≤` direction AND the `BddAbove`.
  have hfwd : ∀ r ∈ { r : ℕ | ∃ hr : 0 < r, Restricts (unitTensor F (k := k) ⟨r, hr⟩) S },
      r ≤ pF.subrank (TensorClass.mk ⟨d, S⟩) := by
    rintro r ⟨hr, hres⟩
    rw [pF.le_subrank_iff, hpF, rel_natCast_mk_iff_restricts hk S hr]
    exact hres
  have hbdd : BddAbove { r : ℕ | ∃ hr : 0 < r, Restricts (unitTensor F (k := k) ⟨r, hr⟩) S } :=
    ⟨_, hfwd⟩
  apply le_antisymm
  · -- `subrank S ≤ pF.subrank (mk S)`.
    exact csSup_le' hfwd
  · -- `pF.subrank (mk S) ≤ subrank S`: every abstract witness `n > 0` is concrete.
    change sSup { n : ℕ | pF.rel (n : TensorClass F k) (TensorClass.mk ⟨d, S⟩) } ≤ subrank S
    rw [csSup_le_iff (pF.subrank_set_bddAbove _)
        ⟨0, by simpa using pF.zero_le (TensorClass.mk ⟨d, S⟩)⟩]
    intro n hn
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0; exact Nat.zero_le _
    · apply le_csSup hbdd
      refine ⟨hnpos, ?_⟩
      rw [← rel_natCast_mk_iff_restricts hk S hnpos]
      exact hn

/-- **Per-power bridge**: `subrank (kronPowNat S n) = pF.subrank ((mk ⟨d,S⟩)^(n+1))`.

Combines `mkPow` (`(mk S)^(n+1) = mk (kronPowNat S n)`) with bridge (a). -/
lemma subrank_kronPowNat_eq_abstract (hk : 2 ≤ k) {d : Fin k → ℕ+} (S : KTensor F d) (n : ℕ) :
    (subrank (kronPowNat S n) : ℕ)
      = (tensorStrassenPreorder (F := F) hk).subrank
          ((TensorClass.mk ⟨d, S⟩ : TensorClass F k) ^ (n + 1)) := by
  rw [mkPow, subrank_eq_abstract hk]

/-! ## Bridge (b) — concrete `asympSubrank` = abstract `asympSubrank`.

The concrete `asympSubrank` (`MaxRankBound.lean:4866`, corrected def, tex:974) is
`sSup { subrank (kronPowNat T n)^{1/(n+1)} : n ∈ ℕ }`.  Because `kronPowNat T n` is the
`(n+1)`-fold Kronecker power (`kronPowNat T 0 = T`), the concrete `n`-th term is
`subrank(T^{⊠(n+1)})^{1/(n+1)}`, whose *root* index `n+1` now MATCHES its *power*
index `n+1`.  After reindexing `m = n+1`, this is exactly the standard
`Q̃(T) = sup_{m ≥ 1} subrank(T^{⊠m})^{1/m}`, the abstract `pF.asympSubrankSet (mk T)`.
The old off-by-one (`1/N` root on the `(N+1)`-power) — which forced the bridge to be
a directional `≤` only — is gone, so the bridge is now a clean EQUALITY. -/

/-- The concrete `asympSubrank` `sSup`-range is bounded above (by `pF.rank a`,
`a = mk ⟨d,S⟩`).  The `n`-th term is `subrank(S^{⊠(n+1)})^{1/(n+1)}`, and
`subrank(S^{⊠(n+1)}) = pF.subrank (a^(n+1)) ≤ pF.rank a ^ (n+1)`, so the term is
`≤ (pF.rank a)^{(n+1)/(n+1)} = pF.rank a` (the root index now matches the power
index `n+1`, removing the old off-by-one `(N+1)/N` skew). -/
lemma concrete_asympSubrankSet_bddAbove (hk : 2 ≤ k) {d : Fin k → ℕ+} (S : KTensor F d) :
    BddAbove (Set.range (fun n : ℕ =>
      (subrank (kronPowNat S n) : ℝ) ^ ((1 : ℝ) / ((n : ℝ) + 1)))) := by
  classical
  set pF := tensorStrassenPreorder (F := F) hk with hpF
  set a : TensorClass F k := TensorClass.mk ⟨d, S⟩ with ha
  refine ⟨(pF.rank a : ℝ), ?_⟩
  rintro x ⟨N, rfl⟩
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  -- `subrank (kronPowNat S N) = pF.subrank (a^(N+1)) ≤ pF.rank a ^ (N+1)`.
  have heq : (subrank (kronPowNat S N) : ℕ) = pF.subrank (a ^ (N + 1)) := by
    rw [ha, subrank_kronPowNat_eq_abstract hk S N]
  have hle : pF.subrank (a ^ (N + 1)) ≤ pF.rank a ^ (N + 1) :=
    le_trans (pF.subrank_le_rank _) (pF.rank_pow_le a (N + 1))
  have hsubr_le : (subrank (kronPowNat S N) : ℝ) ≤ (pF.rank a : ℝ) ^ (N + 1) := by
    rw [heq]; exact_mod_cast hle
  have hbase_nonneg : (0 : ℝ) ≤ (pF.rank a : ℝ) := Nat.cast_nonneg _
  have hexp_nonneg : (0 : ℝ) ≤ (1 : ℝ) / ((N : ℝ) + 1) := by positivity
  calc (subrank (kronPowNat S N) : ℝ) ^ ((1 : ℝ) / ((N : ℝ) + 1))
      ≤ ((pF.rank a : ℝ) ^ (N + 1)) ^ ((1 : ℝ) / ((N : ℝ) + 1)) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hsubr_le hexp_nonneg
    _ = (pF.rank a : ℝ) := by
        rw [← Real.rpow_natCast (pF.rank a : ℝ) (N + 1), ← Real.rpow_mul hbase_nonneg]
        rw [show ((N + 1 : ℕ) : ℝ) * ((1 : ℝ) / ((N : ℝ) + 1)) = 1 by
              push_cast; field_simp]
        rw [Real.rpow_one]

/-- **Bridge (b)** — the concrete `asympSubrank S` agrees with the abstract
Strassen-preorder `asympSubrank (mk ⟨d,S⟩)`.

With the corrected concrete definition (`MaxRankBound.lean`, tex:974) the concrete
`sSup`-range and the abstract `asympSubrankSet` are the SAME set: reindexing the
concrete index `n ∈ ℕ` (term `subrank(kronPowNat S n)^{1/(n+1)} = subrank(a^{n+1})^{1/(n+1)}`)
by `m = n+1 ≥ 1` lands exactly on the abstract term `subrank(a^m)^{1/m}`.  Hence the
two `sSup`s coincide.  (Previously the concrete root index was `1/n` on the `(n+1)`-power,
making the two sets differ and only a directional `≤` provable; that off-by-one is gone.) -/
lemma asympSubrank_eq_abstract (hk : 2 ≤ k) {d : Fin k → ℕ+} (S : KTensor F d) :
    asympSubrank S
      = (tensorStrassenPreorder (F := F) hk).asympSubrank (TensorClass.mk ⟨d, S⟩) := by
  classical
  set pF := tensorStrassenPreorder (F := F) hk with hpF
  set a : TensorClass F k := TensorClass.mk ⟨d, S⟩ with ha
  -- Both are `sSup` of the SAME set; show the two index families have equal range/image.
  have hset : (Set.range (fun n : ℕ =>
        (subrank (kronPowNat S n) : ℝ) ^ ((1 : ℝ) / ((n : ℝ) + 1))))
      = pF.asympSubrankSet a := by
    rw [StrassenPreorder.asympSubrankSet]
    apply Set.eq_of_subset_of_subset
    · -- concrete ⊆ abstract: term at `n` is the abstract term at `m = n+1 ≥ 1`.
      rintro x ⟨n, rfl⟩
      refine ⟨n + 1, Set.mem_Ici.mpr (Nat.le_add_left 1 n), ?_⟩
      simp only
      have heq : (subrank (kronPowNat S n) : ℕ) = pF.subrank (a ^ (n + 1)) := by
        rw [ha, subrank_kronPowNat_eq_abstract hk S n]
      rw [heq]
      push_cast
      ring_nf
    · -- abstract ⊆ concrete: abstract term at `m ≥ 1` is the concrete term at `n = m-1`.
      rintro x ⟨m, hm, rfl⟩
      obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos hm).symm⟩
      refine ⟨n, ?_⟩
      simp only
      have heq : (subrank (kronPowNat S n) : ℕ) = pF.subrank (a ^ (n + 1)) := by
        rw [ha, subrank_kronPowNat_eq_abstract hk S n]
      rw [heq]
      push_cast
      ring_nf
  unfold asympSubrank
  rw [hset, StrassenPreorder.asympSubrank]

/-- **Abstract subrank power law** (Fekete; Strassen 1988).  For `1 ≤_P a` and any
`m ≥ 1`, `pF.asympSubrank (a^m) = pF.asympSubrank a ^ m`.

Proof via the Fekete limit `asympSubrank_eq_tendsto` (`RankSubrank.lean:932`):
`subrank(a^k)^{1/k} → Q := pF.asympSubrank a`, and the subsequence identity
`subrank((a^m)^k)^{1/k} = (subrank(a^{mk})^{1/(mk)})^m` gives
`subrank((a^m)^k)^{1/k} → Q^m`; uniqueness of limits closes it. -/
lemma asympSubrank_pow_abstract {a : TensorClass F k}
    (pF : StrassenPreorder (TensorClass F k)) (ha : pF.rel 1 a) (m : ℕ) (hm : 1 ≤ m) :
    pF.asympSubrank (a ^ m) = pF.asympSubrank a ^ m := by
  have hmpos : 0 < m := hm
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hmpos
  -- `1 ≤_P a^m`.
  have ham : pF.rel 1 (a ^ m) := pF.one_le_pow_of_one_le ha m hmpos
  -- Fekete limit for `a^m`: `subrank((a^m)^k)^{1/k} → asympSubrank (a^m)`.
  have htend_am : Filter.Tendsto
      (fun k : ℕ => (pF.subrank ((a ^ m) ^ k) : ℝ) ^ (1 / (k : ℝ)))
      Filter.atTop (nhds (pF.asympSubrank (a ^ m))) :=
    StrassenPreorder.asympSubrank_eq_tendsto pF ham
  -- Fekete limit for `a` along the subsequence `k ↦ m*k`.
  have htend_a : Filter.Tendsto
      (fun k : ℕ => (pF.subrank (a ^ k) : ℝ) ^ (1 / (k : ℝ)))
      Filter.atTop (nhds (pF.asympSubrank a)) :=
    StrassenPreorder.asympSubrank_eq_tendsto pF ha
  have hsub_atTop : Filter.Tendsto (fun k : ℕ => m * k) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop_of_monotone
    · intro x y hxy; exact Nat.mul_le_mul_left m hxy
    · intro b; exact ⟨b, Nat.le_mul_of_pos_left b hmpos⟩
  have htend_a_sub : Filter.Tendsto
      (fun k : ℕ => (pF.subrank (a ^ (m * k)) : ℝ) ^ (1 / ((m * k : ℕ) : ℝ)))
      Filter.atTop (nhds (pF.asympSubrank a)) :=
    htend_a.comp hsub_atTop
  -- `subrank((a^m)^k)^{1/k} = (subrank(a^{mk})^{1/(mk)})^m` eventually.
  have htend_am' : Filter.Tendsto
      (fun k : ℕ => (pF.subrank ((a ^ m) ^ k) : ℝ) ^ (1 / (k : ℝ)))
      Filter.atTop (nhds (pF.asympSubrank a ^ m)) := by
    rw [show (pF.asympSubrank a) ^ m = (pF.asympSubrank a) ^ (m : ℝ) by
          rw [Real.rpow_natCast]]
    apply Filter.Tendsto.congr' _
      ((htend_a_sub).rpow_const (Or.inr (by exact_mod_cast Nat.zero_le m)))
    filter_upwards [Filter.eventually_gt_atTop 0] with k hk
    have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hk
    have hmk_ne : ((m * k : ℕ) : ℝ) ≠ 0 := by
      push_cast; exact mul_ne_zero hm_ne hk_ne
    -- LHS: `(subrank(a^{mk})^{1/(mk)})^m = subrank(a^{mk})^{m/(mk)} = subrank(a^{mk})^{1/k}`.
    -- RHS: `subrank((a^m)^k)^{1/k} = subrank(a^{mk})^{1/k}` since `(a^m)^k = a^{mk}`.
    rw [← pow_mul, ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    push_cast
    field_simp
  -- Uniqueness of limits.
  exact tendsto_nhds_unique htend_am htend_am'

/-- For nonzero `S`, the abstract `pF.asympSubrank (mk S)` is `≤` the concrete
`asympSubrank S`.  Immediate corollary of the EQUALITY `asympSubrank_eq_abstract`
(the corrected concrete def removed the off-by-one that previously made only this
directional bound provable). -/
lemma abstract_asympSubrank_le_concrete (hk : 2 ≤ k) {d : Fin k → ℕ+} (S : KTensor F d)
    (_hS : TensorClass.mk ⟨d, S⟩ ≠ (0 : TensorClass F k)) :
    (tensorStrassenPreorder (F := F) hk).asympSubrank (TensorClass.mk ⟨d, S⟩)
      ≤ asympSubrank S :=
  (asympSubrank_eq_abstract hk S).ge

/-! ## Nontriviality and the abstract spectrum nonemptiness. -/

/-- `TensorClass F k` is nontrivial: `1 ≠ 0`, because `pF.nat_compat` would force
`1 ≤ 0` otherwise. -/
lemma tensorClass_nontrivial (hk : 2 ≤ k) : Nontrivial (TensorClass F k) := by
  refine ⟨1, 0, ?_⟩
  intro h
  -- `1 = 0` in the class would give `pF.rel ((1:ℕ):TC) ((0:ℕ):TC)`, i.e. `1 ≤ 0`.
  have hrel : (tensorStrassenPreorder (F := F) hk).rel
      (((1 : ℕ) : TensorClass F k)) (((0 : ℕ) : TensorClass F k)) := by
    simp only [Nat.cast_one, Nat.cast_zero]
    rw [h]
    exact (tensorStrassenPreorder (F := F) hk).refl 0
  have := (nat_compat_relClass (F := F) hk 1 0).mpr hrel
  omega

/-- **Gapped concrete-inf bridge** — for `S` whose class `mk ⟨d, S⟩` is gapped, the
infimum of `φ(S)` over *concrete* spectral points `φ : SpectralPoint k F` is `≤`
the abstract `pF.asympSubrank (mk S)`.

For every abstract spectral point `ψ : AsymptoticSpectrum pF`, the concrete point
`ofAbstractSpectralPoint hk ψ` evaluates to `ψ (mk S)` on `S`, so the concrete inf
is below every abstract value, hence below the abstract inf, which equals
`pF.asympSubrank (mk S)` by Strassen-1988 duality (`asympSubrank_eq_iInf_spectrum`,
requiring gappedness). -/
lemma iInf_concrete_le_abstract_asympSubrank (hk : 2 ≤ k) {d : Fin k → ℕ+} (S : KTensor F d)
    (hgap : (tensorStrassenPreorder (F := F) hk).IsGapped (TensorClass.mk ⟨d, S⟩)) :
    (⨅ φ : SpectralPoint k F, φ.toFun S)
      ≤ (tensorStrassenPreorder (F := F) hk).asympSubrank (TensorClass.mk ⟨d, S⟩) := by
  classical
  set pF := tensorStrassenPreorder (F := F) hk with hpF
  haveI : Nontrivial (TensorClass F k) := tensorClass_nontrivial hk
  haveI : Nonempty (AsymptoticSpectrum pF) := AsymptoticSpectrum.nonempty pF
  -- The concrete inf is BddBelow (by `0`) and the family nonempty.
  have hnonneg : ∀ (φ : SpectralPoint k F) {d' : Fin k → ℕ+} (T : KTensor F d'),
      (0 : ℝ) ≤ φ.toFun T := by
    intro φ d' T
    have hmono := φ.mono (zeroT : KTensor F (fun _ => (1 : ℕ+))) T (zeroT_restricts T)
    rwa [SpectralPoint.toFun_zeroT φ] at hmono
  have hbddSpec : BddBelow (Set.range (fun φ : SpectralPoint k F => φ.toFun S)) := by
    refine ⟨0, ?_⟩
    rintro y ⟨φ, rfl⟩
    exact hnonneg φ S
  -- Concrete inf ≤ each abstract value.
  have hle_each : ∀ ψ : AsymptoticSpectrum pF,
      (⨅ φ : SpectralPoint k F, φ.toFun S)
        ≤ AsymptoticSpectrum.eval pF (TensorClass.mk ⟨d, S⟩) ψ := by
    intro ψ
    -- `ofAbstractSpectralPoint (K := F) hk ψ` is a concrete point with value `ψ (mk S)` on `S`.
    have hval : (ofAbstractSpectralPoint (K := F) hk ψ).toFun S
        = AsymptoticSpectrum.eval pF (TensorClass.mk ⟨d, S⟩) ψ := rfl
    calc (⨅ φ : SpectralPoint k F, φ.toFun S)
        ≤ (ofAbstractSpectralPoint (K := F) hk ψ).toFun S :=
          ciInf_le hbddSpec _
      _ = AsymptoticSpectrum.eval pF (TensorClass.mk ⟨d, S⟩) ψ := hval
  -- Combine: concrete inf ≤ abstract inf = abstract asympSubrank.
  rw [StrassenPreorder.asympSubrank_eq_iInf_spectrum pF (TensorClass.mk ⟨d, S⟩) hgap
    (tensor_strong_archimedean (F := F) hk)]
  exact le_ciInf hle_each

/-- The concrete `asympSubrank` is nonnegative (`sSup` of a nonnegative,
bounded-above set). -/
lemma asympSubrank_nonneg' (hk : 2 ≤ k) {d : Fin k → ℕ+} (S : KTensor F d) :
    (0 : ℝ) ≤ asympSubrank S := by
  classical
  unfold asympSubrank
  have hmem :
      ((subrank (kronPowNat S 0) : ℝ) ^ ((1 : ℝ) / (((0 : ℕ) : ℝ) + 1)))
        ∈ Set.range (fun n : ℕ =>
            (subrank (kronPowNat S n) : ℝ) ^ ((1 : ℝ) / ((n : ℝ) + 1))) :=
    ⟨0, rfl⟩
  have hnonneg : (0 : ℝ) ≤ (subrank (kronPowNat S 0) : ℝ) ^ ((1 : ℝ) / (((0 : ℕ) : ℝ) + 1)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact le_trans hnonneg (le_csSup (concrete_asympSubrankSet_bddAbove hk S) hmem)

/-- The inf over concrete spectral points is below `asympSubrank S` for gapped `S`,
combining the gapped concrete-inf bridge with the directional `asympSubrank` bridge.
For the zero tensor (also gapped) both sides reduce to `0`. -/
lemma iInf_concrete_le_asympSubrank (hk : 2 ≤ k) {d : Fin k → ℕ+} (S : KTensor F d)
    (hgap : (tensorStrassenPreorder (F := F) hk).IsGapped (TensorClass.mk ⟨d, S⟩)) :
    (⨅ φ : SpectralPoint k F, φ.toFun S) ≤ asympSubrank S := by
  by_cases hS : TensorClass.mk ⟨d, S⟩ = (0 : TensorClass F k)
  · -- Zero tensor: `⨅ φ φ(S) ≤ φ₀(S) = φ₀(0) = 0 ≤ asympSubrank S`.
    haveI : Nontrivial (TensorClass F k) := tensorClass_nontrivial hk
    set pF := tensorStrassenPreorder (F := F) hk with hpF
    haveI : Nonempty (AsymptoticSpectrum pF) := AsymptoticSpectrum.nonempty pF
    obtain ⟨ψ⟩ := (inferInstance : Nonempty (AsymptoticSpectrum pF))
    have hbddSpec : BddBelow (Set.range (fun φ : SpectralPoint k F => φ.toFun S)) := by
      refine ⟨0, ?_⟩
      rintro y ⟨φ, rfl⟩
      have hmono := φ.mono (zeroT : KTensor F (fun _ => (1 : ℕ+))) S (zeroT_restricts S)
      rwa [SpectralPoint.toFun_zeroT φ] at hmono
    -- `(ofAbstractSpectralPoint (K:=F) hk ψ).toFun S = ψ (mk S) = ψ 0 = 0`.
    have hval0 : (ofAbstractSpectralPoint (K := F) hk ψ).toFun S = 0 := by
      change ψ.toFun (TensorClass.mk ⟨d, S⟩) = 0
      rw [hS, ψ.map_zero]
    calc (⨅ φ : SpectralPoint k F, φ.toFun S)
        ≤ (ofAbstractSpectralPoint (K := F) hk ψ).toFun S := ciInf_le hbddSpec _
      _ = 0 := hval0
      _ ≤ asympSubrank S := asympSubrank_nonneg' hk S
  · exact le_trans (iInf_concrete_le_abstract_asympSubrank hk S hgap)
      (abstract_asympSubrank_le_concrete hk S hS)

end Semicontinuity
