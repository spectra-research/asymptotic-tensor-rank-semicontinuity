/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.MultigraphVC
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.FieldInvariance
import AsymptoticTensorRankSemicontinuity.SpectrumWellOrdered

/-!
# Corollary 3.5 headline

Source (semicontinuity tex:982-996), quoted verbatim:

Proof: q_ij := subrank_{i,j}(T). Then T^{⊠ k(k-1)/2} ≥ ⊠_{i<j} ⟨q_ij⟩
(ingredient 1). asympSubrank(⊠⟨q_ij⟩) = min_{∅≠I⊊[k]} ∏_{i∈I,j∉I} q_ij
(weighted VC formula). Field-invariance (Strassen 1988 Thm 3.10): may assume F
infinite. By Thm 3.2 then min_I ∏ q_ij ≥ min_I flatRank_I. Take
k(k-1)/2-th root.

The statement below is copied from `MaxRankBound.lean:5050-5054` with a fresh
name.  As currently encoded, the `⨅ I ∈ S, ...` form ranges over all finsets
before restricting by membership in `S`; the excluded empty cut contributes an
empty inner infimum, which is `0` in `ℝ`.  Thus this exact Lean statement follows
from nonnegativity of `asympSubrank`.
-/

open Finset BigOperators

namespace Semicontinuity

universe u

variable {F : Type u} [Field F]


/-- **Corollary 3.5, genuine non-vacuous minimum form.**

This is the honest `Finset.inf'` formulation: the left side is the minimum of
`flatRank T I` over the nonempty finset `MinCut.admissibleCuts k`, not an
`iInf` over all finsets with an empty indexed summand. -/
theorem minCut_flatRank_le_asympSubrank_of_infinite {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (hk : 3 ≤ k)
    (hbig : ∀ I : Finset (Fin k), ((flatRank T I : ℕ) : Cardinal) < Cardinal.mk F)
    [Infinite F] :
    ((MinCut.admissibleCuts k).inf' (MinCut.admissibleCuts_nonempty (by omega))
        (fun I => ((flatRank T I : ℝ)) ) : ℝ) ^
      ((2 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)))
        ≤ asympSubrank T := by
  classical
  haveI : NeZero k := ⟨by omega⟩
  let q : Fin k → Fin k → ℕ := fun i j => subrankPair T i j
  let mF : ℝ :=
    (MinCut.admissibleCuts k).inf' (MinCut.admissibleCuts_nonempty (by omega : 2 ≤ k))
      (fun I => ((flatRank T I : ℝ)))
  have hflat_le_cut :
      ∀ I ∈ MinCut.admissibleCuts k, flatRank T I ≤ MinCut.cutProduct q I := by
    intro I hI
    have hI' : I.Nonempty ∧ I ≠ Finset.univ := (MinCut.mem_admissibleCuts).1 hI
    have hcard : 1 ≤ I.card := Finset.card_pos.mpr hI'.1
    have hcard' : I.card ≤ k - 1 := by
      have hlt : I.card < k := by
        have := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hI'.2)
        simpa [Finset.card_univ, Fintype.card_fin] using this
      omega
    simpa [q, MinCut.cutProduct] using
      subrankPair_prod_ge_flatRank T I hcard hcard' (hbig I)
  have hmin_flat_le_mincut :
      mF ≤ ((MinCut.minCut q (by omega : 2 ≤ k) : ℕ) : ℝ) := by
    rw [MinCut.minCut_real_eq_inf' q (by omega : 2 ≤ k)]
    change
      (MinCut.admissibleCuts k).inf' (MinCut.admissibleCuts_nonempty (by omega : 2 ≤ k))
          (fun I => ((flatRank T I : ℝ)))
        ≤
      (MinCut.admissibleCuts k).inf' (MinCut.admissibleCuts_nonempty (by omega : 2 ≤ k))
          (fun I => ((MinCut.cutProduct q I : ℕ) : ℝ))
    apply Finset.le_inf'
    intro I hI
    exact le_trans (Finset.inf'_le _ hI) (by exact_mod_cast hflat_le_cut I hI)
  have hmincut_root_le :
      ((MinCut.minCut q (by omega : 2 ≤ k) : ℕ) : ℝ) ^
          ((2 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)))
        ≤ asympSubrank T := by
    -- Non-vacuous Corollary 3.5 chain (tex:983-996); no `iInf`/empty-cut convention.
    have hk2 : 2 ≤ k := by omega
    -- Root exponent abbreviation and positivity facts.
    set c : ℝ := (2 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)) with hc
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 2 ≤ k)
    have hden : (0 : ℝ) < (k : ℝ) * ((k : ℝ) - 1) := by nlinarith
    have hc_pos : 0 < c := by rw [hc]; positivity
    -- Case split: either every off-diagonal `subrankPair` is positive, or some is `0`.
    by_cases hall : ∀ i j : Fin k, i ≠ j → 0 < subrankPair T i j
    · -- All positive: run the weighted Vrana-Christandl + restriction chain.
      have hq : ∀ i j, i ≠ j → 1 ≤ q i j := fun i j hij => hall i j hij
      have hsym : ∀ i j, q i j = q j i := fun i j => subrankPair_comm T i j
      -- `minCut(q) ≤ asympSubrank(pairUnitKronQ F q)`  (weightedVC, tex:987-990).
      have hweighted :
          ((MinCut.minCut q (by omega : 2 ≤ k) : ℕ) : ℝ) ≤
            asympSubrank (pairUnitKronQ F q).2 :=
        weightedVC (F := F) q (by omega : 3 ≤ k) hsym hq
      -- `(pairUnitKronQ F q).2 ≤ₜ kronPowNat T (N-1)`, `N = (cgPairsList k).length`.
      have hrestr :
          Restricts (pairUnitKronQ F q).2 (kronPowNat T ((cgPairsList k).length - 1)) :=
        pairUnitKronQ_subrankPair_restricts_kronPow (F := F) T hk2 hall
      -- `asympSubrank(pairUnitKronQ) ≤ asympSubrank(kronPowNat T (N-1)) = asympSubrank(T)^N`.
      have hmono :
          asympSubrank (pairUnitKronQ F q).2 ≤
            asympSubrank (kronPowNat T ((cgPairsList k).length - 1)) :=
        asympSubrank_mono_restricts hk2 hrestr
      -- `T ≠ 0`: some pair-unit `⟨subrankPair⟩ ≤ₜ T` with positive rank, so `mk T ≠ 0`.
      have hTne : TensorClass.mk ⟨d, T⟩ ≠ (0 : TensorClass F k) := by
        have h01 : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := by
          intro h; simpa using congrArg Fin.val h
        exact mk_ne_zero_of_subrankPair_pos T h01 (hall _ _ h01)
      have hpowlaw :
          asympSubrank (kronPowNat T ((cgPairsList k).length - 1)) =
            asympSubrank T ^ ((cgPairsList k).length - 1 + 1) :=
        asympSubrank_kronPowNat hk2 T hTne _
      -- `N - 1 + 1 = N = k(k-1)/2`.
      have hN : (cgPairsList k).length - 1 + 1 = (cgPairsList k).length := by
        have hge1 : 1 ≤ (cgPairsList k).length := by
          rw [cgPairsList_length]
          have h2 : 2 ≤ k * (k - 1) := by
            have h1 : 1 ≤ k - 1 := by omega
            calc 2 = 2 * 1 := by ring
              _ ≤ k * (k - 1) := Nat.mul_le_mul hk2 h1
          omega
        omega
      rw [hN] at hpowlaw
      -- `minCut(q) ≤ asympSubrank(T)^N`, take the `c = 2/(k(k-1))`-th root.
      have hchain :
          ((MinCut.minCut q (by omega : 2 ≤ k) : ℕ) : ℝ) ≤
            asympSubrank T ^ (cgPairsList k).length :=
        le_trans hweighted (hpowlaw ▸ hmono)
      have hasr_nn : 0 ≤ asympSubrank T := asympSubrank_nonneg' hk2 T
      -- `minCut^c ≤ (asympSubrank T ^ N)^c = asympSubrank T ^ (N·c) = asympSubrank T`.
      have hroot :
          ((MinCut.minCut q (by omega : 2 ≤ k) : ℕ) : ℝ) ^ c ≤
            (asympSubrank T ^ (cgPairsList k).length) ^ c := by
        apply Real.rpow_le_rpow (by positivity) hchain hc_pos.le
      refine le_trans hroot ?_
      -- `(asympSubrank T ^ N)^c = asympSubrank T`, since `N · c = 1`.
      rw [← Real.rpow_natCast (asympSubrank T) (cgPairsList k).length,
        ← Real.rpow_mul hasr_nn]
      have hNc : ((cgPairsList k).length : ℝ) * c = 1 := by
        -- `2 * length = k(k-1)` over `ℕ`, hence `(length : ℝ) = k(k-1)/2`.
        have h2N : 2 * (cgPairsList k).length = k * (k - 1) := by
          rw [cgPairsList_length]
          have heven : 2 ∣ k * (k - 1) := by
            rcases Nat.even_or_odd k with he | ho
            · exact Dvd.dvd.mul_right he.two_dvd _
            · rcases ho with ⟨m, rfl⟩
              have : (2 * m + 1 - 1) = 2 * m := by omega
              rw [this]; exact Dvd.dvd.mul_left ⟨m, rfl⟩ _
          omega
        have hNr : ((cgPairsList k).length : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
          have : (2 : ℝ) * ((cgPairsList k).length : ℝ) = (k : ℝ) * ((k : ℝ) - 1) := by
            have := congrArg (Nat.cast : ℕ → ℝ) h2N
            push_cast [Nat.cast_sub (by omega : 1 ≤ k)] at this
            linarith [this]
          linarith
        rw [hc, hNr]
        have hk1 : (k : ℝ) - 1 ≠ 0 := by
          have : (2 : ℝ) ≤ (k : ℝ) := hkR; intro h; nlinarith
        have hkne : (k : ℝ) ≠ 0 := by
          have : (2 : ℝ) ≤ (k : ℝ) := hkR; intro h; nlinarith
        field_simp
      rw [hNc, Real.rpow_one]
    · -- Some off-diagonal pair is `0`: then `minCut q = 0`, so the root is `0`.
      push_neg at hall
      obtain ⟨i₀, j₀, hij₀, hzero⟩ := hall
      have hzero' : q i₀ j₀ = 0 := Nat.le_zero.mp hzero
      -- The singleton cut `{i₀}` is admissible and its product contains the `0` factor.
      have hmem : ({i₀} : Finset (Fin k)).Nonempty ∧ ({i₀} : Finset (Fin k)) ≠ Finset.univ := by
        refine ⟨Finset.singleton_nonempty _, ?_⟩
        intro h
        have hjmem : j₀ ∈ ({i₀} : Finset (Fin k)) := h ▸ Finset.mem_univ _
        rw [Finset.mem_singleton] at hjmem
        exact hij₀ hjmem.symm
      have hcut0 : MinCut.cutProduct q {i₀} = 0 := by
        unfold MinCut.cutProduct
        apply Finset.prod_eq_zero (i := (i₀, j₀))
        · rw [Finset.mem_product, Finset.mem_singleton, Finset.mem_sdiff,
            Finset.mem_singleton]
          exact ⟨rfl, Finset.mem_univ _, fun h => hij₀ h.symm⟩
        · exact hzero'
      have hmc0 : MinCut.minCut q (by omega : 2 ≤ k) = 0 :=
        Nat.le_zero.mp (hcut0 ▸ MinCut.minCut_le_cutProduct q (by omega : 2 ≤ k) hmem)
      rw [hmc0]
      simp only [Nat.cast_zero]
      rw [Real.zero_rpow (ne_of_gt hc_pos)]
      exact asympSubrank_nonneg' hk2 T
  have hmF_nonneg : 0 ≤ mF := by
    rw [show mF =
        (MinCut.admissibleCuts k).inf' (MinCut.admissibleCuts_nonempty (by omega : 2 ≤ k))
          (fun I => ((flatRank T I : ℝ))) from rfl]
    rw [Finset.le_inf'_iff]
    intro I _; positivity
  have hroot_mono :
      mF ^ ((2 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)))
        ≤ ((MinCut.minCut q (by omega : 2 ≤ k) : ℕ) : ℝ) ^
          ((2 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1))) := by
    apply Real.rpow_le_rpow hmF_nonneg hmin_flat_le_mincut
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 2 ≤ k)
    have hden : (0 : ℝ) < (k : ℝ) * ((k : ℝ) - 1) := by nlinarith
    positivity
  exact hroot_mono.trans hmincut_root_le


/-- **Corollary 3.5 over an arbitrary field** (semicontinuity tex:982-996).

Base-change to the algebraic closure, apply the infinite-field theorem
`minCut_flatRank_le_asympSubrank_of_infinite`, then descend the two sides using flat-rank invariance
(`flatRank_baseChange_eq`) and Strassen 1988 field invariance of asymptotic
subrank (`asympSubrank_baseChange_general`, tex:991-992). -/
theorem minCut_flatRank_le_asympSubrank_of_isGapped {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (hk : 3 ≤ k)
    (hgap :
      haveI : NeZero k := ⟨by omega⟩
      (tensorStrassenPreorder (F := F) (by omega : 2 ≤ k)).IsGapped
        (TensorClass.mk ⟨d, T⟩)) :
    ((MinCut.admissibleCuts k).inf' (MinCut.admissibleCuts_nonempty (by omega))
        (fun I => (flatRank T I : ℝ)))
      ^ ((2 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)))
        ≤ asympSubrank T := by
  classical
  haveI : NeZero k := ⟨by omega⟩
  set Tbar : KTensor (AlgebraicClosure F) d :=
    T.baseChange (K := AlgebraicClosure F) with hTbar
  have hbig :
      ∀ I : Finset (Fin k),
        ((flatRank Tbar I : ℕ) : Cardinal) < Cardinal.mk (AlgebraicClosure F) := by
    intro I
    exact flatRank_lt_card_of_infinite (F := AlgebraicClosure F) Tbar I
  have hbar :
      ((MinCut.admissibleCuts k).inf' (MinCut.admissibleCuts_nonempty (by omega))
          (fun I => (flatRank Tbar I : ℝ)))
        ^ ((2 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)))
          ≤ asympSubrank Tbar :=
    minCut_flatRank_le_asympSubrank_of_infinite (F := AlgebraicClosure F) Tbar hk hbig
  have hinf :
      (MinCut.admissibleCuts k).inf' (MinCut.admissibleCuts_nonempty (by omega : 2 ≤ k))
          (fun I => (flatRank Tbar I : ℝ))
        =
      (MinCut.admissibleCuts k).inf' (MinCut.admissibleCuts_nonempty (by omega : 2 ≤ k))
          (fun I => (flatRank T I : ℝ)) := by
    subst Tbar
    apply Finset.inf'_congr (MinCut.admissibleCuts_nonempty (by omega : 2 ≤ k)) rfl
    intro I _hI
    exact_mod_cast (flatRank_baseChange_eq (K := AlgebraicClosure F) T I)
  have hasr : asympSubrank Tbar = asympSubrank T := by
    subst Tbar
    exact asympSubrank_baseChange_general
      (F := F) (K := AlgebraicClosure F) (by omega : 2 ≤ k) T hgap
  rw [hinf, hasr] at hbar
  exact hbar


private lemma isGapped_of_all_flatRank_cut_ge_two {k : ℕ} [NeZero k]
    {d : Fin k → ℕ+} (T : KTensor F d) (hk : 2 ≤ k)
    (hall : ∀ S : Finset (Fin k), S.Nonempty → S ≠ Finset.univ → 2 ≤ flatRank T S) :
    (tensorStrassenPreorder (F := F) hk).IsGapped (TensorClass.mk ⟨d, T⟩) := by
  classical
  obtain ⟨n, hres⟩ :=
    exists_unitTwo_restricts_of_all_flatRank_cut_ge_two (F := F) hk T hall
  refine Or.inl ⟨n + 1, Nat.succ_pos n, ?_⟩
  rw [mkPow T n]
  have htwo :
      (2 : TensorClass F k) =
        TensorClass.mk ⟨_, unitTensor F (k := k) (2 : ℕ+)⟩ := by
    have h2cast : (2 : TensorClass F k) = ((2 : ℕ) : TensorClass F k) := by
      norm_cast
    rw [h2cast, natCast_eq_unitClass, unitClass, dif_pos (by norm_num : 0 < 2)]
    rfl
  rw [htwo]
  change Restricts (unitTensor F (k := k) (2 : ℕ+)) (kronPowNat T n)
  exact hres

private lemma flatRank_singleton_zero_le_subrank_k2 {d : Fin 2 → ℕ+}
    (T : KTensor F d) :
    flatRank T ({0} : Finset (Fin 2)) ≤ subrank T := by
  classical
  by_cases hr0 : flatRank T ({0} : Finset (Fin 2)) = 0
  · rw [hr0]
    exact Nat.zero_le _
  · have hrpos : 0 < flatRank T ({0} : Finset (Fin 2)) := Nat.pos_of_ne_zero hr0
    have hres :
        Restricts
          (unitTensor F (k := 2)
            ⟨flatRank T ({0} : Finset (Fin 2)), hrpos⟩) T :=
      (tensor_restricts_equiv_unitTensor_k2 (F := F) T
        (r := flatRank T ({0} : Finset (Fin 2))) hrpos rfl).1
    have hmem :
        flatRank T ({0} : Finset (Fin 2)) ∈
          { r : ℕ | ∃ hr : 0 < r,
            Restricts (unitTensor F (k := 2) ⟨r, hr⟩) T } :=
      ⟨hrpos, hres⟩
    exact le_csSup
      (subrank_set_bddAbove' (F := F) (k := 2)
        (0 : Fin 2) (1 : Fin 2) (by decide) T) hmem

private lemma subrank_le_asympSubrank {k : ℕ} [NeZero k]
    (hk : 2 ≤ k) {d : Fin k → ℕ+} (T : KTensor F d) :
    (subrank T : ℝ) ≤ asympSubrank T := by
  classical
  unfold asympSubrank
  have hmem :
      (subrank (kronPowNat T 0) : ℝ) ^
          ((1 : ℝ) / (((0 : ℕ) : ℝ) + 1)) ∈
        Set.range (fun n : ℕ =>
          (subrank (kronPowNat T n) : ℝ) ^ ((1 : ℝ) / ((n : ℝ) + 1))) :=
    ⟨0, rfl⟩
  calc
    (subrank T : ℝ)
        = (subrank (kronPowNat T 0) : ℝ) ^
            ((1 : ℝ) / (((0 : ℕ) : ℝ) + 1)) := by
          simp [kronPowNat, Real.rpow_one]
    _ ≤ sSup (Set.range (fun n : ℕ =>
          (subrank (kronPowNat T n) : ℝ) ^ ((1 : ℝ) / ((n : ℝ) + 1)))) :=
        le_csSup (concrete_asympSubrankSet_bddAbove hk T) hmem

/-- **Corollary 3.5 over an arbitrary field, unconditionally.**

This is the paper-faithful headline: no infinite-field hypothesis, no
`IsGapped` hypothesis, and no largeness hypothesis on the field. -/
theorem minCut_flatRank_le_asympSubrank {k : ℕ} {d : Fin k → ℕ+} (T : KTensor F d) (hk : 2 ≤ k) :
    ((MinCut.admissibleCuts k).inf' (MinCut.admissibleCuts_nonempty (by omega))
        (fun I => (flatRank T I : ℝ))) ^ ((2 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)))
      ≤ asympSubrank T := by
  classical
  rcases Nat.lt_or_ge k 3 with hklt | hkge
  · have hk_eq : k = 2 := by omega
    subst hk_eq
    haveI : NeZero 2 := ⟨by norm_num⟩
    have hmem0 : ({0} : Finset (Fin 2)) ∈ MinCut.admissibleCuts 2 := by
      rw [MinCut.mem_admissibleCuts]
      refine ⟨Finset.singleton_nonempty _, ?_⟩
      intro h
      have h1 : (1 : Fin 2) ∈ ({0} : Finset (Fin 2)) := by
        rw [h]
        exact Finset.mem_univ _
      rw [Finset.mem_singleton] at h1
      have hval := congrArg Fin.val h1
      norm_num at hval
    have hinf_le :
        (MinCut.admissibleCuts 2).inf'
            (MinCut.admissibleCuts_nonempty (by norm_num : 2 ≤ 2))
            (fun I => (flatRank T I : ℝ))
          ≤ (flatRank T ({0} : Finset (Fin 2)) : ℝ) :=
      Finset.inf'_le _ hmem0
    have hflat_sub :
        (flatRank T ({0} : Finset (Fin 2)) : ℝ) ≤ (subrank T : ℝ) := by
      exact_mod_cast flatRank_singleton_zero_le_subrank_k2 (F := F) T
    have hsub_asymp : (subrank T : ℝ) ≤ asympSubrank T :=
      subrank_le_asympSubrank (F := F) (k := 2) (by norm_num : 2 ≤ 2) T
    have hexp :
        (2 : ℝ) / (((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) - 1)) = 1 := by
      norm_num
    rw [hexp, Real.rpow_one]
    exact hinf_le.trans (hflat_sub.trans hsub_asymp)
  haveI : NeZero k := ⟨by omega⟩
  have hk2 : 2 ≤ k := hk
  by_cases hall : ∀ S : Finset (Fin k), S.Nonempty → S ≠ Finset.univ → 2 ≤ flatRank T S
  · have hgap :
        (tensorStrassenPreorder (F := F) hk2).IsGapped (TensorClass.mk ⟨d, T⟩) :=
      isGapped_of_all_flatRank_cut_ge_two (F := F) T hk2 hall
    exact minCut_flatRank_le_asympSubrank_of_isGapped T hkge hgap
  · push_neg at hall
    obtain ⟨S₀, hS₀ne, hS₀univ, hS₀not⟩ := hall
    have hS₀le : flatRank T S₀ ≤ 1 := by omega
    have hS₀mem : S₀ ∈ MinCut.admissibleCuts k := by
      rw [MinCut.mem_admissibleCuts]
      exact ⟨hS₀ne, hS₀univ⟩
    set m : ℝ :=
      (MinCut.admissibleCuts k).inf' (MinCut.admissibleCuts_nonempty (by omega : 2 ≤ k))
        (fun I => (flatRank T I : ℝ)) with hm
    set c : ℝ := (2 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)) with hc
    change m ^ c ≤ asympSubrank T
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    have hden : (0 : ℝ) < (k : ℝ) * ((k : ℝ) - 1) := by nlinarith
    have hc_pos : 0 < c := by
      rw [hc]
      exact div_pos (by norm_num) hden
    have hc_nonneg : 0 ≤ c := le_of_lt hc_pos
    have hm_nonneg : 0 ≤ m := by
      rw [hm, Finset.le_inf'_iff]
      intro I _hI
      positivity
    have hm_le_one : m ≤ 1 := by
      calc
        m ≤ (flatRank T S₀ : ℝ) := by
          rw [hm]
          exact Finset.inf'_le _ hS₀mem
        _ ≤ 1 := by exact_mod_cast hS₀le
    have hlhs_le_one : m ^ c ≤ 1 := by
      calc
        m ^ c ≤ (1 : ℝ) ^ c := Real.rpow_le_rpow hm_nonneg hm_le_one hc_nonneg
        _ = 1 := Real.one_rpow c
    by_cases hTne : TensorClass.mk ⟨d, T⟩ ≠ (0 : TensorClass F k)
    · exact hlhs_le_one.trans (one_le_asympSubrank_of_ne_zero hk2 T hTne)
    · push_neg at hTne
      have hTequiv : T ∼ₜ (zeroT : KTensor F (fun _ => (1 : ℕ+))) :=
        Quotient.exact (hTne.trans TensorClass.zero_def)
      have hTzero : T = (0 : KTensor F d) := by
        obtain ⟨A, hA⟩ := hTequiv.1
        funext idx
        rw [hA idx]
        apply Finset.sum_eq_zero
        intro z _hz
        simp [zeroT]
      have hflat0 : flatRank T S₀ = 0 := by
        subst hTzero
        unfold flatRank
        have hmat : flattenMatrix (0 : KTensor F d) S₀ = 0 := by
          funext row col
          simp [flattenMatrix]
        rw [hmat, Matrix.rank_zero]
      have hm_le_zero : m ≤ 0 := by
        calc
          m ≤ (flatRank T S₀ : ℝ) := by
            rw [hm]
            exact Finset.inf'_le _ hS₀mem
          _ = 0 := by rw [hflat0]; norm_num
      have hm_eq_zero : m = 0 := le_antisymm hm_le_zero hm_nonneg
      have hlhs_zero : m ^ c = 0 := by
        rw [hm_eq_zero, Real.zero_rpow (ne_of_gt hc_pos)]
      rw [hlhs_zero]
      exact asympSubrank_nonneg' hk2 T

end Semicontinuity

