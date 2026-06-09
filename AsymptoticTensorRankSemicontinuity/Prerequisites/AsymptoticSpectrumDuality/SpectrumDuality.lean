/-
Copyright (c) 2024 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.AsymptoticSpectrumDuality.AsymptoticSpectrum

/-!
# Duality between Asymptotic Rank/Subrank and the Spectrum

This file proves the main duality theorems:
- `asympRank(a) = max_{φ ∈ X} φ(a)` (asymptotic rank equals pointwise maximum over spectrum)
- `asympSubrank(a) = min_{φ ∈ X} φ(a)` for gapped elements

## Main Results

* `asympRank_eq_iSup_spectrum` - Asymptotic rank equals supremum over spectral evaluations
* `asympRank_eq_max_spectrum` - For compact spectrum, this supremum is achieved (max exists)
* `asympSubrank_eq_iInf_spectrum` - For gapped elements, asymptotic subrank equals infimum
* `asympSubrank_eq_min_spectrum` - For compact spectrum and gapped elements, min exists

## References

* survey.tex, Theorems th:asymprank-duality and th:asympsubrank-duality
-/

namespace AsymptoticSpectrumDuality

open scoped NNReal ENNReal Topology

variable {S : Type*} [CommSemiring S]

namespace StrassenPreorder

variable (p : StrassenPreorder S)

/-! ### Asymptotic Rank = Max over Spectrum

We use the ℝ-valued asympRank and asympSubrank from RankSubrank.lean. -/

/-- For any spectral point φ, we have φ(a) ≤ asympRank(a).
    This follows from φ being a homomorphism: φ(a)^n = φ(a^n) ≤ rank(a^n),
    so φ(a) ≤ rank(a^n)^{1/n} for all n. -/
theorem spectralPoint_le_asympRank (φ : AsymptoticSpectrum p) (a : S) :
    AsymptoticSpectrum.eval p a φ ≤ p.asympRank a := by
  -- The asymptotic rank is inf over n ≥ 1 of rank(a^n)^{1/n}
  -- We need to show: φ(a) ≤ inf { rank(a^n)^{1/n} : n ≥ 1 }
  unfold asympRank
  apply le_csInf (p.asympRankSet_nonempty a)
  intro x hx
  simp only [asympRankSet, Set.mem_image] at hx
  obtain ⟨n, hn, rfl⟩ := hx
  have hn_pos : 0 < n := Nat.one_le_iff_ne_zero.mp hn |> Nat.pos_of_ne_zero
  have hn_real_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_real_pos
  -- We have φ(a)^n = φ(a^n) ≤ rank(a^n)
  have heval := AsymptoticSpectrum.eval_pow p φ a n
  have hbound := AsymptoticSpectrum.eval_le_rank p φ (a ^ n)
  have heval_nonneg := AsymptoticSpectrum.eval_nonneg p φ a
  -- φ(a)^n ≤ rank(a^n) in ℝ
  have hpow : (AsymptoticSpectrum.eval p a φ) ^ n ≤ p.rank (a ^ n) := by
    rw [← heval]; exact hbound
  -- From x^n ≤ y we get x ≤ y^{1/n} for nonnegative x, y
  have hrank_nonneg : (0 : ℝ) ≤ p.rank (a ^ n) := Nat.cast_nonneg _
  -- φ(a) = (φ(a)^n)^{1/n}
  have hpow_eq : AsymptoticSpectrum.eval p a φ =
      ((AsymptoticSpectrum.eval p a φ) ^ n) ^ (1 / (n : ℝ)) := by
    rw [← Real.rpow_natCast (AsymptoticSpectrum.eval p a φ) n,
        ← Real.rpow_mul heval_nonneg, mul_one_div_cancel hn_ne, Real.rpow_one]
  rw [hpow_eq]
  apply Real.rpow_le_rpow (pow_nonneg heval_nonneg n) hpow
  exact div_nonneg (by norm_num) (le_of_lt hn_real_pos)

/-- The asymptotic relation can be characterized via the spectrum:
    a ≲_asymp b iff φ(a) ≤ φ(b) for all φ ∈ X.

    This is a restatement of spectral_duality_abstract in our setting. -/
theorem asympRel_iff_forall_spectrum (a b : S) :
    AsympRel p a b ↔ ∀ φ : AsymptoticSpectrum p, AsymptoticSpectrum.eval p a φ ≤
                                                  AsymptoticSpectrum.eval p b φ := by
  constructor
  · -- Forward: use asymp_implies_spectral
    intro hasym φ
    exact asymp_implies_spectral p hasym φ
  · -- Backward: use spectral_duality_abstract
    intro hspec
    rw [spectral_duality_abstract]
    intro q hpq hqmax
    -- spectralPointOfMaximal q hqmax is a SpectralPoint q
    -- We can view it as a SpectralPoint p since p ≤ q
    let φq := spectralPointOfMaximal q hqmax
    -- Construct the corresponding SpectralPoint p
    let φp : AsymptoticSpectrum p :=
      ⟨φq.toFun, φq.map_zero, φq.map_one, φq.map_add, φq.map_mul,
       fun a b hab => φq.monotone a b (hpq a b hab), φq.nonneg⟩
    -- By assumption, φp a ≤ φp b
    have h := hspec φp
    -- This is exactly spectralPointOfMaximal q hqmax a ≤ ... b
    exact h

/-- The asymptotic rank equals the supremum of φ(a) over all φ ∈ X.

    This theorem requires the hypothesis that ∃φ, φ(a) ≥ 1 (equivalently,
    sup_φ φ(a) ≥ 1). This is standard in the theory; cf. diss_ch_strassensemiring.tex
    Corollary str_rankthm which has the same hypothesis.

    Proof outline:
    1. ≤ direction: Power argument with n_k = ⌈s^k⌉ + 1
    2. ≥ direction: By spectralPoint_le_asympRank -/
theorem asympRank_eq_iSup_spectrum [Nonempty (AsymptoticSpectrum p)] (a : S)
    (ha : ∃ φ : AsymptoticSpectrum p, 1 ≤ AsymptoticSpectrum.eval p a φ) :
    p.asympRank a = ⨆ φ : AsymptoticSpectrum p, AsymptoticSpectrum.eval p a φ := by
  apply le_antisymm
  · -- asympRank a ≤ sup
    -- Strategy: For k ≥ 1, let n_k = ⌈s^k⌉ + 1 where s = sup φ(a).
    -- Then φ(a^k) = φ(a)^k ≤ s^k < n_k for all φ.
    -- By spectral duality, a^k ≲ n_k, so asympRank(a)^k ≤ n_k ≤ s^k + 2.
    -- Taking k → ∞: (s^k + 2)^{1/k} → s, so asympRank(a) ≤ s.
    set s := ⨆ φ : AsymptoticSpectrum p, AsymptoticSpectrum.eval p a φ with hs_def
    have hbdd : BddAbove (Set.range (AsymptoticSpectrum.eval p a)) := by
      use p.rank a
      intro x hx
      obtain ⟨φ, rfl⟩ := hx
      exact AsymptoticSpectrum.eval_le_rank p φ a
    have hs_nonneg : 0 ≤ s := by
      obtain ⟨φ⟩ := ‹Nonempty (AsymptoticSpectrum p)›
      calc (0 : ℝ) ≤ AsymptoticSpectrum.eval p a φ := AsymptoticSpectrum.eval_nonneg p φ a
        _ ≤ s := le_ciSup hbdd φ
    -- From hypothesis ha: ∃φ, φ(a) ≥ 1, we get s = sup φ(a) ≥ 1
    have hs_ge1 : 1 ≤ s := by
      obtain ⟨φ, hφ⟩ := ha
      calc (1 : ℝ) ≤ AsymptoticSpectrum.eval p a φ := hφ
        _ ≤ s := le_ciSup hbdd φ
    -- Key bound: For k ≥ 1, asympRank(a) ≤ (s^k + 2)^{1/k}
    have hkey : ∀ k : ℕ, k ≥ 1 → p.asympRank a ≤ (s ^ k + 2 : ℝ) ^ (1 / k : ℝ) := by
      intro k hk
      -- Define n_k = ⌈s^k⌉ + 1
      set n_k := Nat.ceil (s ^ k) + 1 with hn_k_def
      have hn_k_pos : 0 < n_k := Nat.add_one_pos _
      have hs_lt_nk : s ^ k < (n_k : ℝ) := by
        have hceil : s ^ k ≤ Nat.ceil (s ^ k) := Nat.le_ceil (s ^ k)
        have hn_k_eq : (n_k : ℝ) = Nat.ceil (s ^ k) + 1 := by exact_mod_cast rfl
        linarith
      -- For all φ: φ(a)^k ≤ s^k < n_k
      have hasymp : AsympRel p (a ^ k) (n_k : S) := by
        rw [asympRel_iff_forall_spectrum]
        intro φ
        have h1 : AsymptoticSpectrum.eval p a φ ≤ s := le_ciSup hbdd φ
        have heval_nn := AsymptoticSpectrum.eval_nonneg p φ a
        have h2 : AsymptoticSpectrum.eval p a φ ^ k ≤ s ^ k := by
          gcongr
        simp only [AsymptoticSpectrum.eval_pow, AsymptoticSpectrum.eval_natCast]
        linarith
      -- By asympRank_mono and asympRank_natCast
      have h1 := asympRank_mono p hasymp
      have h2 : p.asympRank (n_k : S) = n_k := asympRank_natCast p n_k hn_k_pos
      have h3 : p.asympRank a ^ k = p.asympRank (a ^ k) := (asympRank_pow p a k).symm
      -- n_k ≤ s^k + 2
      have hn_k_le : (n_k : ℝ) ≤ s ^ k + 2 := by
        -- ⌈x⌉ ≤ ⌊x⌋ + 1 ≤ x + 1 for x ≥ 0
        have hspow_nonneg : 0 ≤ s ^ k := pow_nonneg hs_nonneg k
        have hfl := Nat.floor_le hspow_nonneg
        have hcl := Nat.ceil_le_floor_add_one (s ^ k)
        have hceil_le : (Nat.ceil (s ^ k) : ℝ) ≤ s ^ k + 1 := by
          have h1 : (Nat.ceil (s ^ k) : ℝ) ≤ Nat.floor (s ^ k) + 1 := by
            exact_mod_cast hcl
          linarith
        have hn_k_eq : (n_k : ℝ) = Nat.ceil (s ^ k) + 1 := by exact_mod_cast rfl
        linarith
      -- asympRank(a)^k ≤ s^k + 2
      have hasymprk_pow_le : p.asympRank a ^ k ≤ s ^ k + 2 := by
        calc p.asympRank a ^ k = p.asympRank (a ^ k) := h3
          _ ≤ p.asympRank (n_k : S) := h1
          _ = n_k := h2
          _ ≤ s ^ k + 2 := hn_k_le
      -- Taking k-th root
      have hk_pos : (0 : ℝ) < k :=
        Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hk))
      have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
      have hasymprk_nonneg : 0 ≤ p.asympRank a := asympRank_nonneg p a
      have hrhs_nonneg : 0 ≤ s ^ k + 2 := by positivity
      have hexp_nonneg : 0 ≤ (1 : ℝ) / k := div_nonneg (by norm_num) (le_of_lt hk_pos)
      calc p.asympRank a
          = (p.asympRank a ^ k) ^ (1 / k : ℝ) := by
            rw [← Real.rpow_natCast (p.asympRank a) k, ← Real.rpow_mul hasymprk_nonneg,
                mul_one_div_cancel hk_ne, Real.rpow_one]
        _ ≤ (s ^ k + 2) ^ (1 / k : ℝ) := by
            apply Real.rpow_le_rpow (pow_nonneg hasymprk_nonneg k) hasymprk_pow_le hexp_nonneg
    -- Now show (s^k + 2)^{1/k} → s using squeeze theorem
    -- Lower bound: s ≤ (s^k + 2)^{1/k}
    -- Upper bound: (s^k + 2)^{1/k} ≤ 2^{1/k} * s (for s^k ≥ 2)
    have htendsto : Filter.Tendsto (fun k : ℕ => (s ^ k + 2 : ℝ) ^ (1 / k : ℝ))
        Filter.atTop (nhds s) := by
      -- Lower bound: s = (s^k)^{1/k} ≤ (s^k + 2)^{1/k}
      have hlower : Filter.Tendsto (fun _ : ℕ => s) Filter.atTop (nhds s) := tendsto_const_nhds
      -- Upper bound: s^k + 2 ≤ 3 * s^k when s ≥ 1, so (s^k + 2)^{1/k} ≤ 3^{1/k} * s → s
      have hupper : Filter.Tendsto (fun k : ℕ => (3 : ℝ) ^ (1 / k : ℝ) * s)
          Filter.atTop (nhds (1 * s)) := by
        apply Filter.Tendsto.mul _ tendsto_const_nhds
        -- c^{1/k} → 1 for c > 0 via continuity at 0
        have h1 : Filter.Tendsto (fun k : ℕ => (1 / (k : ℝ))) Filter.atTop (nhds 0) := by
          simp only [one_div]
          exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
        have hcont : ContinuousAt (fun y : ℝ => (3 : ℝ) ^ y) 0 :=
          Real.continuousAt_const_rpow (by norm_num : (3 : ℝ) ≠ 0)
        have h2 : (3 : ℝ) ^ (0 : ℝ) = 1 := Real.rpow_zero 3
        have hcomp := hcont.tendsto.comp h1
        simp only [one_div] at hcomp ⊢
        rwa [h2] at hcomp
      rw [one_mul] at hupper
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
      -- Lower bound holds for k ≥ 1
      · filter_upwards [Filter.eventually_ge_atTop 1] with k hk
        have hk_pos : (0 : ℝ) < k :=
          Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hk))
        have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
        have hexp_nonneg : 0 ≤ (1 : ℝ) / k := div_nonneg (by norm_num) (le_of_lt hk_pos)
        calc s = (s ^ k) ^ (1 / k : ℝ) := by
              rw [← Real.rpow_natCast s k, ← Real.rpow_mul hs_nonneg,
                  mul_one_div_cancel hk_ne, Real.rpow_one]
          _ ≤ (s ^ k + 2) ^ (1 / k : ℝ) := by
              apply Real.rpow_le_rpow (pow_nonneg hs_nonneg k) (by linarith) hexp_nonneg
      -- Upper bound: s^k + 2 ≤ 3 * s^k when s^k ≥ 1 (since 2 ≤ 2 * s^k)
      · filter_upwards [Filter.eventually_ge_atTop 1] with k hk
        have hk_pos : (0 : ℝ) < k :=
          Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hk))
        have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
        have hexp_nonneg : 0 ≤ (1 : ℝ) / k := div_nonneg (by norm_num) (le_of_lt hk_pos)
        have hspow_ge1 : 1 ≤ s ^ k := one_le_pow₀ hs_ge1
        have hspow_nonneg : 0 ≤ s ^ k := pow_nonneg hs_nonneg k
        -- s^k + 2 ≤ s^k + 2 * s^k = 3 * s^k (since 1 ≤ s^k implies 2 ≤ 2 * s^k)
        calc (s ^ k + 2 : ℝ) ^ (1 / k : ℝ)
            ≤ (s ^ k + 2 * s ^ k : ℝ) ^ (1 / k : ℝ) := by
              apply Real.rpow_le_rpow (by linarith)
              · have h2sk : 2 ≤ 2 * s ^ k := by linarith
                linarith
              · exact hexp_nonneg
          _ = (3 * s ^ k : ℝ) ^ (1 / k : ℝ) := by ring_nf
          _ = (3 : ℝ) ^ (1 / k : ℝ) * (s ^ k : ℝ) ^ (1 / k : ℝ) := by
              rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hspow_nonneg]
          _ = (3 : ℝ) ^ (1 / k : ℝ) * s := by
              congr 1
              rw [← Real.rpow_natCast s k, ← Real.rpow_mul hs_nonneg,
                  mul_one_div_cancel hk_ne, Real.rpow_one]
    -- Use le_of_tendsto
    have hbound_eventually : ∀ᶠ (k : ℕ) in Filter.atTop,
        p.asympRank a ≤ (s ^ k + 2 : ℝ) ^ (1 / (k : ℝ)) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with k hk
      exact hkey k hk
    exact ge_of_tendsto htendsto hbound_eventually
  · -- sup ≤ asympRank a
    apply ciSup_le
    intro φ
    exact spectralPoint_le_asympRank p φ a

/-- When the spectrum is nonempty and compact, the supremum is achieved.
    This gives asympRank(a) = max_{φ ∈ X} φ(a).
    Requires the hypothesis that ∃φ, φ(a) ≥ 1. -/
theorem asympRank_eq_max_spectrum [Nonempty (AsymptoticSpectrum p)] (a : S)
    (ha : ∃ φ : AsymptoticSpectrum p, 1 ≤ AsymptoticSpectrum.eval p a φ) :
    ∃ φ : AsymptoticSpectrum p, p.asympRank a = AsymptoticSpectrum.eval p a φ := by
  -- By compactness of X and continuity of eval, the sup is achieved
  -- Uses IsCompact.exists_isMaxOn
  have hcpt := AsymptoticSpectrum.isCompact p
  have hne : (Set.univ : Set (AsymptoticSpectrum p)).Nonempty := Set.univ_nonempty
  have hcont : ContinuousOn (AsymptoticSpectrum.eval p a) Set.univ :=
    (AsymptoticSpectrum.continuous_eval p a).continuousOn
  obtain ⟨φmax, _, hmax⟩ := hcpt.exists_isMaxOn hne hcont
  -- φmax achieves the maximum
  use φmax
  -- asympRank a = sup = φmax(a)
  -- First, show the set is bounded above (by rank a)
  have hbdd : BddAbove (Set.range (AsymptoticSpectrum.eval p a)) := by
    use p.rank a
    intro x hx
    obtain ⟨φ, rfl⟩ := hx
    exact AsymptoticSpectrum.eval_le_rank p φ a
  have hsup_eq : ⨆ φ : AsymptoticSpectrum p, AsymptoticSpectrum.eval p a φ =
      AsymptoticSpectrum.eval p a φmax := by
    apply le_antisymm
    · apply ciSup_le
      intro φ
      exact hmax (Set.mem_univ φ)
    · exact le_ciSup hbdd φmax
  rw [asympRank_eq_iSup_spectrum p a ha, hsup_eq]

/-! ### Asymptotic Subrank = Min over Spectrum (for Gapped Elements) -/

/-- For any spectral point φ, we have asympSubrank(a) ≤ φ(a).
    This follows from the definition and monotonicity. -/
theorem asympSubrank_le_spectralPoint (φ : AsymptoticSpectrum p) (a : S) :
    p.asympSubrank a ≤ AsymptoticSpectrum.eval p a φ := by
  -- The asymptotic subrank is sup over n ≥ 1 of subrank(a^n)^{1/n}
  -- We need to show: sup { subrank(a^n)^{1/n} : n ≥ 1 } ≤ φ(a)
  unfold asympSubrank
  apply csSup_le (p.asympSubrankSet_nonempty a)
  intro x hx
  simp only [asympSubrankSet, Set.mem_image] at hx
  obtain ⟨n, hn, rfl⟩ := hx
  have hn_pos : 0 < n := Nat.one_le_iff_ne_zero.mp hn |> Nat.pos_of_ne_zero
  have hn_real_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_real_pos
  -- We have subrank(a^n) ≤ φ(a^n) = φ(a)^n
  have heval := AsymptoticSpectrum.eval_pow p φ a n
  have hbound := AsymptoticSpectrum.subrank_le_eval p φ (a ^ n)
  have heval_nonneg := AsymptoticSpectrum.eval_nonneg p φ a
  -- subrank(a^n) ≤ φ(a)^n in ℝ
  have hpow : (p.subrank (a ^ n) : ℝ) ≤ (AsymptoticSpectrum.eval p a φ) ^ n := by
    calc (p.subrank (a ^ n) : ℝ) ≤ AsymptoticSpectrum.eval p (a ^ n) φ := hbound
      _ = (AsymptoticSpectrum.eval p a φ) ^ n := heval
  -- From x ≤ y^n we get x^{1/n} ≤ y for nonnegative x, y
  have hsubrank_nonneg : (0 : ℝ) ≤ p.subrank (a ^ n) := Nat.cast_nonneg _
  -- (φ(a)^n)^{1/n} = φ(a)
  have hpow_eq : ((AsymptoticSpectrum.eval p a φ) ^ n) ^ (1 / (n : ℝ)) =
      AsymptoticSpectrum.eval p a φ := by
    rw [← Real.rpow_natCast (AsymptoticSpectrum.eval p a φ) n,
        ← Real.rpow_mul heval_nonneg, mul_one_div_cancel hn_ne, Real.rpow_one]
  calc (p.subrank (a ^ n) : ℝ) ^ (1 / (n : ℝ))
      ≤ ((AsymptoticSpectrum.eval p a φ) ^ n) ^ (1 / (n : ℝ)) := by
        apply Real.rpow_le_rpow hsubrank_nonneg hpow
        exact div_nonneg (by norm_num) (le_of_lt hn_real_pos)
    _ = AsymptoticSpectrum.eval p a φ := hpow_eq

/-- For gapped elements, the asymptotic subrank equals the infimum of φ(a) over all φ ∈ X.

    The gapped condition is necessary to ensure that the infimum matches the subrank.
    Without it, there can be a gap between asympSubrank and inf_{φ} φ(a).

    Proof uses:
    - th:asympsubrank-almost for intermediate characterization
    - lem:gapped to strengthen the bounds -/
theorem asympSubrank_eq_iInf_spectrum (a : S) (ha : p.IsGapped a)
    (harch : ∀ x : S, p.rel x 0 ∨ p.rel 1 x)
    [Nonempty (AsymptoticSpectrum p)] :
    p.asympSubrank a = ⨅ φ : AsymptoticSpectrum p, AsymptoticSpectrum.eval p a φ := by
  apply le_antisymm
  · -- asympSubrank a ≤ inf: each spectral point bounds subrank
    apply le_ciInf
    intro φ
    exact asympSubrank_le_spectralPoint p φ a
  · -- inf ≤ asympSubrank a: requires gapped condition
    -- Handle three cases: strictly gapped, ≤_P 0, or ∃φ φ(a)=1
    rcases ha with ⟨k, hk_pos, hgap⟩ | ha0 | ⟨φ₀, hφ₀⟩
    · -- Case 1: strictly gapped (∃k > 0, 2 ≤_P a^k)
      -- Proof (from survey.tex Lemma lem:gapped):
      -- 1. Let s = inf φ(a). From gapped (a^k ≥_P 2): all φ(a)^k ≥ 2, so s ≥ 1.
      -- 2. For all n: ⌊s^n⌋ ≤ φ(a^n) for all φ
      -- 3. By spectral duality: ⌊s^n⌋ ≤_{asymp} a^n
      -- 4. Unfold: ⌊s^n⌋^m ≤_P a^{nm} · x_m with x_m^{1/m} → 1
      -- 5. Using gapped: eventually x_m ≤ 2^m ≤ a^{km}
      -- 6. So ⌊s^n⌋^m ≤_P a^{(n+k)m} for large m
      -- 7. Take subrank: ⌊s^n⌋ ≤ subrank(a^{(n+k)m})^{1/m} ≤ asympSubrank(a)^{(n+k)}
      -- 8. So ⌊s^n⌋^{1/(n+k)} ≤ asympSubrank(a), and as n → ∞: s ≤ asympSubrank(a)
      let s := ⨅ φ : AsymptoticSpectrum p, AsymptoticSpectrum.eval p a φ
      -- Step 1: s ≥ 1 since all φ(a)^k ≥ 2
      have hs_ge1 : 1 ≤ s := by
        apply le_ciInf
        intro φ
        -- From gapped: p.rel 2 (a^k), so eval 2 ≤ eval (a^k)
        have hphi_ak := AsymptoticSpectrum.eval_mono p φ hgap
        -- Convert: eval p 2 φ = 2 and eval p (a^k) φ = (eval p a φ)^k
        have h2_eq : AsymptoticSpectrum.eval p (2 : S) φ = 2 := by
          have := AsymptoticSpectrum.eval_natCast p φ 2
          simp only [Nat.cast_ofNat] at this
          exact this
        have hpow_eq := AsymptoticSpectrum.eval_pow p φ a k
        rw [h2_eq, hpow_eq] at hphi_ak
        -- 2 ≤ φ(a)^k implies φ(a) ≥ 1 (since 0 ≤ x < 1 implies x^k < 1 < 2)
        have hphi_a_nonneg := AsymptoticSpectrum.eval_nonneg p φ a
        by_contra hlt
        push_neg at hlt
        -- hlt : φ(a) < 1
        have hpow_lt : (AsymptoticSpectrum.eval p a φ) ^ k < 1 := by
          calc (AsymptoticSpectrum.eval p a φ) ^ k
              < 1 ^ k := pow_lt_pow_left₀ hlt hphi_a_nonneg (Nat.one_le_iff_ne_zero.mp hk_pos)
            _ = 1 := one_pow k
        linarith
      have hs_nonneg : 0 ≤ s := by linarith
      -- Step 2-3: For each n ≥ 1, ⌊s^n⌋ ≤_{asymp} a^n via spectral duality
      have hasym_floor : ∀ n : ℕ, 0 < n → AsympRel p (⌊s ^ n⌋₊ : S) (a ^ n) := by
        intro n hn
        rw [asympRel_iff_forall_spectrum]
        intro φ
        simp only [AsymptoticSpectrum.eval_natCast, AsymptoticSpectrum.eval_pow]
        have hs_le : s ≤ AsymptoticSpectrum.eval p a φ := ciInf_le
          ⟨0, fun x ⟨ψ, hψ⟩ => hψ ▸ AsymptoticSpectrum.eval_nonneg p ψ a⟩ φ
        calc (⌊s ^ n⌋₊ : ℝ) ≤ s ^ n := Nat.floor_le (pow_nonneg hs_nonneg n)
          _ ≤ (AsymptoticSpectrum.eval p a φ) ^ n := pow_le_pow_left₀ hs_nonneg hs_le n
      -- Step 4-7: Use AsympRel and gapped to show ⌊s^n⌋^{1/(n+k)} ≤ asympSubrank(a)
      -- Key steps (documented):
      -- 1. From AsympRel p ⌊s^n⌋ (a^n): ∃ x, ⌊s^n⌋^m ≤_P (a^n)^m * x(m) with sInf x^{1/m} = 1
      -- 2. From gapped: 2^m ≤_P a^{km} (by induction on m using hgap)
      -- 3. From sInf = 1: eventually x(m)^{1/m} < 2, so x(m) < 2^m for large m
      -- 4. Combining: ⌊s^n⌋^m ≤_P a^{nm} * x(m) ≤_P a^{nm} * 2^m ≤_P a^{nm} * a^{km}
      --    = a^{(n+k)m}
      -- 5. Subrank: ⌊s^n⌋^m ≤ subrank(a^{(n+k)m})
      -- 6. Take ((n+k)m)-th root:
      --    ⌊s^n⌋^{1/(n+k)} ≤ subrank(a^{(n+k)m})^{1/((n+k)m)} ≤ asympSubrank(a)
      have hfloor_bound : ∀ n : ℕ, 0 < n →
          (⌊s ^ n⌋₊ : ℝ) ^ (1 / ((n : ℝ) + k)) ≤ p.asympSubrank a := by
        intro n hn
        have hnk_pos : (0 : ℝ) < n + k := by positivity
        -- Case: ⌊s^n⌋ = 0
        by_cases hfloor_zero : ⌊s ^ n⌋₊ = 0
        · simp only [hfloor_zero, Nat.cast_zero]
          have hexp_ne : 1 / ((n : ℝ) + k) ≠ 0 := by positivity
          have h0pow : (0 : ℝ) ^ (1 / ((n : ℝ) + k)) = 0 := Real.zero_rpow hexp_ne
          rw [h0pow]
          exact p.asympSubrank_nonneg a
        -- Case: ⌊s^n⌋ ≥ 1
        have hfloor_pos : 0 < ⌊s ^ n⌋₊ := Nat.pos_of_ne_zero hfloor_zero
        -- Get AsympRel witness
        obtain ⟨x, hx_bound, hx_inf⟩ := hasym_floor n hn
        -- From gapped: 2^m ≤_P a^{km} by induction
        have h2m_le_akm : ∀ m : ℕ, p.rel ((2 : ℕ) ^ m) (a ^ (k * m)) := by
          intro m
          induction m with
          | zero => simp only [pow_zero, mul_zero, pow_zero]; exact p.refl 1
          | succ m' ih =>
            have h1 : ((2 : ℕ) ^ (m' + 1) : S) = (2 : ℕ) ^ m' * 2 := by ring
            have h2 : a ^ (k * (m' + 1)) = a ^ (k * m') * a ^ k := by ring
            rw [h1, h2]
            exact p.mul_mono_both ih hgap
        -- From sInf = 1 < 2, there exists m ≥ 1 with x(m)^{1/m} < 2
        have hsInf_lt_2 : sInf ((fun m => (x m : ℝ) ^ (1 / (m : ℝ))) '' {m | 1 ≤ m}) < 2 := by
          rw [hx_inf]; norm_num
        -- Step 1: From sInf = 1 < 2, extract m ≥ 1 with x(m)^{1/m} < 2
        have hne : ((fun m => (x m : ℝ) ^ (1 / (m : ℝ))) '' {m | 1 ≤ m}).Nonempty := by
          use (x 1 : ℝ) ^ (1 / (1 : ℝ))
          exact ⟨1, Nat.le_refl 1, by simp⟩
        obtain ⟨y, ⟨m, hm, rfl⟩, hy_lt⟩ := exists_lt_of_csInf_lt hne hsInf_lt_2
        -- Step 2: From x(m)^{1/m} < 2 we get x(m) < 2^m
        have hm_pos : (0 : ℝ) < m :=
          Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hm))
        have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
        have hxm_lt_2m : (x m : ℝ) < (2 : ℝ) ^ m := by
          have hxm_nonneg : (0 : ℝ) ≤ x m := Nat.cast_nonneg _
          have h2m_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ m := by positivity
          have hexp_pos : 0 < 1 / (m : ℝ) := by positivity
          -- hy_lt : (fun m ↦ ↑(x m) ^ (1 / ↑m)) m < 2 = ↑(x m) ^ (1 / ↑m) < 2
          -- We have (x m)^{1/m} < 2 = (2^m)^{1/m}, so (x m) < 2^m by rpow_lt_rpow_iff
          have heq : (2 : ℝ) = ((2 : ℝ) ^ (m : ℕ)) ^ (1 / (m : ℝ)) := by
            have h2_nonneg : (0 : ℝ) ≤ 2 := by norm_num
            rw [← Real.rpow_natCast 2 m, ← Real.rpow_mul h2_nonneg,
                mul_one_div_cancel hm_ne, Real.rpow_one]
          rw [heq] at hy_lt
          -- hy_lt : ↑(x m) ^ (1 / ↑m) < (2 ^ m) ^ (1 / ↑m)
          exact Real.rpow_lt_rpow_iff hxm_nonneg h2m_nonneg hexp_pos |>.mp hy_lt
        -- Now use integrality: x(m) : ℕ and x(m) < 2^m means x(m) ≤ 2^m - 1 < 2^m
        -- More directly: x(m) < 2^m in ℕ
        have hxm_lt_2m_nat : x m < 2 ^ m := by
          have h2m_pos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
          have h := hxm_lt_2m
          rw [show ((2 : ℝ) ^ m) = ((2 ^ m : ℕ) : ℝ) by push_cast; rfl] at h
          exact Nat.cast_lt.mp h
        -- Step 3-4: Chain the preorder inequalities
        -- hx_bound m hm : p.rel (⌊s^n⌋^m) ((a^n)^m * x(m))
        have hfloor_bound_m := hx_bound m hm
        -- From x(m) < 2^m we get x(m) ≤ 2^m in ℕ, so x(m) ≤_P 2^m (use natCast_mono)
        have hxm_le_2m : p.rel ((x m : ℕ) : S) ((2 ^ m : ℕ) : S) := by
          apply p.natCast_mono
          exact le_of_lt hxm_lt_2m_nat
        -- Need to convert (2 : ℕ) ^ m to match h2m_le_akm which has ↑2 ^ m
        have h2pow_eq : ((2 ^ m : ℕ) : S) = (2 : S) ^ m := by push_cast; rfl
        rw [h2pow_eq] at hxm_le_2m
        have hmul_step : p.rel (((a ^ n) ^ m) * (x m : S)) (((a ^ n) ^ m) * ((2 : S) ^ m)) :=
          p.mul_mono_right _ hxm_le_2m
        -- h2m_le_akm m : p.rel (↑2^m) (a^{km})
        have h2m_le : p.rel ((2 : S) ^ m) (a ^ (k * m)) := h2m_le_akm m
        have hmul_step2 : p.rel (((a ^ n) ^ m) * ((2 : S) ^ m)) (((a ^ n) ^ m) * (a ^ (k * m))) :=
          p.mul_mono_right _ h2m_le
        -- Combine: (a^n)^m * a^{km} = a^{nm + km} = a^{(n+k)m}
        have hpow_eq : ((a ^ n) ^ m) * (a ^ (k * m)) = a ^ ((n + k) * m) := by
          rw [← pow_mul, ← pow_add]; ring_nf
        rw [hpow_eq] at hmul_step2
        -- Full chain: ⌊s^n⌋^m ≤_P a^{(n+k)m}
        have hchain : p.rel ((⌊s ^ n⌋₊ : S) ^ m) (a ^ ((n + k) * m)) :=
          p.trans _ _ _ (p.trans _ _ _ hfloor_bound_m hmul_step) hmul_step2
        -- Step 5-6: Take subrank and roots
        -- ⌊s^n⌋^m ≤ subrank(a^{(n+k)m}) by subrank_mono and subrank_natCast'
        have hsubrank_ineq : (⌊s ^ n⌋₊ : ℕ) ^ m ≤ p.subrank (a ^ ((n + k) * m)) := by
          have h1 : p.subrank ((⌊s ^ n⌋₊ : S) ^ m) ≤ p.subrank (a ^ ((n + k) * m)) :=
            p.subrank_mono hchain
          have h2 : p.subrank ((⌊s ^ n⌋₊ : S) ^ m) = p.subrank (((⌊s ^ n⌋₊ : ℕ) ^ m : ℕ) : S) := by
            congr 1; push_cast; rfl
          rw [h2, p.subrank_natCast'] at h1
          exact h1
        -- Rewrite as ⌊s^n⌋ ^ m ≤ subrank(a^{(n+k)m}) in ℝ
        have hsubrank_real : (⌊s ^ n⌋₊ : ℝ) ^ m ≤ (p.subrank (a ^ ((n + k) * m)) : ℝ) := by
          calc (⌊s ^ n⌋₊ : ℝ) ^ m = (((⌊s ^ n⌋₊ : ℕ) ^ m : ℕ) : ℝ) := by push_cast; rfl
            _ ≤ ((p.subrank (a ^ ((n + k) * m))) : ℝ) := Nat.cast_le.mpr hsubrank_ineq
        -- Take ((n+k)m)-th root
        have hnkm_nat_pos : 0 < (n + k) * m :=
          Nat.mul_pos (Nat.add_pos_left hn k) (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hm))
        have hnkm_pos : (0 : ℝ) < ((n + k) * m : ℕ) := Nat.cast_pos.mpr hnkm_nat_pos
        have hnkm_ne : (((n + k) * m : ℕ) : ℝ) ≠ 0 := ne_of_gt hnkm_pos
        have hfloor_nonneg : (0 : ℝ) ≤ ⌊s ^ n⌋₊ := Nat.cast_nonneg _
        have hsubrank_nonneg : (0 : ℝ) ≤ p.subrank (a ^ ((n + k) * m)) := Nat.cast_nonneg _
        -- ⌊s^n⌋^{m/((n+k)m)} ≤ subrank(a^{(n+k)m})^{1/((n+k)m)}
        have hroot_ineq : (⌊s ^ n⌋₊ : ℝ) ^ ((m : ℝ) / (((n + k) * m : ℕ) : ℝ)) ≤
            (p.subrank (a ^ ((n + k) * m)) : ℝ) ^ (1 / (((n + k) * m : ℕ) : ℝ)) := by
          have hexp_nonneg : 0 ≤ 1 / (((n + k) * m : ℕ) : ℝ) := by positivity
          -- x^{m / ((n+k)m)} = (x^m)^{1/((n+k)m)} since m / ((n+k)m) = m * (1/((n+k)m))
          have hexp_eq : (m : ℝ) / (((n + k) * m : ℕ) : ℝ) =
              (m : ℕ) * (1 / (((n + k) * m : ℕ) : ℝ)) := by
            simp only [Nat.cast_mul, Nat.cast_add]; ring
          rw [hexp_eq, Real.rpow_mul hfloor_nonneg, Real.rpow_natCast]
          apply Real.rpow_le_rpow (pow_nonneg hfloor_nonneg m) hsubrank_real hexp_nonneg
        -- Simplify exponent: m / ((n+k)m) = 1/(n+k)
        have hexp_simp : (m : ℝ) / (((n + k) * m : ℕ) : ℝ) = 1 / ((n : ℝ) + k) := by
          simp only [Nat.cast_mul, Nat.cast_add]
          field_simp
        rw [hexp_simp] at hroot_ineq
        -- Step 7: subrank(a^{(n+k)m})^{1/((n+k)m)} ≤ asympSubrank(a)
        have hasym_bound : (p.subrank (a ^ ((n + k) * m)) : ℝ) ^ (1 / (((n + k) * m : ℕ) : ℝ)) ≤
            p.asympSubrank a := by
          apply le_csSup (p.asympSubrankSet_bddAbove a)
          simp only [asympSubrankSet, Set.mem_image, Set.mem_Ici]
          refine ⟨(n + k) * m, ?_, ?_⟩
          · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.add_pos_left hn k).ne'
              (Nat.one_le_iff_ne_zero.mp hm))
          · simp only [one_div, Nat.cast_mul, Nat.cast_add]
        exact hroot_ineq.trans hasym_bound
      -- Step 8: As n → ∞, ⌊s^n⌋^{1/(n+k)} → s, so s ≤ asympSubrank(a)
      -- Since ⌊s^n⌋ ≥ s^n - 1 and ⌊s^n⌋ ≤ s^n, we have ⌊s^n⌋^{1/(n+k)} → s as n → ∞
      -- Combined with hfloor_bound: s ≤ asympSubrank(a)
      -- Use contradiction: if s > asympSubrank(a), find large n where bound fails
      by_contra hlt
      push_neg at hlt
      -- s > asympSubrank(a)
      obtain ⟨r, hasub_lt_r, hr_lt_s⟩ := exists_between hlt
      -- For large n, ⌊s^n⌋^{1/(n+k)} > r (since it converges to s > r)
      -- But hfloor_bound says ⌊s^n⌋^{1/(n+k)} ≤ asympSubrank(a) < r, contradiction
      -- Limit: ⌊s^n⌋^{1/(n+k)} ≤ s^{n/(n+k)} → s as n → ∞
      -- And ⌊s^n⌋^{1/(n+k)} ≥ (s^n - 1)^{1/(n+k)} → s as n → ∞ (since s ≥ 1)
      -- Technical: need Filter.Tendsto machinery
      have hconv : Filter.Tendsto (fun n : ℕ => (⌊s ^ n⌋₊ : ℝ) ^ (1 / ((n : ℝ) + k)))
          Filter.atTop (nhds s) := by
        -- Use squeeze theorem: (s^n - 1)^{1/(n+k)} ≤ ⌊s^n⌋^{1/(n+k)} ≤ s^{n/(n+k)}
        -- Both bounds → s as n → ∞
        have hs_pos : 0 < s := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hs_ge1
        have hs_ne : s ≠ 0 := ne_of_gt hs_pos
        -- Upper bound: s^{n/(n+k)} → s since n/(n+k) → 1 and s^y is continuous
        have hupper_tendsto : Filter.Tendsto (fun n : ℕ => s ^ ((n : ℝ) / ((n : ℝ) + k)))
            Filter.atTop (nhds s) := by
          have hexp_tendsto : Filter.Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + k))
              Filter.atTop (nhds 1) := tendsto_natCast_div_add_atTop (k : ℝ)
          have hcont := Real.continuous_const_rpow hs_ne
          have h1 := hcont.tendsto 1 |>.comp hexp_tendsto
          simp only [Real.rpow_one] at h1
          exact h1
        -- Case split: s = 1 or s > 1
        rcases eq_or_lt_of_le hs_ge1 with hs_eq1 | hs_gt1
        · -- Case s = 1: floor(1^n) = 1, so 1^{1/(n+k)} = 1 → 1
          rw [← hs_eq1]
          simp only [one_pow, Nat.floor_one, Nat.cast_one]
          have heq : (fun n : ℕ => (1 : ℝ) ^ (1 / ((n : ℝ) + k))) = fun _ => 1 := by
            funext n
            exact Real.one_rpow _
          rw [heq]
          exact tendsto_const_nhds
        · -- Case s > 1: use squeeze theorem
          -- Upper bound: ⌊s^n⌋₊ ≤ s^n, so ⌊s^n⌋₊^{1/(n+k)} ≤ s^{n/(n+k)}
          have hupper : ∀ n : ℕ, (⌊s ^ n⌋₊ : ℝ) ^ (1 / ((n : ℝ) + k)) ≤
              s ^ ((n : ℝ) / ((n : ℝ) + k)) := by
            intro n
            have hnk_pos : (0 : ℝ) < n + k := by positivity
            have hexp_pos : 0 < 1 / ((n : ℝ) + k) := by positivity
            have hfloor_le : (⌊s ^ n⌋₊ : ℝ) ≤ s ^ n := Nat.floor_le (pow_nonneg hs_nonneg n)
            have hfloor_nonneg : (0 : ℝ) ≤ ⌊s ^ n⌋₊ := Nat.cast_nonneg _
            calc (⌊s ^ n⌋₊ : ℝ) ^ (1 / ((n : ℝ) + k))
                ≤ (s ^ n) ^ (1 / ((n : ℝ) + k)) := by
                  apply Real.rpow_le_rpow hfloor_nonneg hfloor_le (le_of_lt hexp_pos)
              _ = s ^ (n * (1 / ((n : ℝ) + k))) := by
                  rw [← Real.rpow_natCast s n, ← Real.rpow_mul hs_nonneg]
              _ = s ^ ((n : ℝ) / ((n : ℝ) + k)) := by ring_nf
          -- Lower bound: for large n, s^n ≥ 2, so ⌊s^n⌋₊ ≥ s^n - 1 ≥ s^n/2
          -- Then (s^n/2)^{1/(n+k)} = s^{n/(n+k)} / 2^{1/(n+k)} → s
          have hlower_tendsto : Filter.Tendsto
              (fun n : ℕ => s ^ ((n : ℝ) / ((n : ℝ) + k)) / 2 ^ (1 / ((n : ℝ) + k)))
              Filter.atTop (nhds s) := by
            have h2exp : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ (1 / ((n : ℝ) + k)))
                Filter.atTop (nhds 1) := by
              have hexp_tendsto : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + k))
                  Filter.atTop (nhds 0) := by
                have hnat_tendsto : Filter.Tendsto (fun n : ℕ => (n : ℝ) + (k : ℝ))
                    Filter.atTop Filter.atTop := by
                  apply Filter.Tendsto.atTop_add tendsto_natCast_atTop_atTop
                  exact tendsto_const_nhds
                have hdiv := Filter.Tendsto.inv_tendsto_atTop hnat_tendsto
                simp only [one_div]
                exact hdiv
              have hcont := Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0)
              have h1 := hcont.tendsto 0 |>.comp hexp_tendsto
              simp only [Real.rpow_zero] at h1
              exact h1
            have hdiv := Filter.Tendsto.div hupper_tendsto h2exp (by norm_num : (1 : ℝ) ≠ 0)
            simp only [div_one] at hdiv
            exact hdiv
          -- Eventually ⌊s^n⌋₊ ≥ s^n / 2 (when s^n ≥ 2)
          have hlower_eventually : ∀ᶠ n : ℕ in Filter.atTop,
              s ^ ((n : ℝ) / ((n : ℝ) + k)) / 2 ^ (1 / ((n : ℝ) + k)) ≤
              (⌊s ^ n⌋₊ : ℝ) ^ (1 / ((n : ℝ) + k)) := by
            -- s^n → ∞ since s > 1, so eventually s^n ≥ 2
            have hs_pow_tendsto :
                Filter.Tendsto (fun n : ℕ => s ^ n) Filter.atTop Filter.atTop := by
              exact tendsto_pow_atTop_atTop_of_one_lt hs_gt1
            have h2_filter := hs_pow_tendsto.eventually_ge_atTop 2
            apply h2_filter.mono
            intro n hsn_ge2
            have hnk_pos : (0 : ℝ) < n + k := by positivity
            have hexp_pos : 0 < 1 / ((n : ℝ) + k) := by positivity
            -- From s^n ≥ 2, we get s^n - 1 ≥ s^n / 2
            have hdiv_bound : s ^ n / 2 ≤ s ^ n - 1 := by
              have : s ^ n / 2 + 1 ≤ s ^ n := by linarith
              linarith
            -- ⌊s^n⌋₊ ≥ s^n - 1
            have hfloor_ge : s ^ n - 1 ≤ (⌊s ^ n⌋₊ : ℝ) := le_of_lt (Nat.sub_one_lt_floor (s ^ n))
            have hfloor_ge' : s ^ n / 2 ≤ (⌊s ^ n⌋₊ : ℝ) := hdiv_bound.trans hfloor_ge
            -- (s^n / 2)^{1/(n+k)} ≤ ⌊s^n⌋₊^{1/(n+k)}
            have hdiv_nonneg : 0 ≤ s ^ n / 2 := by positivity
            calc s ^ ((n : ℝ) / ((n : ℝ) + k)) / 2 ^ (1 / ((n : ℝ) + k))
                = (s ^ n / 2) ^ (1 / ((n : ℝ) + k)) := by
                  rw [Real.div_rpow (pow_nonneg hs_nonneg n) (by norm_num : (0 : ℝ) ≤ 2),
                      ← Real.rpow_natCast s n, ← Real.rpow_mul hs_nonneg]
                  ring_nf
              _ ≤ (⌊s ^ n⌋₊ : ℝ) ^ (1 / ((n : ℝ) + k)) := by
                  apply Real.rpow_le_rpow hdiv_nonneg hfloor_ge' (le_of_lt hexp_pos)
          -- Apply squeeze theorem
          exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower_tendsto hupper_tendsto
            hlower_eventually (Filter.Eventually.of_forall hupper)
      have hr_pos : 0 < r := lt_of_le_of_lt (p.asympSubrank_nonneg a) hasub_lt_r
      have heventually := hconv.eventually_const_lt hr_lt_s
      obtain ⟨N, hN⟩ := heventually.exists_forall_of_atTop
      -- Need N > 0 for hfloor_bound
      have hN_pos : 0 < max 1 N := by omega
      specialize hN (max 1 N) (le_max_right _ _)
      have hbound := hfloor_bound (max 1 N) (Nat.lt_of_lt_of_le Nat.one_pos (le_max_left _ _))
      linarith
    · -- Case 2: a ≤_P 0 (a is equivalent to 0)
      -- All spectral points give φ(a) = 0 since 0 ≤ φ(a) ≤ φ(0) = 0
      have heq_zero : ∀ φ : AsymptoticSpectrum p, AsymptoticSpectrum.eval p a φ = 0 := by
        intro φ
        have h1 : AsymptoticSpectrum.eval p a φ ≤ AsymptoticSpectrum.eval p (0 : S) φ :=
          AsymptoticSpectrum.eval_mono p φ ha0
        have h2 : AsymptoticSpectrum.eval p (0 : S) φ = 0 := by
          have := AsymptoticSpectrum.eval_natCast p φ 0
          simp only [Nat.cast_zero] at this
          exact this
        have h3 : 0 ≤ AsymptoticSpectrum.eval p a φ := AsymptoticSpectrum.eval_nonneg p φ a
        linarith
      simp only [heq_zero, ciInf_const]
      exact p.asympSubrank_nonneg a
    · -- Case 3: ∃ φ₀ with φ₀(a) = 1 (survey def:gapped disjunct (iii), tex:1912-1916).
      -- Goal: ⨅ φ, φ(a) ≤ asympSubrank a.
      -- φ₀(a) = 1 > 0 forces ¬(a ≤_P 0); the Strong-Archimedean hypothesis `harch`
      -- then gives 1 ≤_P a, hence asympSubrank a ≥ 1, while ⨅ ≤ φ₀(a) = 1.
      have hnot0 : ¬ p.rel a 0 := by
        intro h0
        have hle := AsymptoticSpectrum.eval_mono p φ₀ h0
        rw [AsymptoticSpectrum.eval_zero p φ₀, hφ₀] at hle
        linarith
      have h1a : p.rel 1 a := (harch a).resolve_left hnot0
      have hbdd : BddBelow (Set.range (fun φ : AsymptoticSpectrum p =>
          AsymptoticSpectrum.eval p a φ)) :=
        ⟨0, fun x ⟨ψ, hψ⟩ => hψ ▸ AsymptoticSpectrum.eval_nonneg p ψ a⟩
      have hs_le1 : (⨅ φ : AsymptoticSpectrum p, AsymptoticSpectrum.eval p a φ) ≤ 1 :=
        (ciInf_le hbdd φ₀).trans (le_of_eq hφ₀)
      have hasub : (1 : ℝ) ≤ p.asympSubrank a :=
        (p.one_le_asympSubrank_le_asympRank h1a).1
      exact hs_le1.trans hasub

/-- When the spectrum is nonempty, compact, and the element is gapped,
    the infimum is achieved. This gives asympSubrank(a) = min_{φ ∈ X} φ(a). -/
theorem asympSubrank_eq_min_spectrum [Nonempty (AsymptoticSpectrum p)] (a : S)
    (ha : p.IsGapped a) (harch : ∀ x : S, p.rel x 0 ∨ p.rel 1 x) :
    ∃ φ : AsymptoticSpectrum p, p.asympSubrank a = AsymptoticSpectrum.eval p a φ := by
  -- By compactness of X and continuity of eval, the inf is achieved
  -- Uses IsCompact.exists_isMinOn
  have hcpt := AsymptoticSpectrum.isCompact p
  have hne : (Set.univ : Set (AsymptoticSpectrum p)).Nonempty := Set.univ_nonempty
  have hcont : ContinuousOn (AsymptoticSpectrum.eval p a) Set.univ :=
    (AsymptoticSpectrum.continuous_eval p a).continuousOn
  obtain ⟨φmin, _, hmin⟩ := hcpt.exists_isMinOn hne hcont
  -- φmin achieves the minimum
  use φmin
  -- asympSubrank a = inf = φmin(a)
  -- First, show the set is bounded below (by 0)
  have hbdd : BddBelow (Set.range (AsymptoticSpectrum.eval p a)) := by
    use 0
    intro x hx
    obtain ⟨φ, rfl⟩ := hx
    exact AsymptoticSpectrum.eval_nonneg p φ a
  have hinf_eq : ⨅ φ : AsymptoticSpectrum p, AsymptoticSpectrum.eval p a φ =
      AsymptoticSpectrum.eval p a φmin := by
    apply le_antisymm
    · exact ciInf_le hbdd φmin
    · apply le_ciInf
      intro φ
      exact hmin (Set.mem_univ φ)
  rw [asympSubrank_eq_iInf_spectrum p a ha harch, hinf_eq]

/-! ### Multiplicativity via Spectral Duality -/

/-- Asymptotic rank is sub-multiplicative, via spectral duality.

    Proof: asympRank(ab) = sup_φ φ(ab) = sup_φ φ(a)φ(b)
           ≤ (sup_φ φ(a))(sup_φ φ(b)) = asympRank(a)·asympRank(b)

    Requires the hypothesis that ∃φ, φ(x) ≥ 1 for x ∈ {a, b, a*b}. -/
theorem asympRank_mul_le_of_spectrum [Nonempty (AsymptoticSpectrum p)] (a b : S)
    (ha : ∃ φ : AsymptoticSpectrum p, 1 ≤ AsymptoticSpectrum.eval p a φ)
    (hb : ∃ φ : AsymptoticSpectrum p, 1 ≤ AsymptoticSpectrum.eval p b φ)
    (hab : ∃ φ : AsymptoticSpectrum p, 1 ≤ AsymptoticSpectrum.eval p (a * b) φ) :
    p.asympRank (a * b) ≤ p.asympRank a * p.asympRank b := by
  -- Bounded above by rank
  have hbdd_a : BddAbove (Set.range (AsymptoticSpectrum.eval p a)) := by
    use p.rank a
    intro x hx
    obtain ⟨φ, rfl⟩ := hx
    exact AsymptoticSpectrum.eval_le_rank p φ a
  have hbdd_b : BddAbove (Set.range (AsymptoticSpectrum.eval p b)) := by
    use p.rank b
    intro x hx
    obtain ⟨φ, rfl⟩ := hx
    exact AsymptoticSpectrum.eval_le_rank p φ b
  -- Using spectral characterization
  rw [asympRank_eq_iSup_spectrum p (a * b) hab, asympRank_eq_iSup_spectrum p a ha,
      asympRank_eq_iSup_spectrum p b hb]
  -- sup_φ φ(ab) ≤ (sup_φ φ(a)) * (sup_φ φ(b))
  apply ciSup_le
  intro φ
  -- φ(ab) = φ(a) * φ(b) ≤ sup_φ φ(a) * sup_φ φ(b)
  have ha_le : AsymptoticSpectrum.eval p a φ ≤ ⨆ ψ, AsymptoticSpectrum.eval p a ψ :=
    le_ciSup hbdd_a φ
  have hb_le : AsymptoticSpectrum.eval p b φ ≤ ⨆ ψ, AsymptoticSpectrum.eval p b ψ :=
    le_ciSup hbdd_b φ
  have hb_nonneg : 0 ≤ AsymptoticSpectrum.eval p b φ := AsymptoticSpectrum.eval_nonneg p φ b
  have hsup_a_nonneg : 0 ≤ ⨆ ψ, AsymptoticSpectrum.eval p a ψ := by
    apply le_ciSup_of_le hbdd_a φ (AsymptoticSpectrum.eval_nonneg p φ a)
  calc AsymptoticSpectrum.eval p (a * b) φ
      = AsymptoticSpectrum.eval p a φ * AsymptoticSpectrum.eval p b φ :=
        AsymptoticSpectrum.eval_mul p φ a b
    _ ≤ (⨆ ψ, AsymptoticSpectrum.eval p a ψ) * (⨆ ψ, AsymptoticSpectrum.eval p b ψ) :=
        mul_le_mul ha_le hb_le hb_nonneg hsup_a_nonneg

/-- Asymptotic subrank is super-multiplicative, via spectral duality.

    Proof: asympSubrank(a)·asympSubrank(b) = (inf_φ φ(a))(inf_φ φ(b))
           ≤ inf_φ φ(a)φ(b) = inf_φ φ(ab) = asympSubrank(ab)

    Note: This version requires all three elements (a, b, and a*b) to be gapped
    to use the full spectral characterization. -/
theorem le_asympSubrank_mul_of_spectrum [Nonempty (AsymptoticSpectrum p)] (a b : S)
    (ha : p.IsGapped a) (hb : p.IsGapped b) (hab : p.IsGapped (a * b))
    (harch : ∀ x : S, p.rel x 0 ∨ p.rel 1 x) :
    p.asympSubrank a * p.asympSubrank b ≤ p.asympSubrank (a * b) := by
  -- Bounded below by 0
  have hbdd_a : BddBelow (Set.range (AsymptoticSpectrum.eval p a)) := by
    use 0; intro x hx; obtain ⟨φ, rfl⟩ := hx; exact AsymptoticSpectrum.eval_nonneg p φ a
  have hbdd_b : BddBelow (Set.range (AsymptoticSpectrum.eval p b)) := by
    use 0; intro x hx; obtain ⟨φ, rfl⟩ := hx; exact AsymptoticSpectrum.eval_nonneg p φ b
  -- Using spectral characterization for gapped elements
  rw [asympSubrank_eq_iInf_spectrum p a ha harch, asympSubrank_eq_iInf_spectrum p b hb harch,
      asympSubrank_eq_iInf_spectrum p (a * b) hab harch]
  -- inf φ(a) * inf φ(b) ≤ inf φ(ab)
  apply le_ciInf
  intro φ
  have ha_ge : (⨅ ψ, AsymptoticSpectrum.eval p a ψ) ≤ AsymptoticSpectrum.eval p a φ :=
    ciInf_le hbdd_a φ
  have hb_ge : (⨅ ψ, AsymptoticSpectrum.eval p b ψ) ≤ AsymptoticSpectrum.eval p b φ :=
    ciInf_le hbdd_b φ
  have hinf_b_nonneg : 0 ≤ ⨅ ψ, AsymptoticSpectrum.eval p b ψ := by
    apply le_ciInf; intro ψ; exact AsymptoticSpectrum.eval_nonneg p ψ b
  calc (⨅ ψ, AsymptoticSpectrum.eval p a ψ) * (⨅ ψ, AsymptoticSpectrum.eval p b ψ)
      ≤ AsymptoticSpectrum.eval p a φ * AsymptoticSpectrum.eval p b φ :=
        mul_le_mul ha_ge hb_ge hinf_b_nonneg (AsymptoticSpectrum.eval_nonneg p φ a)
    _ = AsymptoticSpectrum.eval p (a * b) φ := (AsymptoticSpectrum.eval_mul p φ a b).symm

/-- Asymptotic rank of a power: asympRank(a^n) = asympRank(a)^n.

    Requires the hypothesis ∃φ, φ(a) ≥ 1 when n ≥ 1.
    For n = 0, this is trivially asympRank(1) = 1. -/
theorem asympRank_pow_of_spectrum [Nonempty (AsymptoticSpectrum p)] (a : S) (n : ℕ)
    (ha : n = 0 ∨ ∃ φ : AsymptoticSpectrum p, 1 ≤ AsymptoticSpectrum.eval p a φ) :
    p.asympRank (a ^ n) = p.asympRank a ^ n := by
  -- Using spectral characterization: asympRank(a^n) = sup_φ φ(a^n) = sup_φ φ(a)^n
  -- And sup_φ φ(a)^n = (sup_φ φ(a))^n when n > 0 (and equals 1 when n = 0)
  cases n with
  | zero =>
    simp only [pow_zero]
    -- asympRank(1) = sup_φ φ(1) = sup_φ 1 = 1
    -- Hypothesis for 1: φ(1) = 1 ≥ 1 always holds
    obtain ⟨φ₀⟩ := ‹Nonempty (AsymptoticSpectrum p)›
    have h1 : ∃ φ : AsymptoticSpectrum p, 1 ≤ AsymptoticSpectrum.eval p 1 φ :=
      ⟨φ₀, by rw [AsymptoticSpectrum.eval_one]⟩
    rw [asympRank_eq_iSup_spectrum p 1 h1]
    simp only [AsymptoticSpectrum.eval_one]
    exact ciSup_const
  | succ n =>
    -- For n+1, we have the hypothesis on a
    have ha' : ∃ φ : AsymptoticSpectrum p, 1 ≤ AsymptoticSpectrum.eval p a φ := by
      rcases ha with ⟨⟨⟩⟩ | h
      exact h
    rw [pow_succ, pow_succ]
    -- Derive hypotheses for a^n and a^n*a from ha'
    have ha_pow : ∃ φ : AsymptoticSpectrum p, 1 ≤ AsymptoticSpectrum.eval p (a ^ n) φ := by
      obtain ⟨φ, hφ⟩ := ha'
      use φ
      rw [AsymptoticSpectrum.eval_pow]
      exact one_le_pow₀ (n := n) hφ
    have ha_prod : ∃ φ : AsymptoticSpectrum p, 1 ≤ AsymptoticSpectrum.eval p (a ^ n * a) φ := by
      obtain ⟨φ, hφ⟩ := ha'
      use φ
      rw [AsymptoticSpectrum.eval_mul, AsymptoticSpectrum.eval_pow]
      have hpow := one_le_pow₀ (n := n) hφ
      calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
        _ ≤ AsymptoticSpectrum.eval p a φ ^ n * AsymptoticSpectrum.eval p a φ := by
          apply mul_le_mul hpow hφ (by norm_num : (0 : ℝ) ≤ 1)
          linarith
    -- asympRank(a^{n+1}) = asympRank(a^n * a) ≤ asympRank(a^n) * asympRank(a)
    --                    = asympRank(a)^n * asympRank(a) = asympRank(a)^{n+1}
    apply le_antisymm
    · calc p.asympRank (a ^ n * a)
          ≤ p.asympRank (a ^ n) * p.asympRank a :=
            asympRank_mul_le_of_spectrum p _ _ ha_pow ha' ha_prod
        _ = p.asympRank a ^ n * p.asympRank a := by
            congr 1
            exact asympRank_pow_of_spectrum a n (Or.inr ha')
    · -- For the reverse: asympRank(a)^n * asympRank(a) ≤ asympRank(a^n * a)
      -- This follows from spectral point lower bound: for any φ, φ(a)^n * φ(a) ≤ asympRank(a^n * a)
      rw [asympRank_eq_iSup_spectrum p a ha', asympRank_eq_iSup_spectrum p (a ^ n * a) ha_prod]
      have hbdd : BddAbove (Set.range (AsymptoticSpectrum.eval p a)) := by
        use p.rank a
        intro x hx
        obtain ⟨φ, rfl⟩ := hx
        exact AsymptoticSpectrum.eval_le_rank p φ a
      have hbdd_pow : BddAbove (Set.range (AsymptoticSpectrum.eval p (a ^ n * a))) := by
        use p.rank (a ^ n * a)
        intro x hx
        obtain ⟨φ, rfl⟩ := hx
        exact AsymptoticSpectrum.eval_le_rank p φ (a ^ n * a)
      -- Use that the φ maximizing φ(a) achieves (sup φ(a))^n * sup φ(a) = φmax(a)^n * φmax(a)
      obtain ⟨φmax_a, hmax_a⟩ := asympRank_eq_max_spectrum p a ha'
      rw [asympRank_eq_iSup_spectrum p a ha'] at hmax_a
      -- Goal: (sup φ(a))^n * (sup φ(a)) ≤ sup φ(a^n * a)
      calc (⨆ φ, AsymptoticSpectrum.eval p a φ) ^ n * (⨆ φ, AsymptoticSpectrum.eval p a φ)
          = AsymptoticSpectrum.eval p a φmax_a ^ n * AsymptoticSpectrum.eval p a φmax_a := by
            rw [hmax_a]
        _ = AsymptoticSpectrum.eval p (a ^ n) φmax_a * AsymptoticSpectrum.eval p a φmax_a := by
            rw [AsymptoticSpectrum.eval_pow]
        _ = AsymptoticSpectrum.eval p (a ^ n * a) φmax_a := by
            rw [AsymptoticSpectrum.eval_mul]
        _ ≤ ⨆ φ, AsymptoticSpectrum.eval p (a ^ n * a) φ := le_ciSup hbdd_pow φmax_a

/-- Asymptotic rank is monotone: a ≤_P b → asympRank(a) ≤ asympRank(b).

    Requires the hypothesis ∃φ, φ(x) ≥ 1 for x ∈ {a, b}. -/
theorem asympRank_mono_of_spectrum [Nonempty (AsymptoticSpectrum p)] {a b : S}
    (ha : ∃ φ : AsymptoticSpectrum p, 1 ≤ AsymptoticSpectrum.eval p a φ)
    (hb : ∃ φ : AsymptoticSpectrum p, 1 ≤ AsymptoticSpectrum.eval p b φ)
    (hab : p.rel a b) : p.asympRank a ≤ p.asympRank b := by
  -- Using spectral characterization
  rw [asympRank_eq_iSup_spectrum p a ha, asympRank_eq_iSup_spectrum p b hb]
  have hbdd_b : BddAbove (Set.range (AsymptoticSpectrum.eval p b)) := by
    use p.rank b; intro x hx; obtain ⟨φ, rfl⟩ := hx
    exact AsymptoticSpectrum.eval_le_rank p φ b
  apply ciSup_mono hbdd_b
  intro φ
  exact AsymptoticSpectrum.eval_mono p φ hab

/-- Asymptotic subrank is monotone: a ≤_P b → asympSubrank(a) ≤ asympSubrank(b) -/
theorem asympSubrank_mono_of_spectrum [Nonempty (AsymptoticSpectrum p)] {a b : S}
    (ha : p.IsGapped a) (hb : p.IsGapped b) (hab : p.rel a b)
    (harch : ∀ x : S, p.rel x 0 ∨ p.rel 1 x) :
    p.asympSubrank a ≤ p.asympSubrank b := by
  -- Using spectral characterization for gapped elements
  rw [asympSubrank_eq_iInf_spectrum p a ha harch, asympSubrank_eq_iInf_spectrum p b hb harch]
  have hbdd_a : BddBelow (Set.range (AsymptoticSpectrum.eval p a)) := by
    use 0; intro x hx; obtain ⟨φ, rfl⟩ := hx
    exact AsymptoticSpectrum.eval_nonneg p φ a
  apply ciInf_mono hbdd_a
  intro φ
  exact AsymptoticSpectrum.eval_mono p φ hab

end StrassenPreorder

end AsymptoticSpectrumDuality
