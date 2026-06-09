/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import AsymptoticTensorRankSemicontinuity.SpectrumDescend
import AsymptoticTensorRankSemicontinuity.ZariskiSublevel
import AsymptoticTensorRankSemicontinuity.FieldExtension
import AsymptoticTensorRankSemicontinuity.SpectralPointExtension

/-!
# §3 main theorem: well-orderedness across formats for the asymptotic spectrum

Source: the semicontinuity manuscript,
lines 818-820 (statement) and 1054-1067 (proof).

* `asympSpectrum_values_wellOrdered` — **Theorem 3.1** (tex:812-814,
  `\label{th:spec-well-ord}` / `\label{thm:spectral points well ordered}`).
-/

namespace Semicontinuity

universe u

variable {F : Type u} [Field F]

/-! ## Infinite-field proof skeleton (paper tex:1050-1061)

The paper proves Theorem 3.1 first for infinite fields, by induction on `k`.
The formal inputs below are named so downstream files can refer to their precise
mathematical statements.
-/

/-- Pair-unit growth extracted uniformly from the Case 1 hypothesis.

This packages the finite minimum over ordered pairs `i ≠ j` of the exponents
obtained from `F(⟨2⟩_{i,j}) > 1` and multiplicativity of pair-units. -/
private theorem pair_units_uniform_power_lower_bound {k : ℕ} [Infinite F]
    (hk : 3 ≤ k) (Fspec : SpectralPoint k F)
    (hpair : ∀ (i j : Fin k) (hij : i ≠ j),
      1 < Fspec.toFun (unitPairTensor (F := F) 2 i j hij)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (i j : Fin k) (hij : i ≠ j) (r : ℕ+),
        (r : ℝ) ^ c ≤ Fspec.toFun (unitPairTensor (F := F) r i j hij) := by
  classical
  let Pair := {p : Fin k × Fin k // p.1 ≠ p.2}
  let pairExp : Pair → ℝ := fun p =>
    (Real.log (Fspec.toFun
        (unitPairTensor (F := F) 2 p.1.1 p.1.2 p.2)) / Real.log 2) / 2
  have hpairExp_pos : ∀ p : Pair, 0 < pairExp p := by
    intro p
    have hx_gt_one :
        1 < Fspec.toFun (unitPairTensor (F := F) 2 p.1.1 p.1.2 p.2) :=
      hpair p.1.1 p.1.2 p.2
    have hlogx_pos :
        0 < Real.log (Fspec.toFun
          (unitPairTensor (F := F) 2 p.1.1 p.1.2 p.2)) :=
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
  let x : ℝ := Fspec.toFun (unitPairTensor (F := F) 2 i j hij)
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
        Fspec.toFun (unitPairTensor (F := F)
          (⟨2 ^ a, pow_pos (by norm_num : (0 : ℕ) < 2) a⟩ : ℕ+) i j hij) =
          x ^ a := by
    intro a
    induction a with
    | zero =>
        change Fspec.toFun (unitPairTensor (F := F) 1 i j hij) = 1
        simpa [x] using Fspec.unitPair_one i j hij
    | succ a ih =>
        let powTwo : ℕ → ℕ+ :=
          fun n => ⟨2 ^ n, pow_pos (by norm_num : (0 : ℕ) < 2) n⟩
        have hmul := Fspec.unitPair_mul i j hij (powTwo a) (2 : ℕ+)
        have hfmt : powTwo (a + 1) = powTwo a * (2 : ℕ+) := by
          apply PNat.coe_injective
          simp [powTwo, pow_succ, Nat.mul_comm]
        change Fspec.toFun (unitPairTensor (F := F) (powTwo (a + 1)) i j hij) =
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
        Fspec.toFun (unitPairTensor (F := F) (powTwo a) i j hij) ≤
          Fspec.toFun (unitPairTensor (F := F) r i j hij) :=
      Fspec.mono
        (unitPairTensor (F := F) (powTwo a) i j hij)
        (unitPairTensor (F := F) r i j hij)
        (unitPairTensor_restricts_of_le (F := F) i j hij hpow_le_r)
    have hx_pow_le :
        x ^ a ≤ Fspec.toFun (unitPairTensor (F := F) r i j hij) := by
      simpa [powTwo] using (hpow_two_value a).symm.le.trans hmono
    exact hreduce_exp.trans (hrpow_le.trans (hpow_bound_eq.le.trans hx_pow_le))

/-- Narrow bridge for paper tex:1056-1058 after Corollary 3.3 has chosen the
pair `j`.

Given
`flatRank_i(T)^(1/(k-1)) ≤ subrankPair T i j`, this helper unpacks the
`subrankPair` supremum into a pair-unit restriction witness, applies
monotonicity, and performs the real-power arithmetic to obtain the exponent
`cPair/(k-1)`. -/
private theorem flatRank_power_le_of_large_subrankPair {k : ℕ}
    (hk : 3 ≤ k) (Fspec : SpectralPoint k F) {cPair : ℝ} (hcPair : 0 < cPair)
    (hunit : ∀ (i j : Fin k) (hij : i ≠ j) (r : ℕ+),
      (r : ℝ) ^ cPair ≤ Fspec.toFun (unitPairTensor (F := F) r i j hij))
    {d : Fin k → ℕ+} (T : KTensor F d) (i j : Fin k) (hij : i ≠ j)
    (hlarge :
      (flatRank T {i} : ℝ) ^ ((1 : ℝ) / ((k : ℝ) - 1)) ≤ subrankPair T i j) :
      (flatRank T {i} : ℝ) ^ (cPair / ((k : ℝ) - 1)) ≤ Fspec.toFun T := by
  classical
  have hk_real : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hkden_pos : 0 < (k : ℝ) - 1 := by linarith
  have hexp_pos : 0 < cPair / ((k : ℝ) - 1) := div_pos hcPair hkden_pos
  have hzero_restricts :
      ∀ {dS dT : Fin k → ℕ+},
        Restricts (F := F) (0 : KTensor F dS) (0 : KTensor F dT) := by
    intro dS dT
    refine ⟨fun _ => 0, ?_⟩
    intro jdx
    simp
  have hF_zero : Fspec.toFun (0 : KTensor F d) = 0 := by
    let dsum : Fin k → ℕ+ := fun ℓ => d ℓ + d ℓ
    have hle₁ :
        Fspec.toFun (0 : KTensor F d) ≤ Fspec.toFun (0 : KTensor F dsum) :=
      Fspec.mono (0 : KTensor F d) (0 : KTensor F dsum) hzero_restricts
    have hle₂ :
        Fspec.toFun (0 : KTensor F dsum) ≤ Fspec.toFun (0 : KTensor F d) :=
      Fspec.mono (0 : KTensor F dsum) (0 : KTensor F d) hzero_restricts
    have hsame :
        Fspec.toFun (0 : KTensor F dsum) = Fspec.toFun (0 : KTensor F d) :=
      le_antisymm hle₂ hle₁
    have hsum_zero :
        (0 : KTensor F d) ⊕ₜ (0 : KTensor F d) = (0 : KTensor F dsum) := by
      ext idx
      simp [directSumTensor, dsum]
    have hadd := Fspec.add (0 : KTensor F d) (0 : KTensor F d)
    have hadd' :
        Fspec.toFun (0 : KTensor F dsum) =
          Fspec.toFun (0 : KTensor F d) + Fspec.toFun (0 : KTensor F d) := by
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
        Restricts (unitPairTensor (F := F) rSub i j hij) T := by
      let S : Set ℕ := { r : ℕ | ∃ hr : 0 < r,
        Restricts (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) T }
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
            (unitPairTensor (F := F) rSub i j hij) ≤
          Fspec.toFun T :=
      Fspec.mono
        (unitPairTensor (F := F) rSub i j hij) T
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

/-- Corollary 3.3 plus monotonicity turns uniform pair-unit growth into a
singleton-flattening power bound.

This is the formal bridge from `exists_large_subrankPair` and the defining
restriction witness for `subrankPair` to the displayed inequality. -/
private theorem flatRank_power_le_of_pair_units {k : ℕ} [Infinite F]
    (hk : 3 ≤ k) (Fspec : SpectralPoint k F) {cPair : ℝ} (hcPair : 0 < cPair)
    (hunit : ∀ (i j : Fin k) (hij : i ≠ j) (r : ℕ+),
      (r : ℝ) ^ cPair ≤ Fspec.toFun (unitPairTensor (F := F) r i j hij)) :
    ∀ {d : Fin k → ℕ+} (T : KTensor F d) (i : Fin k),
      (flatRank T {i} : ℝ) ^ (cPair / ((k : ℝ) - 1)) ≤ Fspec.toFun T := by
  classical
  intro d T i
  have hFcard : ((flatRank T {i} : ℕ) : Cardinal) < Cardinal.mk F :=
    Cardinal.natCast_lt_aleph0.trans_le (Cardinal.aleph0_le_mk F)
  have hk2 : 2 ≤ k := by omega
  obtain ⟨j, hij, hlarge⟩ :=
    exists_large_subrankPair (F := F) hk2 T i hFcard
  exact flatRank_power_le_of_large_subrankPair
    (F := F) hk Fspec hcPair hunit T i j hij hlarge

/-- **Case 1 power bound** (paper tex:1056-1057).

If every pair-unit has spectral value strictly larger than `1`, then Corollary
3.3 (`exists_large_subrankPair`) and monotonicity of the spectral point give a
uniform positive power lower bound for every singleton flattening rank. -/
private theorem pair_gt_two_implies_flatRank_power_lower_bound {k : ℕ} [Infinite F]
    (hk : 3 ≤ k) (Fspec : SpectralPoint k F)
    (hpair : ∀ (i j : Fin k) (hij : i ≠ j),
      1 < Fspec.toFun (unitPairTensor (F := F) 2 i j hij)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {d : Fin k → ℕ+} (T : KTensor F d) (i : Fin k),
        (flatRank T {i} : ℝ) ^ c ≤ Fspec.toFun T := by
  classical
  obtain ⟨cPair, hcPair, hunit⟩ :=
    pair_units_uniform_power_lower_bound (F := F) hk Fspec hpair
  refine ⟨cPair / ((k : ℝ) - 1), ?_, ?_⟩
  · have hk_real : (3 : ℝ) ≤ k := by exact_mod_cast hk
    exact div_pos hcPair (by linarith)
  · exact flatRank_power_le_of_pair_units (F := F) hk Fspec hcPair hunit

/-- Spectral points take value `0` on zero tensors.

The proof uses restriction-equivalence between zero tensors in any two formats
and additivity for `0 ⊕ₜ 0`. -/
private lemma SpectralPoint.map_zero {k : ℕ} (Fspec : SpectralPoint k F)
    {d : Fin k → ℕ+} :
    Fspec.toFun (0 : KTensor F d) = 0 := by
  classical
  have hzero_restricts :
      ∀ {dS dT : Fin k → ℕ+},
        Restricts (F := F) (0 : KTensor F dS) (0 : KTensor F dT) := by
    intro dS dT
    refine ⟨fun _ => 0, ?_⟩
    intro jdx
    simp
  let dsum : Fin k → ℕ+ := fun ℓ => d ℓ + d ℓ
  have hle₁ :
      Fspec.toFun (0 : KTensor F d) ≤ Fspec.toFun (0 : KTensor F dsum) :=
    Fspec.mono (0 : KTensor F d) (0 : KTensor F dsum) hzero_restricts
  have hle₂ :
      Fspec.toFun (0 : KTensor F dsum) ≤ Fspec.toFun (0 : KTensor F d) :=
    Fspec.mono (0 : KTensor F dsum) (0 : KTensor F d) hzero_restricts
  have hsame :
      Fspec.toFun (0 : KTensor F dsum) = Fspec.toFun (0 : KTensor F d) :=
    le_antisymm hle₂ hle₁
  have hsum_zero :
      (0 : KTensor F d) ⊕ₜ (0 : KTensor F d) = (0 : KTensor F dsum) := by
    ext idx
    simp [directSumTensor, dsum]
  have hadd := Fspec.add (0 : KTensor F d) (0 : KTensor F d)
  have hadd' :
      Fspec.toFun (0 : KTensor F dsum) =
        Fspec.toFun (0 : KTensor F d) + Fspec.toFun (0 : KTensor F d) := by
    rw [← hsum_zero]
    exact hadd
  linarith

private lemma le_rpow_one_div_of_rpow_le {a M c : ℝ}
    (ha : 0 ≤ a) (hc : 0 < c) (h : a ^ c ≤ M) :
    a ≤ M ^ ((1 : ℝ) / c) := by
  have hinv : 0 ≤ (1 : ℝ) / c := by positivity
  have hroot :
      (a ^ c) ^ ((1 : ℝ) / c) ≤ M ^ ((1 : ℝ) / c) :=
    Real.rpow_le_rpow (Real.rpow_nonneg ha c) h hinv
  have hsimp : (a ^ c) ^ ((1 : ℝ) / c) = a := by
    rw [← Real.rpow_mul ha]
    have hcne : c ≠ 0 := ne_of_gt hc
    field_simp [hcne]
    rw [Real.rpow_one]
  rwa [hsimp] at hroot

/-- The trivial F_1-boundedness fact (paper tex:534-536): every `X : KTensor F d'`
restricts to `unitTensor ⟨∏ d'_i⟩` via the standard-basis decomposition, so
`Fspec X ≤ ∏ d'_i` by `Fspec.mono` + `Fspec.normalize`.

Field-general port of `Fspec_le_prod_dims` (EuclideanClosed.lean). -/
private lemma Fspec_le_prod_dims_F {k : ℕ} (hk : 1 ≤ k) {d' : Fin k → ℕ+}
    (Fspec : SpectralPoint k F) (X : KTensor F d') :
    Fspec.toFun X ≤ ∏ i, (d' i : ℕ) := by
  classical
  set Idx := ∀ i : Fin k, Fin (d' i) with hIdx
  set N : ℕ := Fintype.card Idx with hN
  have hcard : N = ∏ i, (d' i : ℕ) := by simp [hN, hIdx, Fintype.card_pi]
  have hNpos : 0 < N := by
    rw [hcard]
    exact Finset.prod_pos (fun i _ => (d' i).pos)
  let e : Fin N ≃ Idx := (Fintype.equivFin Idx).symm
  have hrestr : Restricts X (unitTensor (F := F) (k := k) ⟨N, hNpos⟩) := by
    refine ⟨fun i => fun (j : Fin (d' i)) (c : Fin N) =>
      if i = ⟨0, hk⟩ then (if j = (e c) i then X (e c) else 0)
                     else (if j = (e c) i then 1 else 0), ?_⟩
    intro jdx
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
    rw [hX_eq]
    refine Finset.sum_of_injOn (e := fun c : Fin N => (fun _ : Fin k => c))
      ?_ ?_ ?_ ?_
    · intro a _ b _ hab
      have := congrFun hab ⟨0, hk⟩
      simpa using this
    · intro c _; exact Finset.mem_univ _
    · intro idx _ hidx
      have hne : ¬ (∀ i j : Fin k, idx i = idx j) := by
        intro hconst
        apply hidx
        refine ⟨idx ⟨0, hk⟩, by simp, ?_⟩
        funext i
        exact (hconst ⟨0, hk⟩ i)
      have huz : unitTensor (F := F) (k := k) ⟨N, hNpos⟩ idx = 0 := by
        simp only [unitTensor]; rw [if_neg hne]
      rw [huz, mul_zero]
    · intro c _
      have hud : unitTensor (F := F) (k := k) ⟨N, hNpos⟩ (fun _ : Fin k => c) = 1 := by
        simp [unitTensor]
      simp only [hud, mul_one]
      exact (hterm c).symm
  have hmono := Fspec.mono _ _ hrestr
  rw [Fspec.normalize (k := k) (F := F) ⟨N, hNpos⟩] at hmono
  have hmono' : Fspec.toFun X ≤ (N : ℝ) := by exact_mod_cast hmono
  rw [hcard] at hmono'
  exact_mod_cast hmono'

/-- Every spectral point `Fspec ∈ Δ(F, k)` induces an admissible functional on a
fixed format `d` via `toFun n T := Real.toNNReal (Fspec (regroupingMap d n T))`
(paper tex:783).

Field-general port of `Fspec_regroupingMap_admissible_exists` (EuclideanClosed.lean). -/
private lemma Fspec_regroupingMap_admissible_exists_F {k : ℕ} (d : Fin k → ℕ+)
    (Fspec : SpectralPoint k F) :
    ∃ Func : AdmissibleFunctional F (KTensor F d),
      ∀ (n : ℕ+) (T : TensorPower F (n : ℕ) (KTensor F d)),
        Func.toFun n T = Real.toNNReal (Fspec.toFun (regroupingMap d n T)) := by
  classical
  have absurd_at_zero : k = 0 →
      ∃ Func : AdmissibleFunctional F (KTensor F d),
        ∀ (n : ℕ+) (T : TensorPower F (n : ℕ) (KTensor F d)),
          Func.toFun n T = Real.toNNReal (Fspec.toFun (regroupingMap d n T)) := by
    intro hk0
    subst hk0
    have h1 :
        Restricts (unitTensor (F := F) (k := 0) 1)
          (unitTensor (F := F) (k := 0) 2) := by
      refine Restricts.of_eq_cast (fun (i : Fin 0) => i.elim0) ?_
      intro jdx
      simp [unitTensor]
    have h2 :
        Restricts (unitTensor (F := F) (k := 0) 2)
          (unitTensor (F := F) (k := 0) 1) := by
      refine Restricts.of_eq_cast (fun (i : Fin 0) => i.elim0) ?_
      intro jdx
      simp [unitTensor]
    have h12 := Fspec.mono _ _ h1
    have h21 := Fspec.mono _ _ h2
    have h1eq2 :
        Fspec.toFun (unitTensor (F := F) (k := 0) 1) =
          Fspec.toFun (unitTensor (F := F) (k := 0) 2) := le_antisymm h12 h21
    have hn1 := Fspec.normalize (k := 0) (F := F) (1 : ℕ+)
    have hn2 := Fspec.normalize (k := 0) (F := F) (2 : ℕ+)
    rw [hn1, hn2] at h1eq2
    norm_num at h1eq2
  by_cases hk : 1 ≤ k
  swap
  · exact absurd_at_zero (by omega)
  have Fspec_cast :
      ∀ {d₁ d₂ : Fin k → ℕ+} (hfmt : d₁ = d₂) (T : KTensor F d₁),
        Fspec.toFun (hfmt ▸ T) = Fspec.toFun T := by
    intro d₁ d₂ hfmt T
    subst hfmt
    rfl
  have smul_Restricts :
      ∀ {d' : Fin k → ℕ+} (α : F) (hα : α ≠ 0) (X : KTensor F d'),
        Restricts (α • X) X := by
    intro d' α _hα X
    refine ⟨fun i => if (i : ℕ) = 0 then
              (α : F) • (1 : Matrix (Fin (d' i)) (Fin (d' i)) F)
            else (1 : Matrix (Fin (d' i)) (Fin (d' i)) F), ?_⟩
    intro jdx
    rw [Finset.sum_eq_single jdx]
    · have hprod :
          (∏ i : Fin k,
            (if (i : ℕ) = 0 then
                (α : F) • (1 : Matrix (Fin (d' i)) (Fin (d' i)) F)
              else (1 : Matrix (Fin (d' i)) (Fin (d' i)) F)) (jdx i) (jdx i)) = α := by
        have hk_pos : 0 < k := hk
        have h0_mem : (⟨0, hk_pos⟩ : Fin k) ∈ (Finset.univ : Finset (Fin k)) :=
          Finset.mem_univ _
        rw [← Finset.mul_prod_erase _ _ h0_mem]
        have hzero_branch :
            (if ((⟨0, hk_pos⟩ : Fin k) : ℕ) = 0 then
                (α : F) • (1 : Matrix (Fin (d' ⟨0, hk_pos⟩)) (Fin (d' ⟨0, hk_pos⟩)) F)
              else (1 : Matrix (Fin (d' ⟨0, hk_pos⟩)) (Fin (d' ⟨0, hk_pos⟩)) F))
              (jdx ⟨0, hk_pos⟩) (jdx ⟨0, hk_pos⟩) = α := by
          simp [Matrix.one_apply_eq]
        rw [hzero_branch]
        have hrest_eq_one :
            (∏ i ∈ (Finset.univ : Finset (Fin k)).erase ⟨0, hk_pos⟩,
              (if (i : ℕ) = 0 then
                  (α : F) • (1 : Matrix (Fin (d' i)) (Fin (d' i)) F)
                else (1 : Matrix (Fin (d' i)) (Fin (d' i)) F)) (jdx i) (jdx i)) = 1 := by
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
              (α : F) • (1 : Matrix (Fin (d' i₀)) (Fin (d' i₀)) F)
            else (1 : Matrix (Fin (d' i₀)) (Fin (d' i₀)) F)) (jdx i₀) (idx i₀) = 0 := by
        by_cases h0 : (i₀ : ℕ) = 0
        · simp [h0, hi₀]
        · simp [h0, hi₀]
      have hprod_zero :
          (∏ i : Fin k, (if (i : ℕ) = 0 then
                (α : F) • (1 : Matrix (Fin (d' i)) (Fin (d' i)) F)
              else (1 : Matrix (Fin (d' i)) (Fin (d' i)) F)) (jdx i) (idx i)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i₀) hzero_entry
      rw [hprod_zero, zero_mul]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim
  have Restricts_smul :
      ∀ {d' : Fin k → ℕ+} (α : F) (hα : α ≠ 0) (X : KTensor F d'),
        Restricts X (α • X) := by
    intro d' α hα X
    have hα_inv : α⁻¹ ≠ 0 := inv_ne_zero hα
    have h := smul_Restricts (α⁻¹) hα_inv (α • X)
    have hcancel : α⁻¹ • (α • X) = X := by
      rw [smul_smul, inv_mul_cancel₀ hα, one_smul]
    rw [hcancel] at h
    exact h
  have Fspec_smul_inv :
      ∀ {d' : Fin k → ℕ+} (α : F) (hα : α ≠ 0) (X : KTensor F d'),
        Fspec.toFun (α • X) = Fspec.toFun X := by
    intro d' α hα X
    apply le_antisymm
    · exact Fspec.mono _ _ (smul_Restricts α hα X)
    · exact Fspec.mono _ _ (Restricts_smul α hα X)
  have zero_Restricts :
      ∀ {dS dT : Fin k → ℕ+} (X : KTensor F dT),
        Restricts (0 : KTensor F dS) X := by
    intro dS dT X
    refine ⟨fun i => (0 : Matrix (Fin (dS i)) (Fin (dT i)) F), ?_⟩
    intro jdx
    change (0 : KTensor F dS) jdx
        = ∑ idx : (∀ i : Fin k, Fin (dT i)),
          (∏ i, (0 : Matrix (Fin (dS i)) (Fin (dT i)) F) (jdx i) (idx i)) * X idx
    have hk_pos : 0 < k := hk
    have h0_mem : (⟨0, hk_pos⟩ : Fin k) ∈ (Finset.univ : Finset (Fin k)) :=
      Finset.mem_univ _
    simp only [Pi.zero_apply]
    apply (Finset.sum_eq_zero _).symm
    intro idx _
    have hprod0 :
        (∏ i, (0 : Matrix (Fin (dS i)) (Fin (dT i)) F) (jdx i) (idx i)) = 0 := by
      apply Finset.prod_eq_zero h0_mem
      simp
    rw [hprod0, zero_mul]
  have Fspec_zero :
      ∀ {d' : Fin k → ℕ+}, Fspec.toFun (0 : KTensor F d') = 0 := by
    intro d'
    have hsum_eq_zero :
        (0 : KTensor F d') ⊕ₜ (0 : KTensor F d') = (0 : KTensor F (fun i => d' i + d' i)) := by
      funext idx
      unfold directSumTensor
      split_ifs <;> rfl
    have hadd := Fspec.add (dS := d') (dT := d') (0 : KTensor F d') (0 : KTensor F d')
    rw [hsum_eq_zero] at hadd
    have hr1 : Restricts (0 : KTensor F (fun i => d' i + d' i)) (0 : KTensor F d') :=
      zero_Restricts _
    have hr2 : Restricts (0 : KTensor F d') (0 : KTensor F (fun i => d' i + d' i)) :=
      zero_Restricts _
    have heq : Fspec.toFun (0 : KTensor F (fun i => d' i + d' i)) =
        Fspec.toFun (0 : KTensor F d') :=
      le_antisymm (Fspec.mono _ _ hr1) (Fspec.mono _ _ hr2)
    rw [heq] at hadd
    linarith
  have Fspec_nonneg :
      ∀ {d' : Fin k → ℕ+} (X : KTensor F d'), 0 ≤ Fspec.toFun X := by
    intro d' X
    have hz : Fspec.toFun (0 : KTensor F d') ≤ Fspec.toFun X :=
      Fspec.mono _ _ (zero_Restricts X)
    rw [Fspec_zero] at hz
    exact hz
  have sum_Restricts_directSum :
      ∀ {d' : Fin k → ℕ+} (A B : KTensor F d'),
        Restricts (A + B) (A ⊕ₜ B) := by
    intro d' A B
    let foldMat : ∀ i : Fin k, Matrix (Fin (d' i)) (Fin (d' i + d' i)) F :=
      fun i j idx =>
        if idx.val = j.val ∨ idx.val = (d' i : ℕ) + j.val then 1 else 0
    refine ⟨foldMat, ?_⟩
    intro jdx
    set sumLHS :
        ∀ i : Fin k, (Fin (d' i + d' i)) := fun _ => 0 with _hsum_def
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
      by_contra hprod_ne
      have hper_leg : ∀ i : Fin k,
          (idx i).val = (jdx i).val ∨ (idx i).val = (d' i : ℕ) + (jdx i).val := by
        intro i
        by_contra h
        push_neg at h
        apply hprod_ne
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [foldMat, h.1, h.2]
      let c : Fin k → Fin 2 := fun i =>
        if (idx i).val = (jdx i).val then 0 else 1
      have hidx_eq : idx = chooseIdx c := by
        funext i
        rcases hper_leg i with h1 | h2
        · have hci : c i = 0 := by simp [c, h1]
          apply Fin.ext
          show (idx i).val = (chooseIdx c i).val
          simp [chooseIdx, hci, h1]
        · have hjlt : (jdx i).val < (d' i : ℕ) := (jdx i).isLt
          have hne_first : (idx i).val ≠ (jdx i).val := by
            rw [h2]; omega
          have hci : c i = 1 := by simp [c, hne_first]
          apply Fin.ext
          show (idx i).val = (chooseIdx c i).val
          simp [chooseIdx, hci, h2]
      exact hne c hidx_eq
    have hds_value : ∀ c : Fin k → Fin 2,
        (A ⊕ₜ B) (chooseIdx c) =
          (if ∀ i, c i = 0 then A jdx else 0) +
          (if ∀ i, c i = 1 then B jdx else 0) := by
      intro c
      unfold directSumTensor
      by_cases hall0 : ∀ i, c i = 0
      · have hSall : ∀ i, (chooseIdx c i).val < (d' i : ℕ) := by
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
      · by_cases hall1 : ∀ i, c i = 1
        · have hnot_first : ¬ ∀ i, (chooseIdx c i).val < (d' i : ℕ) := by
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
        · push_neg at hall0
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
          have hnot_first : ¬ ∀ i, (chooseIdx c i).val < (d' i : ℕ) := by
            push_neg
            refine ⟨i_second, ?_⟩
            simp [chooseIdx, hci_second_one]
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
        · have hci_one : c i = 1 := by
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
    change (A + B) jdx
        = ∑ idx : (∀ i, Fin (d' i + d' i)),
          (∏ i, foldMat i (jdx i) (idx i)) * (A ⊕ₜ B) idx
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
    have himg_eq :
        ∑ idx ∈ Finset.image chooseIdx Finset.univ,
            (∏ i, foldMat i (jdx i) (idx i)) * (A ⊕ₜ B) idx
          = ∑ c : Fin k → Fin 2,
            (∏ i, foldMat i (jdx i) (chooseIdx c i)) * (A ⊕ₜ B) (chooseIdx c) :=
      Finset.sum_image (fun a _ b _ => hchooseIdx_inj.eq_iff.mp)
    rw [himg_eq, hcompl_zero, add_zero]
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
    rw [Finset.sum_add_distrib]
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
  refine ⟨{
    toFun := fun n T => Real.toNNReal (Fspec.toFun (regroupingMap d n T))
    subadd := ?_
    submul := ?_
    perm_inv := ?_
    scalar_inv := ?_
    bdd_one := ?_
  }, ?_⟩
  · intro n T S
    have hmap : regroupingMap d n (T + S) =
        regroupingMap d n T + regroupingMap d n S := by
      exact LinearMap.map_add _ T S
    change Real.toNNReal (Fspec.toFun (regroupingMap d n (T + S)))
        ≤ Real.toNNReal (Fspec.toFun (regroupingMap d n T)) +
            Real.toNNReal (Fspec.toFun (regroupingMap d n S))
    rw [hmap]
    set A := regroupingMap d n T
    set B := regroupingMap d n S
    have hadd := Fspec.add A B
    have hbridge : Restricts (A + B) (A ⊕ₜ B) := sum_Restricts_directSum A B
    have hle : Fspec.toFun (A + B) ≤ Fspec.toFun (A ⊕ₜ B) :=
      Fspec.mono _ _ hbridge
    rw [hadd] at hle
    have hAnn : 0 ≤ Fspec.toFun A := Fspec_nonneg A
    have hBnn : 0 ≤ Fspec.toFun B := Fspec_nonneg B
    calc Real.toNNReal (Fspec.toFun (A + B))
        ≤ Real.toNNReal (Fspec.toFun A + Fspec.toFun B) :=
          Real.toNNReal_mono hle
      _ = Real.toNNReal (Fspec.toFun A) + Real.toNNReal (Fspec.toFun B) :=
          Real.toNNReal_add hAnn hBnn
  · intro n n' T S
    set hfmt : formatPow d ⟨(n : ℕ) + (n' : ℕ), Nat.add_pos_left n.pos _⟩
        = fun i => formatPow d n i * formatPow d n' i :=
      formatPow_add_eq_mul d n n'
    have hbridge :
        (hfmt ▸ regroupingMap d ⟨(n : ℕ) + (n' : ℕ), Nat.add_pos_left n.pos _⟩
            ((tensorPowerAdd F (KTensor F d) (n : ℕ) (n' : ℕ)).symm (T ⊗ₜ[F] S)))
          = (regroupingMap d n T) ⊠ (regroupingMap d n' S) :=
      regroupingMap_tensorPowerAdd_symm_eq_kron_cast (F := F) d n n' T S
    have hLHS_eq :
        Fspec.toFun
          (regroupingMap d ⟨(n : ℕ) + (n' : ℕ), Nat.add_pos_left n.pos _⟩
            ((tensorPowerAdd F (KTensor F d) (n : ℕ) (n' : ℕ)).symm (T ⊗ₜ[F] S)))
          =
        Fspec.toFun ((regroupingMap d n T) ⊠ (regroupingMap d n' S)) := by
      rw [← hbridge, Fspec_cast hfmt]
    have hmul := Fspec.mult (regroupingMap d n T) (regroupingMap d n' S)
    change Real.toNNReal
        (Fspec.toFun
          (regroupingMap d ⟨(n : ℕ) + (n' : ℕ), Nat.add_pos_left n.pos _⟩
            ((tensorPowerAdd F (KTensor F d) (n : ℕ) (n' : ℕ)).symm (T ⊗ₜ[F] S))))
        ≤ Real.toNNReal (Fspec.toFun (regroupingMap d n T)) *
            Real.toNNReal (Fspec.toFun (regroupingMap d n' S))
    rw [hLHS_eq, hmul]
    rw [Real.toNNReal_mul (Fspec_nonneg _)]
  · intro ℓ nVec σ Ts hpos₁ hpos₂
    change Real.toNNReal
        (Fspec.toFun
          (regroupingMap d ⟨_, hpos₁⟩
            (tensorPowerBlock F (KTensor F d) (fun i => (nVec i : ℕ)) Ts)))
        = Real.toNNReal
          (Fspec.toFun
            (regroupingMap d ⟨_, hpos₂⟩
              (tensorPowerBlock F (KTensor F d) (fun i => ((nVec (σ i)) : ℕ))
                (fun i => Ts (σ i)))))
    set hfmt := formatPow_block_perm_eq d nVec σ hpos₁ hpos₂
    set LHS := regroupingMap d ⟨_, hpos₁⟩
          (tensorPowerBlock F (KTensor F d) (fun i => (nVec i : ℕ)) Ts)
    set RHS := regroupingMap d ⟨_, hpos₂⟩
          (tensorPowerBlock F (KTensor F d) (fun i => ((nVec (σ i)) : ℕ))
            (fun i => Ts (σ i)))
    have hLHS_cast : Fspec.toFun LHS = Fspec.toFun (hfmt ▸ LHS) :=
      (Fspec_cast hfmt LHS).symm
    obtain ⟨φ_σ, hLHS_eq⟩ := regroupingMap_tensorPowerBlock_perm_eq_legPerm
      (F := F) d nVec σ Ts hpos₁ hpos₂
    have hperm_le : Fspec.toFun (RHS.legPerm φ_σ) ≤ Fspec.toFun RHS :=
      Fspec.mono _ _ (KTensor.legPerm_Restricts RHS φ_σ)
    have hperm_ge : Fspec.toFun RHS ≤ Fspec.toFun (RHS.legPerm φ_σ) :=
      Fspec.mono _ _ (KTensor.Restricts_legPerm RHS φ_σ)
    have hperm_eq : Fspec.toFun (RHS.legPerm φ_σ) = Fspec.toFun RHS :=
      le_antisymm hperm_le hperm_ge
    rw [hLHS_cast, hLHS_eq, hperm_eq]
  · intro n α hα T
    show Real.toNNReal (Fspec.toFun (regroupingMap d n (α • T)))
        = Real.toNNReal (Fspec.toFun (regroupingMap d n T))
    rw [LinearMap.map_smul]
    rw [Fspec_smul_inv α hα]
  · refine ⟨((∏ i, ((formatPow d (1 : ℕ+) i : ℕ))) : NNReal), ?_⟩
    intro T
    show Real.toNNReal (Fspec.toFun (regroupingMap d 1 T))
        ≤ ((∏ i, ((formatPow d (1 : ℕ+) i : ℕ))) : NNReal)
    have hbound := Fspec_le_prod_dims_F hk Fspec (regroupingMap d 1 T)
    refine (Real.toNNReal_le_toNNReal hbound).trans ?_
    rw [Real.toNNReal_coe_nat]
    push_cast
    rfl
  · intro n T; rfl

/-- The regularization of the admissible functional from
`Fspec_regroupingMap_admissible_exists_F` recovers the original spectral point:
`Fspec.toFun T = Func.regularize T` (paper tex:783).

Field-general port of `Fspec_regroupingMap_regularization_eq` (EuclideanClosed.lean). -/
private lemma Fspec_regroupingMap_regularization_eq_F {k : ℕ} (d : Fin k → ℕ+)
    (Fspec : SpectralPoint k F) (Func : AdmissibleFunctional F (KTensor F d))
    (hFunc : ∀ (n : ℕ+) (T : TensorPower F (n : ℕ) (KTensor F d)),
      Func.toFun n T = Real.toNNReal (Fspec.toFun (regroupingMap d n T))) :
    ∀ T : KTensor F d, Fspec.toFun T = Func.regularize T := by
  classical
  by_cases hk : 1 ≤ k
  swap
  · intro T
    have hk0 : k = 0 := by omega
    subst hk0
    have h1 :
        Restricts (unitTensor (F := F) (k := 0) 1)
          (unitTensor (F := F) (k := 0) 2) := by
      refine Restricts.of_eq_cast (fun (i : Fin 0) => i.elim0) ?_
      intro jdx; simp [unitTensor]
    have h2 :
        Restricts (unitTensor (F := F) (k := 0) 2)
          (unitTensor (F := F) (k := 0) 1) := by
      refine Restricts.of_eq_cast (fun (i : Fin 0) => i.elim0) ?_
      intro jdx; simp [unitTensor]
    have h12 := Fspec.mono _ _ h1
    have h21 := Fspec.mono _ _ h2
    have h1eq2 :
        Fspec.toFun (unitTensor (F := F) (k := 0) 1) =
          Fspec.toFun (unitTensor (F := F) (k := 0) 2) := le_antisymm h12 h21
    have hn1 := Fspec.normalize (k := 0) (F := F) (1 : ℕ+)
    have hn2 := Fspec.normalize (k := 0) (F := F) (2 : ℕ+)
    rw [hn1, hn2] at h1eq2
    norm_num at h1eq2
  have Fspec_cast :
      ∀ {d₁ d₂ : Fin k → ℕ+} (hfmt : d₁ = d₂) (T : KTensor F d₁),
        Fspec.toFun (hfmt ▸ T) = Fspec.toFun T := by
    intro d₁ d₂ hfmt T; subst hfmt; rfl
  have zero_Restricts :
      ∀ {dS dT : Fin k → ℕ+} (X : KTensor F dT),
        Restricts (0 : KTensor F dS) X := by
    intro dS dT X
    refine ⟨fun i => (0 : Matrix (Fin (dS i)) (Fin (dT i)) F), ?_⟩
    intro jdx
    change (0 : KTensor F dS) jdx
        = ∑ idx : (∀ i : Fin k, Fin (dT i)),
          (∏ i, (0 : Matrix (Fin (dS i)) (Fin (dT i)) F) (jdx i) (idx i)) * X idx
    have hk_pos : 0 < k := hk
    have h0_mem : (⟨0, hk_pos⟩ : Fin k) ∈ (Finset.univ : Finset (Fin k)) :=
      Finset.mem_univ _
    simp only [Pi.zero_apply]
    apply (Finset.sum_eq_zero _).symm
    intro idx _
    have hprod0 :
        (∏ i, (0 : Matrix (Fin (dS i)) (Fin (dT i)) F) (jdx i) (idx i)) = 0 := by
      apply Finset.prod_eq_zero h0_mem; simp
    rw [hprod0, zero_mul]
  have Fspec_zero :
      ∀ {d' : Fin k → ℕ+}, Fspec.toFun (0 : KTensor F d') = 0 := by
    intro d'
    have hsum_eq_zero :
        (0 : KTensor F d') ⊕ₜ (0 : KTensor F d')
          = (0 : KTensor F (fun i => d' i + d' i)) := by
      funext idx
      unfold directSumTensor
      split_ifs <;> rfl
    have hadd := Fspec.add (dS := d') (dT := d') (0 : KTensor F d') (0 : KTensor F d')
    rw [hsum_eq_zero] at hadd
    have hr1 : Restricts (0 : KTensor F (fun i => d' i + d' i)) (0 : KTensor F d') :=
      zero_Restricts _
    have hr2 : Restricts (0 : KTensor F d') (0 : KTensor F (fun i => d' i + d' i)) :=
      zero_Restricts _
    have heq : Fspec.toFun (0 : KTensor F (fun i => d' i + d' i)) =
        Fspec.toFun (0 : KTensor F d') :=
      le_antisymm (Fspec.mono _ _ hr1) (Fspec.mono _ _ hr2)
    rw [heq] at hadd
    linarith
  have Fspec_nonneg :
      ∀ {d' : Fin k → ℕ+} (X : KTensor F d'), 0 ≤ Fspec.toFun X := by
    intro d' X
    have hz : Fspec.toFun (0 : KTensor F d') ≤ Fspec.toFun X :=
      Fspec.mono _ _ (zero_Restricts X)
    rw [Fspec_zero] at hz; exact hz
  have KTensor_cast_apply :
      ∀ {d₁ d₂ : Fin k → ℕ+} (h : d₁ = d₂)
        (X : KTensor F d₁) (idx : ∀ i, Fin (d₂ i)),
        (h ▸ X) idx = X (h.symm ▸ idx) := by
    intro d₁ d₂ h X idx; subst h; rfl
  have val_eq_rec_pi_fin :
      ∀ {f g : Fin k → ℕ+} (h : f = g)
        (x : ∀ i : Fin k, Fin ↑(f i)) (i : Fin k),
        ((h ▸ x : ∀ i, Fin ↑(g i)) i).val = (x i).val := by
    intro f g h x i; subst h; rfl
  intro T
  have hpow : ∀ n : ℕ+,
      Fspec.toFun (regroupingMap d n
        (tensorPow (F := F) (V := KTensor F d) n T)) = (Fspec.toFun T) ^ (n : ℕ) := by
    intro n
    induction n using PNat.recOn with
    | one =>
      have hfmt : formatPow d 1 = d := by funext i; simp [formatPow]
      have hreg_eq :
          regroupingMap d (1 : ℕ+)
              (tensorPow (F := F) (V := KTensor F d) (1 : ℕ+) T) =
            hfmt.symm ▸ T := by
        funext jdx
        change regroupingMap d (1 : ℕ+)
            (PiTensorProduct.tprod F (fun _ : Fin ((1 : ℕ+) : ℕ) => T)) jdx
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
      have htP :=
        tensorPowerAdd_symm_tensorPow (F := F) (V := KTensor F d) T n
      have hreg_kron :=
        regroupingMap_tensorPowerAdd_symm_eq_kron_cast (F := F) d n 1
          (tensorPow (F := F) (V := KTensor F d) n T)
          (tensorPow (F := F) (V := KTensor F d) 1 T)
      rw [htP] at hreg_kron
      set X := regroupingMap d n (tensorPow (F := F) (V := KTensor F d) n T)
      set Y :=
        regroupingMap d (1 : ℕ+) (tensorPow (F := F) (V := KTensor F d) 1 T)
      have hcast :
          Fspec.toFun ((formatPow_add_eq_mul d n 1) ▸
            regroupingMap d ⟨(n : ℕ) + ((1 : ℕ+) : ℕ),
                Nat.add_pos_left n.pos _⟩
              (tensorPow (F := F) (V := KTensor F d) (n + 1) T)) =
          Fspec.toFun
            (regroupingMap d ⟨(n : ℕ) + ((1 : ℕ+) : ℕ),
                Nat.add_pos_left n.pos _⟩
              (tensorPow (F := F) (V := KTensor F d) (n + 1) T)) :=
        Fspec_cast (formatPow_add_eq_mul d n 1) _
      have hPNat :
          (⟨(n : ℕ) + ((1 : ℕ+) : ℕ),
              Nat.add_pos_left n.pos _⟩ : ℕ+) = (n + 1 : ℕ+) := by
        apply PNat.coe_injective
        change (n : ℕ) + ((1 : ℕ+) : ℕ) = ((n + 1 : ℕ+) : ℕ)
        rw [PNat.add_coe]
      have hkey :
          Fspec.toFun
              (regroupingMap d ⟨(n : ℕ) + ((1 : ℕ+) : ℕ),
                  Nat.add_pos_left n.pos _⟩
                (tensorPow (F := F) (V := KTensor F d) (n + 1) T)) =
            Fspec.toFun (X ⊠ Y) := by
        rw [← hcast, hreg_kron]
      have hkey' :
          Fspec.toFun
              (regroupingMap d (n + 1 : ℕ+)
                (tensorPow (F := F) (V := KTensor F d) (n + 1) T)) =
            Fspec.toFun (X ⊠ Y) := by
        cases hPNat; exact hkey
      rw [hkey']
      rw [Fspec.mult X Y, ih]
      have hfmt1 : formatPow d 1 = d := by funext i; simp [formatPow]
      have hY_eq : Y = hfmt1.symm ▸ T := by
        funext jdx
        change regroupingMap d (1 : ℕ+)
            (PiTensorProduct.tprod F (fun _ : Fin ((1 : ℕ+) : ℕ) => T)) jdx
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
      rw [PNat.add_coe, show ((1 : ℕ+) : ℕ) = 1 from rfl, pow_succ]
  unfold AdmissibleFunctional.regularize
  have hFspecT_nn : 0 ≤ Fspec.toFun T := Fspec_nonneg T
  have hterm : ∀ n : ℕ+,
      ((Func.toFun n
          (tensorPow (F := F) (V := KTensor F d) n T)) : ℝ) ^
        ((1 : ℝ) / ((n : ℕ+) : ℕ)) = Fspec.toFun T := by
    intro n
    rw [hFunc n
      (tensorPow (F := F) (V := KTensor F d) n T)]
    rw [hpow n]
    have hpow_nn : 0 ≤ (Fspec.toFun T) ^ (n : ℕ) := pow_nonneg hFspecT_nn _
    rw [Real.coe_toNNReal _ hpow_nn]
    have hn_ne : ((n : ℕ+) : ℕ) ≠ 0 := n.pos.ne'
    have hdiv : (1 : ℝ) / ((n : ℕ+) : ℕ) = (((n : ℕ+) : ℕ) : ℝ)⁻¹ := one_div _
    rw [hdiv]
    exact Real.pow_rpow_inv_natCast hFspecT_nn hn_ne
  have hcongr :
      (fun n : ℕ+ =>
          ((Func.toFun n (tensorPow (F := F) (V := KTensor F d) n T)) : ℝ) ^
            ((1 : ℝ) / ((n : ℕ+) : ℕ)))
        = fun _ : ℕ+ => Fspec.toFun T := by
    funext n; exact hterm n
  rw [hcongr]
  exact (ciInf_const).symm

/-- Fixed-format spectral-point values are well-founded.

This is the remaining narrow fixed-format input used after the bounded-format
reduction in paper tex lines 1062-1064.  It is the spectral-point analogue of
the fixed-format well-ordering supplied by Corollary 2.5/Corollary 2.6:
after one format `d` is fixed, the values of a spectral point form a
well-founded subset of `ℝ`. -/
private theorem wellFoundedLT_Fspec_values_per_format {k : ℕ}
    (d : Fin k → ℕ+) (Fspec : SpectralPoint k F) :
    WellFoundedLT (Set.range (fun T : KTensor F d => Fspec.toFun T)) := by
  -- Package `T ↦ Fspec(regroupingMap d n T)` as an admissible functional, identify
  -- its regularization with `Fspec.toFun`, and apply Corollary 2.5.
  obtain ⟨Func, hFunc⟩ := Fspec_regroupingMap_admissible_exists_F d Fspec
  have hreg : ∀ T : KTensor F d, Fspec.toFun T = Func.regularize T :=
    Fspec_regroupingMap_regularization_eq_F d Fspec Func hFunc
  have hrange_eq :
      (Set.range (fun T : KTensor F d => Fspec.toFun T)) = Set.range Func.regularize := by
    ext x
    constructor
    · rintro ⟨T, rfl⟩; exact ⟨T, (hreg T).symm⟩
    · rintro ⟨T, rfl⟩; exact ⟨T, hreg T⟩
  rw [hrange_eq]
  exact wellOrdered_values_per_format Func

/-- **Case 1 finite-format well-ordering extraction** (paper tex:1057-1058).

A uniform positive power lower bound in the singleton flattening ranks forces
any non-increasing convergent sequence of spectral values into finitely many
concise formats; Corollary 2.6 (`asympRank_values_wellOrdered`) then gives
stabilization. -/
private theorem wellFounded_values_of_flatRank_power_lower_bound {k : ℕ} [Infinite F]
    (hk : 3 ≤ k) (Fspec : SpectralPoint k F)
    (hbound : ∃ c : ℝ, 0 < c ∧
      ∀ {d : Fin k → ℕ+} (T : KTensor F d) (i : Fin k),
        (flatRank T {i} : ℝ) ^ c ≤ Fspec.toFun T) :
    WellFoundedLT
      (⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor F d => Fspec.toFun T)) := by
  classical
  have _hk1 : 1 ≤ k := by omega
  obtain ⟨c, hcpos, hpower⟩ := hbound
  set S : Set ℝ :=
    ⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor F d => Fspec.toFun T)
    with hS_def
  refine ⟨?_⟩
  rw [RelEmbedding.wellFounded_iff_isEmpty]
  refine ⟨fun e => ?_⟩
  set r : ℕ → ℝ := fun n => (e n : ℝ) with hr_def
  have hr_anti : StrictAnti r := fun n m hnm => e.map_rel_iff.mpr hnm
  have hr_mem : ∀ n, r n ∈ S := fun n => (e n).2
  have hr_raw :
      ∀ n, ∃ (d : Fin k → ℕ+) (T : KTensor F d), Fspec.toFun T = r n := by
    intro n
    have hn := hr_mem n
    simp only [hS_def, Set.mem_iUnion, Set.mem_range] at hn
    obtain ⟨d, T, hT⟩ := hn
    exact ⟨d, T, hT⟩
  choose dRaw TRaw hTRaw using hr_raw
  have hr_bdd : ∀ n, r n ≤ r 0 := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · simp [h0]
    · exact (hr_anti hpos).le
  set R : ℝ := max 0 (r 0) with hR_def
  set B : ℝ := max 1 (R ^ ((1 : ℝ) / c)) with hB_def
  set N : ℕ := Nat.ceil B with hN_def
  have hB_ge_one : (1 : ℝ) ≤ B := by simp [hB_def]
  have hN_pos : 0 < N := by
    have hceil_ge_one : (1 : ℕ) ≤ Nat.ceil B := by
      exact_mod_cast hB_ge_one.trans (Nat.le_ceil B)
    omega
  set Npos : ℕ+ := ⟨N, hN_pos⟩ with hNpos_def
  set dStar : Fin k → ℕ+ := fun _ => Npos with hdStar_def
  have hbdd : ∀ n, ∃ (d' : Fin k → ℕ+) (T' : KTensor F d'),
      Fspec.toFun T' = r n ∧ ∀ j, (d' j : ℕ) ≤ N := by
    intro n
    by_cases hTzero : TRaw n = 0
    · refine ⟨fun _ => (1 : ℕ+), (0 : KTensor F (fun _ => (1 : ℕ+))), ?_, ?_⟩
      · rw [SpectralPoint.map_zero Fspec, ← hTRaw n, hTzero, SpectralPoint.map_zero Fspec]
      · intro j
        simpa using hN_pos
    · obtain ⟨d', T', hT'_T, hT_T', hflat⟩ := exists_concise_restriction (TRaw n) hTzero
      have hval_eq : Fspec.toFun T' = Fspec.toFun (TRaw n) := by
        have hle₁ := Fspec.mono T' (TRaw n) hT'_T
        have hle₂ := Fspec.mono (TRaw n) T' hT_T'
        exact le_antisymm hle₁ hle₂
      refine ⟨d', T', hval_eq.trans (hTRaw n), ?_⟩
      intro j
      have hdim_eq : ((d' j : ℕ) : ℝ) = (flatRank T' {j} : ℝ) := by
        exact_mod_cast hflat j
      have hpow_le_R : ((d' j : ℕ) : ℝ) ^ c ≤ R := by
        calc
          ((d' j : ℕ) : ℝ) ^ c = (flatRank T' {j} : ℝ) ^ c := by rw [hdim_eq]
          _ ≤ Fspec.toFun T' := hpower T' j
          _ = r n := hval_eq.trans (hTRaw n)
          _ ≤ r 0 := hr_bdd n
          _ ≤ R := by simp [R]
      have hroot :
          ((d' j : ℕ) : ℝ) ≤ R ^ ((1 : ℝ) / c) :=
        le_rpow_one_div_of_rpow_le (by positivity) hcpos hpow_le_R
      have hleB : ((d' j : ℕ) : ℝ) ≤ B :=
        hroot.trans (le_max_right _ _)
      exact_mod_cast hleB.trans (Nat.le_ceil B)
  have hreembed : ∀ n, ∃ T'' : KTensor F dStar, Fspec.toFun T'' = r n := by
    intro n
    obtain ⟨d', T', hval, hle'⟩ := hbdd n
    have hle : ∀ j, (d' j : ℕ) ≤ (dStar j : ℕ) := by
      intro j
      simpa [dStar, hdStar_def, Npos, hNpos_def] using hle' j
    let T'' : KTensor F dStar := reembed hle T'
    have hval_reembed : Fspec.toFun T'' = Fspec.toFun T' := by
      have hle₁ := Fspec.mono T'' T' (restricts_reembed hle T')
      have hle₂ := Fspec.mono T' T'' (reembed_restricts_to hle T')
      exact le_antisymm hle₁ hle₂
    exact ⟨T'', hval_reembed.trans hval⟩
  choose TStar hTStar using hreembed
  have hmem' : ∀ n, r n ∈ Set.range (fun T : KTensor F dStar => Fspec.toFun T) := by
    intro n
    exact ⟨TStar n, hTStar n⟩
  have hWO : WellFoundedLT (Set.range (fun T : KTensor F dStar => Fspec.toFun T)) :=
    wellFoundedLT_Fspec_values_per_format dStar Fspec
  have hWF : WellFounded
      (α := Set.range (fun T : KTensor F dStar => Fspec.toFun T)) (· < ·) :=
    hWO.wf
  rw [RelEmbedding.wellFounded_iff_isEmpty] at hWF
  have hinj : Function.Injective
      (fun n : ℕ => (⟨r n, hmem' n⟩ :
        Set.range (fun T : KTensor F dStar => Fspec.toFun T))) := by
    intro a b hab
    have hr_eq : r a = r b := Subtype.mk.inj hab
    exact hr_anti.injective hr_eq
  refine hWF.false ⟨⟨fun n => ⟨r n, hmem' n⟩, hinj⟩, ?_⟩
  intro a b
  change r a < r b ↔ a > b
  constructor
  · intro hlt
    by_contra hge
    push_neg at hge
    rcases lt_or_eq_of_le hge with halt | hab
    · exact absurd (hr_anti halt) (not_lt.mpr hlt.le)
    · rw [hab] at hlt
      exact absurd hlt (lt_irrefl _)
  · intro hgt
    exact hr_anti hgt

/-- Case 1 in the induction proof of Theorem 3.1 (paper tex:1056-1058).

Assuming every pair-unit `⟨2⟩_{i,j}` has spectral value strictly larger than
`1`, Corollary 3.3 (`exists_large_subrankPair`) and monotonicity give a
positive power lower bound in terms of the maximum singleton flattening rank.
Together with Corollary 2.6 (`asympRank_values_wellOrdered`) this forces
every non-increasing convergent sequence of spectral values to stabilize. -/
theorem asympSpectrum_values_wellOrdered_infinite_case1 {k : ℕ} [Infinite F]
    (hk : 3 ≤ k) (Fspec : SpectralPoint k F)
    (hpair : ∀ (i j : Fin k) (hij : i ≠ j),
      1 < Fspec.toFun (unitPairTensor (F := F) 2 i j hij)) :
    WellFoundedLT
      (⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor F d => Fspec.toFun T)) := by
  exact wellFounded_values_of_flatRank_power_lower_bound hk Fspec
    (pair_gt_two_implies_flatRank_power_lower_bound hk Fspec hpair)

private lemma wellFoundedLT_of_subset {S U : Set ℝ} (hSU : S ⊆ U)
    (hWF : WellFoundedLT U) :
    WellFoundedLT S := by
  let incl : S → U := fun x => ⟨x.1, hSU x.2⟩
  refine ⟨(InvImage.wf incl hWF.wf).mono ?_⟩
  intro x y hxy
  exact hxy

private lemma wellFoundedLT_natCast_range :
    WellFoundedLT (Set.range fun n : ℕ => (n : ℝ)) := by
  classical
  let natOf : (Set.range fun n : ℕ => (n : ℝ)) → ℕ :=
    fun x => Classical.choose x.2
  refine ⟨(InvImage.wf natOf (inferInstance : WellFoundedLT ℕ).wf).mono ?_⟩
  intro x y hxy
  dsimp [InvImage, natOf]
  have hx : ((Classical.choose x.2 : ℕ) : ℝ) = x.1 :=
    Classical.choose_spec x.2
  have hy : ((Classical.choose y.2 : ℕ) : ℝ) = y.1 :=
    Classical.choose_spec y.2
  have hxy_natCast :
      ((Classical.choose x.2 : ℕ) : ℝ) <
        ((Classical.choose y.2 : ℕ) : ℝ) := by
    simpa [hx, hy] using hxy
  exact_mod_cast hxy_natCast

-- `dif_pos`/`dif_neg` simp args below force dependent `if`-branch reduction and
-- are load-bearing despite the unusedSimpArgs linter flagging them.
set_option linter.unusedSimpArgs false in
/-- Two-way restriction normal form for order-two tensors (paper tex:1051).

For a `2`-tensor `T` with `r = flatRank T {0} > 0`, the rank factorisation of
`M = flattenMatrix T {0}` (with `M.rank = r`) produces leg-wise matrices giving
both `unitTensor F ⟨r⟩ ≤ₜ T` and `T ≤ₜ unitTensor F ⟨r⟩`.  This is the matrix
normal-form heart of "every spectral point on matrices is matrix rank". -/
lemma tensor_restricts_equiv_unitTensor_k2 {d : Fin 2 → ℕ+}
    (T : KTensor F d) {r : ℕ} (hr : 0 < r) (hrank : flatRank T {0} = r) :
    Restricts (unitTensor F (k := 2) ⟨r, hr⟩) T ∧
      Restricts T (unitTensor F (k := 2) ⟨r, hr⟩) := by
  classical
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  -- Flattening at I = {0}: rows = leg 0, cols = leg 1.
  set M : Matrix _ _ F := flattenMatrix T {(0 : Fin 2)} with hM_def
  have hMrank : M.rank = r := by rw [hM_def]; exact hrank
  set φ : _ →ₗ[F] _ := M.mulVecLin with hφ_def
  have hrange_dim : Module.finrank F (LinearMap.range φ) = r := by
    rw [← hMrank]; rfl
  obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
      (R := F) (M := Fin r → F) (M' := LinearMap.range φ)
      (by rw [Module.finrank_fin_fun]; exact hrange_dim.symm)
  set U : (Fin r → F) →ₗ[F] _ :=
    (LinearMap.range φ).subtype ∘ₗ e.toLinearMap with hU_def
  have hU_inj : Function.Injective U := fun x y hxy =>
    e.injective (Subtype.ext hxy)
  set φ' : _ →ₗ[F] LinearMap.range φ :=
    φ.codRestrict (LinearMap.range φ) (fun v => LinearMap.mem_range_self φ v) with hφ'_def
  set V : _ →ₗ[F] (Fin r → F) := e.symm.toLinearMap ∘ₗ φ' with hV_def
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
  have hAMB : A * M * B = (1 : Matrix (Fin r) (Fin r) F) := by
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
  have hprod2 : ∀ (g : Fin 2 → F), (∏ ℓ, g ℓ) = g 0 * g 1 := by
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
  -- leg-`ℓ` index of `unitTensor F ⟨r⟩` reindexed to `Fin r`.
  set toFinr : ∀ ℓ : Fin 2, Fin ((fun _ : Fin 2 => (⟨r, hr⟩ : ℕ+)) ℓ) → Fin r :=
    fun ℓ p => Fin.cast (hudim ℓ) p with htoFinr_def
  refine ⟨?_, ?_⟩
  · -- Direction 1: `unitTensor F ⟨r⟩ ≤ₜ T` via leg matrices `A`, `Bᵀ`.
    set C1leg : ∀ ℓ : Fin 2,
        Matrix (Fin ((fun _ : Fin 2 => (⟨r, hr⟩ : ℕ+)) ℓ)) (Fin (d ℓ)) F :=
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
    change (unitTensor F (k := 2) ⟨r, hr⟩) jdx = _
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
  · -- Direction 2: `T ≤ₜ unitTensor F ⟨r⟩` via leg matrices `Pu`, `Qvᵀ`.
    set D2leg : ∀ ℓ : Fin 2,
        Matrix (Fin (d ℓ)) (Fin ((fun _ : Fin 2 => (⟨r, hr⟩ : ℕ+)) ℓ)) F :=
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
    rw [show (∑ idx, (∏ i, D2leg i (jdx i) (idx i)) * (unitTensor F (k := 2) ⟨r, hr⟩) idx)
          = ∑ pp : Fin r × Fin r,
              (∏ i, D2leg i (jdx i)
                ((piFinTwoEquiv (fun ℓ : Fin 2 => Fin ((fun _ : Fin 2 => (⟨r, hr⟩ : ℕ+)) ℓ))).symm
                  pp i)) *
                (unitTensor F (k := 2) ⟨r, hr⟩)
                  ((piFinTwoEquiv (fun ℓ : Fin 2 => Fin ((fun _ : Fin 2 => (⟨r, hr⟩ : ℕ+)) ℓ))).symm
                    pp)
        from (Equiv.sum_comp
          (piFinTwoEquiv (fun ℓ : Fin 2 => Fin ((fun _ : Fin 2 => (⟨r, hr⟩ : ℕ+)) ℓ))).symm
          (fun idx => (∏ i, D2leg i (jdx i) (idx i)) *
            (unitTensor F (k := 2) ⟨r, hr⟩) idx)).symm]
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
      have hunit1 : (unitTensor F (k := 2) ⟨r, hr⟩)
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
      have hunit0 : (unitTensor F (k := 2) ⟨r, hr⟩)
          ((piFinTwoEquiv (fun ℓ : Fin 2 => Fin ((fun _ : Fin 2 => (⟨r, hr⟩ : ℕ+)) ℓ))).symm
            (p0, p1)) = 0 := by
        rw [unitTensor, if_neg]
        intro hall
        exact hp1 (hall 1 0)
      rw [hunit0, mul_zero]
    · intro hp0; exact absurd (Finset.mem_univ _) hp0

/-- Pointwise integrality of order-two spectral values (paper tex:1051).

This is the exact formal content needed from Strassen's classification of the
order-two asymptotic spectrum: every spectral point on matrices is ordinary
matrix rank, hence every individual value is a natural number viewed in `ℝ`. -/
private lemma order_two_spectral_value_mem_natCast_range [Infinite F]
    (Fspec : SpectralPoint 2 F) {d : Fin 2 → ℕ+} (T : KTensor F d) :
    Fspec.toFun T ∈ Set.range (fun n : ℕ => (n : ℝ)) := by
  /- Paper tex:1051: at `k = 2` every spectral point is ordinary matrix rank,
     so `Fspec.toFun T = (r : ℝ)` where `r = flatRank T {0} = rank(T)`. We get
     the two-way restriction `T ∼ₜ unitTensor ⟨r⟩` from
     `tensor_restricts_equiv_unitTensor_k2` (`r > 0`) and `Fspec.normalize`. The
     `r = 0` case is the zero tensor, with value `0` by `⊕`-additivity. -/
  classical
  set r : ℕ := flatRank T {(0 : Fin 2)} with hr_def
  refine ⟨r, ?_⟩
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · -- Zero tensor: `flatRank T {0} = 0 ⟹ T = 0 ⟹ Fspec.toFun T = 0`.
    have hMrank0 : (flattenMatrix T {(0 : Fin 2)}).rank = 0 := hr0
    have hM0 : flattenMatrix T {(0 : Fin 2)} = 0 := by
      have hrange : LinearMap.range (flattenMatrix T {(0 : Fin 2)}).mulVecLin = ⊥ := by
        have hfin : Module.finrank F
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
    have hdsum : Restricts ((0 : KTensor F d) ⊕ₜ (0 : KTensor F d)) (0 : KTensor F d) ∧
        Restricts (0 : KTensor F d) ((0 : KTensor F d) ⊕ₜ (0 : KTensor F d)) := by
      constructor
      · refine ⟨fun _ => 0, ?_⟩
        intro jdx; simp [directSumTensor]
      · refine ⟨fun _ => 0, ?_⟩
        intro jdx; simp [directSumTensor]
    have hle1 := Fspec.mono _ _ hdsum.1
    have hle2 := Fspec.mono _ _ hdsum.2
    have hadd := Fspec.add (0 : KTensor F d) (0 : KTensor F d)
    have heqsum : Fspec.toFun ((0 : KTensor F d) ⊕ₜ (0 : KTensor F d))
        = Fspec.toFun (0 : KTensor F d) := le_antisymm hle1 hle2
    rw [hadd] at heqsum
    have hzero : Fspec.toFun (0 : KTensor F d) = 0 := by linarith
    rw [hT0, hzero, hr0]; norm_num
  · -- Positive rank: `T ∼ₜ unitTensor ⟨r⟩`, value `r`.
    obtain ⟨hunit_le, hle_unit⟩ :=
      tensor_restricts_equiv_unitTensor_k2 (F := F) T hrpos hr_def.symm
    have hmono1 := Fspec.mono _ _ hunit_le
    have hmono2 := Fspec.mono _ _ hle_unit
    rw [Fspec.normalize ⟨r, hrpos⟩] at hmono1 hmono2
    have hval : Fspec.toFun T = ((⟨r, hrpos⟩ : ℕ+) : ℕ) := le_antisymm hmono2 hmono1
    change (r : ℝ) = Fspec.toFun T
    rw [hval]

/-- Matrix-rank uniqueness for order-two spectral values (paper tex:1051).

At `k = 2`, the asymptotic spectrum has a unique point: ordinary matrix rank.
Consequently every spectral-point value of a 2-tensor is a nonnegative integer
viewed in `ℝ`.  This is the subset half needed for well-foundedness. -/
private lemma order_two_spectral_values_subset_natCast_range [Infinite F]
    (Fspec : SpectralPoint 2 F) :
    (⋃ d : Fin 2 → ℕ+, Set.range (fun T : KTensor F d => Fspec.toFun T)) ⊆
      Set.range (fun n : ℕ => (n : ℝ)) := by
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_range] at hx
  obtain ⟨d, T, rfl⟩ := hx
  exact order_two_spectral_value_mem_natCast_range (F := F) Fspec T

/-- The formal Case 2 lift once the free pair has been moved to the final two
legs.  This is the actual `spec_descend` step of paper tex:1058-1061. -/
private theorem asympSpectrum_values_wellOrdered_infinite_descend_last_pair
    {k : ℕ} [Infinite F] (hk : 3 ≤ k) (Fspec : SpectralPoint k F)
    (hij : (⟨k - 2, by omega⟩ : Fin k) ≠ ⟨k - 1, by omega⟩)
    (h2 : Fspec.toFun
        (unitPairTensor (F := F) 2 ⟨k - 2, by omega⟩ ⟨k - 1, by omega⟩ hij) = 1)
    (hIH : ∀ Fspec' : SpectralPoint (k - 1) F,
      WellFoundedLT
        (⋃ e : Fin (k - 1) → ℕ+,
          Set.range (fun U : KTensor F e => Fspec'.toFun U))) :
    WellFoundedLT
      (⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor F d => Fspec.toFun T)) := by
  classical
  obtain ⟨Fspec', _hphi, hgamma⟩ := spec_descend (F := F) hk Fspec hij h2
  refine wellFoundedLT_of_subset ?_ (hIH Fspec')
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_range] at hx ⊢
  obtain ⟨d, T, hT⟩ := hx
  refine ⟨dGamma hk d, gammaMap (F := F) hk T, ?_⟩
  rw [← hT]
  exact (hgamma T).symm

/-- Matrix-rank base case for the infinite-field induction in Theorem 3.1
(paper tex:1051).  For `k = 2`, spectral-point values coincide with matrix
rank values, hence inherit `asympRank_values_wellOrdered`. -/
private theorem asympSpectrum_values_wellOrdered_infinite_base_two [Infinite F]
    (Fspec : SpectralPoint 2 F) :
    WellFoundedLT
      (⋃ d : Fin 2 → ℕ+, Set.range (fun T : KTensor F d => Fspec.toFun T)) := by
  exact wellFoundedLT_of_subset
    (order_two_spectral_values_subset_natCast_range (F := F) Fspec)
    wellFoundedLT_natCast_range

/-- WLOG leg-permutation reduction for Case 2 in the induction step (paper
tex:1058-1061): if some pair-unit has value `1`, permute tensor legs so that
the pair is the final two legs and then apply `spec_descend`.

The leg permutation is realized via `SpectralPoint.reindex`: we build
`σ : Equiv.Perm (Fin k)` carrying the witness pair `(i, j)` to the last two
legs `(k-2, k-1)`, set `Fspec' := Fspec.reindex σ`, and observe that
`Fspec'` has the same value set as `Fspec` (`reindex_iUnion_range`) while the
last-pair value of `Fspec'` equals the `(i,j)`-pair value of `Fspec`
(`reindex_toFun_unitPairTensor`). The descent then runs on `Fspec'`. -/
private theorem asympSpectrum_values_wellOrdered_infinite_case2_wlog
    {k : ℕ} [Infinite F] (hk : 3 ≤ k) (Fspec : SpectralPoint k F)
    (hfree : ∃ (i j : Fin k) (hij : i ≠ j),
      Fspec.toFun (unitPairTensor (F := F) 2 i j hij) = 1)
    (hIH : ∀ Fspec' : SpectralPoint (k - 1) F,
      WellFoundedLT
        (⋃ e : Fin (k - 1) → ℕ+,
          Set.range (fun U : KTensor F e => Fspec'.toFun U))) :
    WellFoundedLT
      (⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor F d => Fspec.toFun T)) := by
  classical
  obtain ⟨i, j, hij, hval⟩ := hfree
  let last₀ : Fin k := ⟨k - 2, by omega⟩
  let last₁ : Fin k := ⟨k - 1, by omega⟩
  have hlast_ne : last₀ ≠ last₁ := by
    intro h
    exact (by omega : ¬ (k - 2 = k - 1)) (Fin.ext_iff.mp h)
  -- A permutation carrying the witness pair `(i, j)` to the last two legs.
  obtain ⟨σ, hσi, hσj⟩ := exists_perm_mapping_pair i j hij last₀ last₁ hlast_ne
  have hsymm₀ : σ.symm last₀ = i := by rw [← hσi, Equiv.symm_apply_apply]
  have hsymm₁ : σ.symm last₁ = j := by rw [← hσj, Equiv.symm_apply_apply]
  -- Move the witness pair to `(σ⁻¹ last₀, σ⁻¹ last₁)` by substitution.
  subst hsymm₀
  subst hsymm₁
  -- Pulled-back spectral point: same value set, free pair now at the last legs.
  set Fspec' : SpectralPoint k F := Fspec.reindex σ with hFspec'
  -- The last-pair value of `Fspec'` equals the witness value of `Fspec`.
  have hlast : Fspec'.toFun (unitPairTensor (F := F) 2 last₀ last₁ hlast_ne) = 1 := by
    rw [hFspec', SpectralPoint.reindex_toFun_unitPairTensor (F := F)
      Fspec σ 2 last₀ last₁ hlast_ne hij]
    exact hval
  -- Run the descent on `Fspec'`, then transfer the well-ordering back.
  have hwell' := asympSpectrum_values_wellOrdered_infinite_descend_last_pair
    (F := F) hk Fspec' hlast_ne hlast hIH
  rw [hFspec', SpectralPoint.reindex_iUnion_range] at hwell'
  exact hwell'

/-- Infinite-field version of Theorem 3.1 (paper tex:1050-1061).

This is the induction on `k`: the base `k = 2` is matrix rank; for `k > 2`,
Case 1 is `asympSpectrum_values_wellOrdered_infinite_case1`; Case 2 applies
Lemma 3.8 (`spec_descend`, tex:1038-1045) when some pair-unit has value `1`
and then uses the induction hypothesis for `k - 1`. -/
theorem asympSpectrum_values_wellOrdered_of_infinite {k : ℕ} [Infinite F]
    (hk : 2 ≤ k) (Fspec : SpectralPoint k F) :
    WellFoundedLT
      (⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor F d => Fspec.toFun T)) := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rcases lt_or_eq_of_le hk with hk_gt | hk_eq
      · have hk3 : 3 ≤ k := by omega
        by_cases hpair : ∀ (i j : Fin k) (hij : i ≠ j),
            1 < Fspec.toFun (unitPairTensor (F := F) 2 i j hij)
        · exact asympSpectrum_values_wellOrdered_infinite_case1 (F := F) hk3 Fspec hpair
        · push_neg at hpair
          obtain ⟨i, j, hij, hij_le⟩ := hpair
          have hone_le :
              (1 : ℝ) ≤ Fspec.toFun (unitPairTensor (F := F) 2 i j hij) := by
            have hmono := Fspec.mono
              (unitPairTensor (F := F) (k := k) 1 i j hij)
              (unitPairTensor (F := F) (k := k) 2 i j hij)
              (unitPairTensor_restricts_of_le (F := F) i j hij (by norm_num))
            simpa [Fspec.unitPair_one i j hij] using hmono
          have hfree :
              ∃ (i j : Fin k) (hij : i ≠ j),
                Fspec.toFun (unitPairTensor (F := F) 2 i j hij) = 1 :=
            ⟨i, j, hij, le_antisymm hij_le hone_le⟩
          refine asympSpectrum_values_wellOrdered_infinite_case2_wlog
            (F := F) hk3 Fspec hfree ?_
          intro Fspec'
          exact ih (k - 1) (by omega) (by omega) Fspec'
      · subst hk_eq
        exact asympSpectrum_values_wellOrdered_infinite_base_two (F := F) Fspec

/-- **Strassen 1988 Theorem 3.10** (strassen1988.tex:1264), extension-existence form.
Every spectral point over `F` extends to one over any field extension `K`, agreeing
with the original on base-changed tensors. The proof is the converse direction of
Thm 3.10, resting on Strassen 1987 Proposition 5.3(i) (strassen1987.tex:873). -/
theorem exists_spectralPoint_extension {k : ℕ} (hk : 2 ≤ k) (Fspec : SpectralPoint k F)
    (K : Type u) [Field K] [Algebra F K] [Algebra.IsAlgebraic F K] :
    ∃ Gspec : SpectralPoint k K,
      ∀ {d : Fin k → ℕ+} (T : KTensor F d),
        Gspec.toFun (T.baseChange (K := K)) = Fspec.toFun T :=
  exists_spectralPoint_extension_bridge hk Fspec K

/-- Reduction from arbitrary fields to infinite fields for Theorem 3.1.

This packages the paper's WLOG step at tex:1049, citing Strassen 1988,
Theorem 3.10: for asymptotic spectra, the well-ordering statement over an
arbitrary field follows from the corresponding infinite-field statement.
The base field is reduced to `AlgebraicClosure F`, which is infinite, and
well-foundedness transfers down the base-change inclusion. -/
theorem asympSpectrum_values_wellOrdered_strassen1988_reduction {k : ℕ}
    (hk : 2 ≤ k) (Fspec : SpectralPoint k F)
    (hinfinite :
      ∀ {K : Type u} [Field K] [Infinite K] (Gspec : SpectralPoint k K),
        WellFoundedLT
          (⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor K d => Gspec.toFun T))) :
    WellFoundedLT
      (⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor F d => Fspec.toFun T)) := by
  classical
  -- Step 1: pass to the algebraic closure, which is an infinite field extension.
  set K := AlgebraicClosure F with hK
  haveI : Infinite K := IsAlgClosed.instInfinite
  -- Step 2: extend the spectral point along the base change.
  obtain ⟨Gspec, hext⟩ := exists_spectralPoint_extension (F := F) hk Fspec K
  -- Step 3: the infinite-field hypothesis applies to the closure.
  have hWF := hinfinite (K := K) Gspec
  -- Step 4: the F-side value set is contained in the K-side value set.
  have hsub :
      (⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor F d => Fspec.toFun T)) ⊆
        (⋃ d : Fin k → ℕ+, Set.range (fun S : KTensor K d => Gspec.toFun S)) := by
    intro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨d, T, hT⟩ := hx
    rw [Set.mem_iUnion]
    refine ⟨d, T.baseChange (K := K), ?_⟩
    simp only at hT ⊢
    rw [hext T, hT]
  -- Step 5: well-foundedness transfers down the inclusion via `InvImage`,
  -- pulling the well-founded `<` on the K-side superset back along the
  -- subset inclusion `Set.inclusion hsub`.
  exact ⟨InvImage.wf (Set.inclusion hsub) hWF.wf⟩

/-- **Theorem 3.1** (tex:812-814,
    `\label{th:spec-well-ord}` / `\label{thm:spectral points well ordered}`).

For any field `F`, any order `k ≥ 2`, and any `F ∈ Δ(F, k)`,
the set `{F(T) : T ∈ F^{d_1} ⊗ ⋯ ⊗ F^{d_k}, d ∈ ℤ_{≥1}^k}` is well-ordered. -/
theorem asympSpectrum_values_wellOrdered {k : ℕ} (hk : 2 ≤ k)
    (Fspec : SpectralPoint k F) :
    WellFoundedLT
      (⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor F d => Fspec.toFun T)) := by
  refine asympSpectrum_values_wellOrdered_strassen1988_reduction (F := F) hk Fspec ?_
  intro K _instField _instInfinite Gspec
  exact asympSpectrum_values_wellOrdered_of_infinite (F := K) hk Gspec

end Semicontinuity
