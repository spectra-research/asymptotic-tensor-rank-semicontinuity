/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.AsymptoticSpectrumDuality.Defs

/-!
# Rank and Subrank for Strassen Preorders

This file defines rank and subrank functions for elements of a semiring
with a Strassen preorder, as well as their asymptotic versions.

## Main Definitions

* `rank` - The smallest natural number n such that a ≤_P n
* `subrank` - The largest natural number n such that n ≤_P a
* `asympRank` - The limit of rank(a^n)^{1/n}
* `asympSubrank` - The limit of subrank(a^n)^{1/n}
* `IsGapped` - Property ensuring asympSubrank = min over spectrum

## References

* Strassen (1988), The asymptotic spectrum of tensors
* survey.tex, Section on rank and subrank characterizations
-/

namespace AsymptoticSpectrumDuality

open scoped NNReal ENNReal

variable {S : Type*} [CommSemiring S]

attribute [local instance] Classical.propDecidable

/-! ### Rank and Subrank -/

/-- There exists n such that a ≤_P n (by archimedean for 1 ≠ 0, or reflexivity for a = 0). -/
theorem StrassenPreorder.exists_rel_nat (p : StrassenPreorder S) (a : S) : ∃ n : ℕ, p.rel a n := by
  by_cases h1 : (1 : S) = 0
  · -- If 1 = 0, then a = a * 1 = a * 0 = 0, so a ≤_P 0 by reflexivity
    have ha : a = 0 := by rw [← mul_one a, h1, mul_zero]
    refine ⟨0, ?_⟩
    simp only [Nat.cast_zero, ha]
    exact p.refl 0
  · -- By archimedean with b = 1
    obtain ⟨r, hr⟩ := p.archimedean a 1 h1
    simp only [mul_one] at hr
    exact ⟨r, hr⟩

/-- Rank of a with respect to P: smallest n such that a ≤_P n.
    Always finite by the archimedean property (and for a = 0, reflexivity gives 0 ≤_P 0). -/
noncomputable def StrassenPreorder.rank (p : StrassenPreorder S) (a : S) : ℕ :=
  Nat.find (p.exists_rel_nat a)

/-- Subrank of a: largest n such that n ≤_P a.
    Always finite since subrank(a) ≤ rank(a) (by transitivity with a ≤_P rank(a)). -/
noncomputable def StrassenPreorder.subrank (p : StrassenPreorder S) (a : S) : ℕ :=
  sSup { n : ℕ | p.rel n a }

namespace StrassenPreorder

variable (p : StrassenPreorder S)

/-! ### Helper lemmas -/

/-- n ≤ m in ℕ implies (n : S) ≤_P (m : S) -/
theorem natCast_mono {n m : ℕ} (h : n ≤ m) : p.rel (n : S) (m : S) :=
  p.nat_compat n m |>.mp h

/-- Multiplication is monotone on the left: a ≤_P b → a * c ≤_P b * c -/
theorem mul_mono_left {a b : S} (c : S) (hab : p.rel a b) : p.rel (a * c) (b * c) :=
  p.mul_mono a b c hab

/-- Multiplication is monotone on the right: a ≤_P b → c * a ≤_P c * b -/
theorem mul_mono_right {a b : S} (c : S) (hab : p.rel a b) : p.rel (c * a) (c * b) := by
  rw [mul_comm c a, mul_comm c b]
  exact p.mul_mono a b c hab

/-! ### Basic Properties of Rank -/

/-- a ≤_P rank(a) -/
theorem rel_rank (a : S) : p.rel a (p.rank a) :=
  Nat.find_spec (p.exists_rel_nat a)

/-- rank(a) is the smallest n with a ≤_P n -/
theorem rank_le_iff (a : S) (n : ℕ) : p.rank a ≤ n ↔ p.rel a n := by
  constructor
  · intro h
    exact p.trans _ _ _ (p.rel_rank a) (p.natCast_mono h)
  · intro h
    exact Nat.find_le h

/-- Rank of n is at most n -/
theorem rank_natCast_le (n : ℕ) : p.rank (n : S) ≤ n :=
  (p.rank_le_iff n n).mpr (p.refl n)

/-- Rank is monotone -/
theorem rank_mono {a b : S} (hab : p.rel a b) : p.rank a ≤ p.rank b := by
  rw [rank_le_iff]
  exact p.trans _ _ _ hab (p.rel_rank b)

/-- Rank is sub-multiplicative: rank(a * b) ≤ rank(a) * rank(b) -/
theorem rank_mul_le (a b : S) : p.rank (a * b) ≤ p.rank a * p.rank b := by
  rw [rank_le_iff]
  have ha := p.rel_rank a
  have hb := p.rel_rank b
  -- a * b ≤ (rank a) * b by mul_mono_left (multiplying ha on the right by b)
  have h1 : p.rel (a * b) ((p.rank a : S) * b) := p.mul_mono_left b ha
  -- (rank a) * b ≤ (rank a) * (rank b) by mul_mono_right (multiplying hb on the left by rank a)
  have h2 : p.rel ((p.rank a : S) * b) ((p.rank a : S) * (p.rank b : S)) :=
    p.mul_mono_right (p.rank a : S) hb
  have h3 : (p.rank a : S) * (p.rank b : S) = ((p.rank a * p.rank b : ℕ) : S) := by
    push_cast; ring
  rw [h3] at h2
  exact p.trans _ _ _ (p.trans _ _ _ h1 h2) (p.refl _)

/-! ### Basic Properties of Subrank -/

/-- The set { n | n ≤_P a } is bounded above by rank(a) -/
theorem subrank_set_bddAbove (a : S) : BddAbove { n : ℕ | p.rel n a } := by
  use p.rank a
  intro n hn
  -- n ≤_P a and a ≤_P rank(a), so n ≤_P rank(a)
  have h : p.rel (n : S) (p.rank a : S) := p.trans _ _ _ hn (p.rel_rank a)
  -- From n ≤_P rank(a), we get n ≤ rank(a) by nat_compat
  exact (p.nat_compat n (p.rank a)).mpr h

/-- subrank(a) ≤_P a -/
theorem rel_subrank (a : S) : p.rel (p.subrank a) a := by
  unfold subrank
  by_cases h : { n : ℕ | p.rel n a }.Nonempty
  · have hbdd := p.subrank_set_bddAbove a
    have hmem := Nat.sSup_mem h hbdd
    exact hmem
  · simp only [Set.not_nonempty_iff_eq_empty] at h
    simp only [h, csSup_empty, Nat.cast_zero, bot_eq_zero']
    exact p.zero_le a

/-- n ≤ subrank(a) iff n ≤_P a -/
theorem le_subrank_iff (a : S) (n : ℕ) : n ≤ p.subrank a ↔ p.rel n a := by
  constructor
  · intro h
    exact p.trans _ _ _ (p.natCast_mono h) (p.rel_subrank a)
  · intro h
    exact le_csSup (p.subrank_set_bddAbove a) h

/-- Subrank of n is at least n -/
theorem le_subrank_natCast (n : ℕ) : n ≤ p.subrank (n : S) :=
  (p.le_subrank_iff n n).mpr (p.refl n)

/-- Subrank is monotone -/
theorem subrank_mono {a b : S} (hab : p.rel a b) : p.subrank a ≤ p.subrank b := by
  rw [le_subrank_iff]
  exact p.trans _ _ _ (p.rel_subrank a) hab

/-- subrank(a) ≤ rank(a) -/
theorem subrank_le_rank (a : S) : p.subrank a ≤ p.rank a := by
  -- subrank(a) ≤_P a ≤_P rank(a), so subrank(a) ≤_P rank(a), hence subrank(a) ≤ rank(a)
  have h : p.rel (p.subrank a : S) (p.rank a : S) :=
    p.trans _ _ _ (p.rel_subrank a) (p.rel_rank a)
  exact (p.nat_compat _ _).mpr h

/-- Rank of n equals n -/
theorem rank_natCast (n : ℕ) : p.rank (n : S) = n := by
  apply le_antisymm (p.rank_natCast_le n)
  calc n ≤ p.subrank (n : S) := p.le_subrank_natCast n
    _ ≤ p.rank (n : S) := p.subrank_le_rank _

/-- Subrank of n equals n -/
theorem subrank_natCast' (n : ℕ) : p.subrank (n : S) = n := by
  apply le_antisymm _ (p.le_subrank_natCast n)
  calc p.subrank (n : S) ≤ p.rank (n : S) := p.subrank_le_rank _
    _ = n := p.rank_natCast n

/-- Subrank is super-multiplicative: subrank(a) * subrank(b) ≤ subrank(a * b) -/
theorem le_subrank_mul (a b : S) : p.subrank a * p.subrank b ≤ p.subrank (a * b) := by
  rw [le_subrank_iff]
  have ha := p.rel_subrank a
  have hb := p.rel_subrank b
  have heq : ((p.subrank a * p.subrank b : ℕ) : S) = (p.subrank a : S) * (p.subrank b : S) := by
    push_cast; ring
  rw [heq]
  -- (subrank a) * (subrank b) ≤ a * (subrank b) by mul_mono_left
  have h1 : p.rel ((p.subrank a : S) * (p.subrank b : S)) (a * (p.subrank b : S)) :=
    p.mul_mono_left (p.subrank b : S) ha
  -- a * (subrank b) ≤ a * b by mul_mono_right
  have h2 : p.rel (a * (p.subrank b : S)) (a * b) := p.mul_mono_right a hb
  exact p.trans _ _ _ h1 h2

/-! ### Powers of elements with 1 ≤_P a -/

/-- If 1 ≤_P a then 1 ≤_P a^n for all n ≥ 1 -/
theorem one_le_pow_of_one_le {a : S} (ha : p.rel 1 a) (n : ℕ) (hn : 0 < n) :
    p.rel 1 (a ^ n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => rw [pow_one]; exact ha
    | succ n =>
      rw [pow_succ]
      -- 1 ≤_P a^{n+1} by IH, and 1 ≤_P a
      -- 1 = 1 * 1 ≤_P a^{n+1} * a = a^{n+2}
      have h1 : p.rel (1 * 1) ((a ^ (n + 1)) * 1) := p.mul_mono_left 1 (ih (Nat.succ_pos n))
      have h2 : p.rel ((a ^ (n + 1)) * 1) ((a ^ (n + 1)) * a) := p.mul_mono_right _ ha
      simp only [mul_one] at h1 h2
      exact p.trans _ _ _ h1 h2

/-- If 1 ≤_P a then rank(a^n) ≥ 1 for all n ≥ 1 -/
theorem one_le_rank_pow_of_one_le {a : S} (ha : p.rel 1 a) (n : ℕ) (hn : 0 < n) :
    1 ≤ p.rank (a ^ n) := by
  have hrel := p.one_le_pow_of_one_le ha n hn
  have h1 : p.rel 1 (p.rank (a ^ n) : S) := p.trans _ _ _ hrel (p.rel_rank _)
  have h2 : p.rel ((1 : ℕ) : S) (p.rank (a ^ n) : S) := by simp only [Nat.cast_one]; exact h1
  exact (p.nat_compat 1 _).mpr h2

/-- If 1 ≤_P a then subrank(a^n) ≥ 1 for all n ≥ 1 -/
theorem one_le_subrank_pow_of_one_le {a : S} (ha : p.rel 1 a) (n : ℕ) (hn : 0 < n) :
    1 ≤ p.subrank (a ^ n) := by
  have hrel := p.one_le_pow_of_one_le ha n hn
  exact (p.le_subrank_iff _ 1).mpr (by simp only [Nat.cast_one]; exact hrel)

/-- Subrank is super-multiplicative for powers: subrank(a)^n ≤ subrank(a^n) -/
theorem le_subrank_pow {a : S} (n : ℕ) : p.subrank a ^ n ≤ p.subrank (a ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero]
    have h : (1 : S) = ((1 : ℕ) : S) := by simp
    rw [h]
    exact p.le_subrank_natCast 1
  | succ n ih =>
    calc p.subrank a ^ (n + 1)
        = p.subrank a ^ n * p.subrank a := by ring
      _ ≤ p.subrank (a ^ n) * p.subrank a := Nat.mul_le_mul_right _ ih
      _ ≤ p.subrank (a ^ n * a) := p.le_subrank_mul _ _
      _ = p.subrank (a ^ (n + 1)) := by rw [pow_succ]

/-! ### Asymptotic Rank and Subrank -/

/-- Rank is sub-multiplicative for powers: rank(a^n) ≤ rank(a)^n -/
theorem rank_pow_le (a : S) (n : ℕ) : p.rank (a ^ n) ≤ p.rank a ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    have h1 : p.rank (1 : S) = 1 := by
      have : (1 : S) = ((1 : ℕ) : S) := by simp
      rw [this, p.rank_natCast]
    simp only [h1]; rfl
  | succ n ih =>
    calc p.rank (a ^ (n + 1))
        = p.rank (a ^ n * a) := by ring_nf
      _ ≤ p.rank (a ^ n) * p.rank a := p.rank_mul_le _ _
      _ ≤ p.rank a ^ n * p.rank a := Nat.mul_le_mul_right _ ih
      _ = p.rank a ^ (n + 1) := by ring

/-- The set { rank(a^n)^{1/n} : n ≥ 1 } -/
def asympRankSet (a : S) : Set ℝ :=
  (fun n : ℕ => (p.rank (a ^ n) : ℝ) ^ (1 / (n : ℝ))) '' Set.Ici 1

/-- The set { subrank(a^n)^{1/n} : n ≥ 1 } -/
def asympSubrankSet (a : S) : Set ℝ :=
  (fun n : ℕ => (p.subrank (a ^ n) : ℝ) ^ (1 / (n : ℝ))) '' Set.Ici 1

theorem asympRankSet_nonempty (a : S) : (p.asympRankSet a).Nonempty := by
  refine ⟨(p.rank a : ℝ) ^ (1 : ℝ), 1, ?_, by simp⟩
  exact Set.mem_Ici.mpr (Nat.le_refl 1)

theorem asympSubrankSet_nonempty (a : S) : (p.asympSubrankSet a).Nonempty := by
  refine ⟨(p.subrank a : ℝ) ^ (1 : ℝ), 1, ?_, by simp⟩
  exact Set.mem_Ici.mpr (Nat.le_refl 1)

theorem asympRankSet_bddBelow (a : S) : BddBelow (p.asympRankSet a) := by
  refine ⟨0, fun x hx => ?_⟩
  obtain ⟨n, _, rfl⟩ := hx
  apply Real.rpow_nonneg (Nat.cast_nonneg _)

theorem asympSubrankSet_bddAbove (a : S) : BddAbove (p.asympSubrankSet a) := by
  refine ⟨p.rank a, fun x hx => ?_⟩
  obtain ⟨n, hn, rfl⟩ := hx
  have hn' : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn')
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  -- subrank(a^n)^{1/n} ≤ rank(a^n)^{1/n} ≤ rank(a)
  calc (p.subrank (a ^ n) : ℝ) ^ (1 / (n : ℝ))
      ≤ (p.rank (a ^ n) : ℝ) ^ (1 / (n : ℝ)) := by
        apply Real.rpow_le_rpow (Nat.cast_nonneg _)
        · exact Nat.cast_le.mpr (p.subrank_le_rank _)
        · exact div_nonneg (by norm_num) (le_of_lt hn_pos)
    _ ≤ ((p.rank a : ℝ) ^ n) ^ (1 / (n : ℝ)) := by
        apply Real.rpow_le_rpow (Nat.cast_nonneg _)
        · -- rank(a^n) ≤ rank(a)^n by submultiplicativity
          have h := p.rank_pow_le a n
          have : (p.rank a ^ n : ℕ) = (p.rank a : ℕ) ^ n := rfl
          calc (p.rank (a ^ n) : ℝ) ≤ ((p.rank a ^ n : ℕ) : ℝ) := Nat.cast_le.mpr h
            _ = (p.rank a : ℝ) ^ n := by push_cast; rfl
        exact div_nonneg (by norm_num) (le_of_lt hn_pos)
    _ = p.rank a := by
        rw [← Real.rpow_natCast (p.rank a : ℝ) n, ← Real.rpow_mul (Nat.cast_nonneg _)]
        rw [mul_one_div_cancel hn_ne, Real.rpow_one]

/-- Asymptotic rank: infimum of rank(a^n)^{1/n} over n ≥ 1.
    By Fekete's lemma (sub-multiplicativity of rank), this equals the limit. -/
noncomputable def asympRank (a : S) : ℝ :=
  sInf (p.asympRankSet a)

/-- Asymptotic subrank: supremum of subrank(a^n)^{1/n} over n ≥ 1.
    By Fekete's lemma (super-multiplicativity of subrank), this equals the limit. -/
noncomputable def asympSubrank (a : S) : ℝ :=
  sSup (p.asympSubrankSet a)

/-- Asymptotic rank is nonnegative -/
theorem asympRank_nonneg (a : S) : 0 ≤ p.asympRank a := by
  unfold asympRank
  apply le_csInf (p.asympRankSet_nonempty a)
  intro x hx
  obtain ⟨n, _, rfl⟩ := hx
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- Asymptotic subrank is nonnegative -/
theorem asympSubrank_nonneg (a : S) : 0 ≤ p.asympSubrank a := by
  unfold asympSubrank
  have hmem : (p.subrank (a ^ 1) : ℝ) ^ (1 / (1 : ℝ)) ∈ p.asympSubrankSet a := by
    refine ⟨1, Nat.le_refl 1, ?_⟩
    simp only [pow_one, one_div, Nat.cast_one, inv_one, Real.rpow_one]
  have helem_nonneg : 0 ≤ (p.subrank (a ^ 1) : ℝ) ^ (1 / (1 : ℝ)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact le_csSup_of_le (p.asympSubrankSet_bddAbove a) hmem helem_nonneg

/-! ### Gapped Elements -/

-- `StrassenPreorder.IsGapped` is defined in `AsymptoticSpectrum.lean` (it references
-- the asymptotic spectrum `𝒳_P`, defined downstream of this file). The definition
-- matches the survey `def:gapped` (survey.tex:1912-1914): disjunct (iii) is
-- `∃ φ ∈ 𝒳, φ(a) = 1`, NOT the too-strong `a ∼ 1`.

/-! ### Properties of Asymptotic Rank/Subrank -/

/-- Rank of 1 is 1 -/
theorem rank_one : p.rank (1 : S) = 1 := by
  have h : (1 : S) = ((1 : ℕ) : S) := by simp
  rw [h, p.rank_natCast]

/-- Subrank of 1 is 1 -/
theorem subrank_one : p.subrank (1 : S) = 1 := by
  have h : (1 : S) = ((1 : ℕ) : S) := by simp
  rw [h, p.subrank_natCast']

/-- Rank is sub-multiplicative for powers: rank(a^{n+m}) ≤ rank(a^n) * rank(a^m) -/
theorem rank_pow_submult (a : S) (n m : ℕ) :
    p.rank (a ^ (n + m)) ≤ p.rank (a ^ n) * p.rank (a ^ m) := by
  rw [pow_add]
  exact p.rank_mul_le _ _

/-- Asymptotic rank of a^n is (asympRank a)^n -/
theorem asympRank_pow (a : S) (n : ℕ) : p.asympRank (a ^ n) = (p.asympRank a) ^ n := by
  -- For n = 0: a^0 = 1, so asympRank(1) = 1 = R^0
  -- For n > 0: (a^n)^k = a^{nk}, use change of variables
  cases n with
  | zero =>
    simp only [pow_zero]
    -- asympRank(1) = sInf { rank(1^k)^{1/k} : k ≥ 1 } = sInf {1} = 1
    have hrank1 : p.rank (1 : S) = 1 := by
      have : (1 : S) = ((1 : ℕ) : S) := by simp
      rw [this, p.rank_natCast]
    have h1 : ∀ k : ℕ, 0 < k → p.rank ((1 : S) ^ k) = 1 := by
      intro k _; simp only [one_pow, hrank1]
    -- The set asympRankSet 1 = { 1^{1/k} = 1 : k ≥ 1 } = {1}
    have hset : p.asympRankSet 1 = {1} := by
      ext x
      simp only [asympRankSet, Set.mem_image, Set.mem_Ici, Set.mem_singleton_iff]
      constructor
      · rintro ⟨k, hk, rfl⟩
        rw [one_pow, hrank1]
        simp only [Nat.cast_one, Real.one_rpow]
      · intro hx
        refine ⟨1, Nat.le_refl 1, ?_⟩
        rw [pow_one, hrank1, one_div, Nat.cast_one, inv_one, Real.rpow_one, hx]
    unfold asympRank
    rw [hset, csInf_singleton]
  | succ n =>
    -- asympRank(a^{n+1}) = sInf_k { rank((a^{n+1})^k)^{1/k} }
    --                    = sInf_k { rank(a^{(n+1)k})^{1/k} }
    --                    = sInf_k { (rank(a^{(n+1)k})^{1/((n+1)k)})^{n+1} }
    -- By Fekete, this equals (lim_m rank(a^m)^{1/m})^{n+1} = (asympRank a)^{n+1}
    let m := n + 1
    have hm_pos : (0 : ℝ) < m := by simp only [m]; positivity
    have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
    -- Key: rank((a^m)^k)^{1/k} = (rank(a^{mk})^{1/(mk)})^m
    have hrewrite : ∀ k : ℕ, 0 < k →
        (p.rank ((a ^ m) ^ k) : ℝ) ^ (1 / (k : ℝ)) =
        ((p.rank (a ^ (m * k)) : ℝ) ^ (1 / ((m : ℝ) * (k : ℝ)))) ^ (m : ℝ) := by
      intro k hk
      have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
      have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
      have hmk_pos : (0 : ℝ) < (m : ℝ) * (k : ℝ) := mul_pos hm_pos hk_pos
      have hmk_ne : (m : ℝ) * (k : ℝ) ≠ 0 := ne_of_gt hmk_pos
      rw [← pow_mul]
      -- LHS: rank(a^{mk})^{1/k}
      -- RHS: (rank(a^{mk})^{1/(mk)})^m
      -- First show 1/k = m/(mk)
      have heq : (1 : ℝ) / (k : ℝ) = (m : ℝ) / ((m : ℝ) * (k : ℝ)) := by field_simp
      rw [heq]
      -- Now show x^{m/(mk)} = (x^{1/(mk)})^m
      -- The RHS is x^{(1/(mk)) * m} = x^{m/(mk)} by rpow_mul
      symm
      rw [← Real.rpow_mul (Nat.cast_nonneg _)]
      congr 1
      field_simp
    -- The set asympRankSet(a^m) has elements (rank(a^{mk}))^{1/k}
    -- These equal (rank(a^{mk})^{1/(mk)})^m (by hrewrite)
    -- Let f(j) = rank(a^j)^{1/j}. Then asympRankSet(a^m) = {f(mk)^m : k ≥ 1}
    -- We show: sInf {f(mk)^m} = asympRank(a)^m = (sInf {f(j)})^m
    apply le_antisymm
    · -- ≤ direction: asympRank(a^m) ≤ asympRank(a)^m
      -- Case split on whether rank(a^j) = 0 for some j ≥ 1
      by_cases hrank_zero : ∃ j, j ≥ 1 ∧ p.rank (a ^ j) = 0
      · -- If rank(a^j) = 0 for some j, then asympRank(a) = 0
        obtain ⟨j, hj_ge1, hrj⟩ := hrank_zero
        have hasymprk_zero : p.asympRank a = 0 := by
          unfold asympRank
          have hj_ne : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hj_ge1)
          have h1j_ne : (1 : ℝ) / j ≠ 0 := one_div_ne_zero hj_ne
          have hmem : (0 : ℝ) ∈ p.asympRankSet a := by
            simp only [asympRankSet, Set.mem_image]
            refine ⟨j, hj_ge1, ?_⟩
            simp only [hrj, Nat.cast_zero, Real.zero_rpow h1j_ne]
          exact le_antisymm (csInf_le (p.asympRankSet_bddBelow a) hmem) (p.asympRank_nonneg a)
        -- Also show asympRank(a^m) = 0
        have hasymprk_m_zero : p.asympRank (a ^ m) = 0 := by
          -- rank(a^{mj}) ≤ rank(a^j)^m = 0, so 0 ∈ asympRankSet(a^m)
          have hj_pos : 0 < j := Nat.one_le_iff_ne_zero.mp hj_ge1 |> Nat.pos_of_ne_zero
          have hmj_ge1 : 1 ≤ m * j := Nat.one_le_iff_ne_zero.mpr
            (Nat.pos_iff_ne_zero.mp (Nat.mul_pos (Nat.succ_pos n) hj_pos))
          have hrank_mj : p.rank (a ^ (m * j)) = 0 := by
            apply Nat.le_zero.mp
            calc p.rank (a ^ (m * j))
                = p.rank ((a ^ j) ^ m) := by rw [← pow_mul, mul_comm]
              _ ≤ (p.rank (a ^ j)) ^ m := p.rank_pow_le (a ^ j) m
              _ = 0 ^ m := by rw [hrj]
              _ = 0 := zero_pow (Nat.succ_ne_zero n)
          have hj_ne : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hj_ge1)
          have h1j_ne : (1 : ℝ) / j ≠ 0 := one_div_ne_zero hj_ne
          have hmem : (0 : ℝ) ∈ p.asympRankSet (a ^ m) := by
            simp only [asympRankSet, Set.mem_image]
            refine ⟨j, hj_ge1, ?_⟩
            have : (a ^ m) ^ j = a ^ (m * j) := by rw [← pow_mul]
            rw [this, hrank_mj]
            simp only [Nat.cast_zero, Real.zero_rpow h1j_ne]
          exact le_antisymm (csInf_le (p.asympRankSet_bddBelow _) hmem) (p.asympRank_nonneg _)
        rw [hasymprk_m_zero, hasymprk_zero, zero_pow (Nat.succ_ne_zero n)]
      · -- Otherwise rank(a^j) ≥ 1 for all j ≥ 1, use Fekete
        push_neg at hrank_zero
        let r : ℕ → ℝ := fun j => (p.rank (a ^ j) : ℝ)
        have hr_ge1 : ∀ j, 1 ≤ r j := fun j => by
          by_cases hj : j = 0
          · simp only [hj, pow_zero, r]; exact Nat.one_le_cast.mpr (le_of_eq p.rank_one.symm)
          · simp only [r]
            exact Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr
              (hrank_zero j (Nat.one_le_iff_ne_zero.mpr hj)))
        have hr_submult : ∀ i j, r (i + j) ≤ r i * r j := fun i j => by
          simp only [r]
          have h := p.rank_mul_le (a ^ i) (a ^ j)
          rw [← pow_add] at h
          exact_mod_cast h
        have hfek := fekete_multiplicative hr_ge1 hr_submult
        have hfek_eq :
            sInf ((fun j => r j ^ (1 / (j : ℝ))) '' {j : ℕ | 1 ≤ j}) = p.asympRank a := by
          unfold asympRank asympRankSet; rfl
        rw [hfek_eq] at hfek
        -- The Tendsto gives us that r(j)^{1/j} → asympRank(a)
        -- For the subsequence j = mk, r(mk)^{1/(mk)} → asympRank(a)
        -- And (r(mk)^{1/(mk)})^m = r(mk)^{1/k} → asympRank(a)^m
        -- The asympRankSet(a^m) = { r(mk)^{1/k} : k ≥ 1 }
        -- So sInf(asympRankSet(a^m)) ≤ lim r(mk)^{1/k} = asympRank(a)^m
        unfold asympRank
        -- Show the limit bound directly
        -- Construct the Tendsto for r(mk)^{1/k}
        have hsubseq : Filter.Tendsto (fun k => r (m * k) ^ (1 / (k : ℝ)))
            Filter.atTop (nhds (p.asympRank a ^ (n + 1))) := by
          -- r(mk)^{1/k} = (r(mk)^{1/(mk)})^m
          have hconv : ∀ k, k ≠ 0 → r (m * k) ^ (1 / (k : ℝ)) =
              (r (m * k) ^ (1 / ((m : ℝ) * (k : ℝ)))) ^ (m : ℝ) := by
            intro k hk
            have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
            have hmk_ne : (m : ℝ) * (k : ℝ) ≠ 0 := mul_ne_zero hm_ne (ne_of_gt hk_pos)
            rw [← Real.rpow_mul (Nat.cast_nonneg _)]
            congr 1
            field_simp
          -- Eventually k ≠ 0, so we can rewrite
          rw [show (p.asympRank a : ℝ) ^ (n + 1) = (p.asympRank a) ^ (m : ℝ) by
            rw [Real.rpow_natCast]]
          apply Filter.Tendsto.congr'
          · -- Eventually equal to (r(mk)^{1/(mk)})^m
            filter_upwards [Filter.eventually_gt_atTop 0] with k hk
            exact (hconv k (Nat.pos_iff_ne_zero.mp hk)).symm
          · -- (r(mk)^{1/(mk)})^m → asympRank(a)^m
            apply Filter.Tendsto.rpow_const
            · -- r(mk)^{1/(mk)} → asympRank(a) as k → ∞
              -- This is a subsequence of the Fekete convergence
              have hsubseq_to_atTop :
                  Filter.Tendsto (fun k => m * k) Filter.atTop Filter.atTop := by
                apply Filter.tendsto_atTop_atTop_of_monotone
                · intro x y hxy; exact Nat.mul_le_mul_left m hxy
                · intro b; use b; exact Nat.le_mul_of_pos_left b (Nat.succ_pos n)
              have hcomp := Filter.Tendsto.comp hfek hsubseq_to_atTop
              -- The composition gives r(m*k)^{1/(m*k)}, need to convert exponent
              apply Filter.Tendsto.congr _ hcomp
              intro k
              simp only [Function.comp_apply]
              congr 1
              rw [Nat.cast_mul]
            · right; exact Nat.cast_nonneg m
        -- Use ge_of_tendsto: if sInf ≤ f(k) eventually and f → L, then sInf ≤ L
        apply ge_of_tendsto hsubseq
        -- Eventually f(k) ∈ asympRankSet(a^m), so sInf ≤ f(k)
        filter_upwards [Filter.eventually_ge_atTop 1] with k hk
        apply csInf_le (p.asympRankSet_bddBelow (a ^ m))
        simp only [asympRankSet, Set.mem_image]
        exact ⟨k, hk, by simp only [r, ← pow_mul]⟩
    · -- ≥ direction: asympRank(a^m) ≥ asympRank(a)^m
      -- Each element of asympRankSet(a^m) is ≥ asympRank(a)^m
      apply le_csInf (p.asympRankSet_nonempty (a ^ m))
      intro x hx
      simp only [asympRankSet, Set.mem_image, Set.mem_Ici] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      have hk_pos : 0 < k := Nat.one_le_iff_ne_zero.mp hk |> Nat.pos_of_ne_zero
      rw [hrewrite k hk_pos]
      -- Now show ((p.rank (a ^ (m * k)))^{1/(m*k)})^m ≥ asympRank(a)^m
      have hmk_ge1 : 1 ≤ m * k := Nat.one_le_iff_ne_zero.mpr
        (Nat.pos_iff_ne_zero.mp (Nat.mul_pos (Nat.succ_pos n) hk_pos))
      have hrank_pow_ge :
          (p.rank (a ^ (m * k)) : ℝ) ^ (1 / ((m : ℝ) * (k : ℝ))) ≥ p.asympRank a := by
        apply csInf_le (p.asympRankSet_bddBelow a)
        simp only [asympRankSet, Set.mem_image, Set.mem_Ici]
        refine ⟨m * k, hmk_ge1, ?_⟩
        congr 1
        rw [Nat.cast_mul]
      have hm_nn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hbase_nn : 0 ≤ (p.rank (a ^ (m * k)) : ℝ) ^ (1 / ((m : ℝ) * (k : ℝ))) :=
        Real.rpow_nonneg (Nat.cast_nonneg _) _
      calc (sInf (p.asympRankSet a)) ^ (n + 1)
          = (p.asympRank a) ^ (n + 1) := rfl
        _ = (p.asympRank a) ^ (m : ℝ) := by rw [Real.rpow_natCast]
        _ ≤ ((p.rank (a ^ (m * k)) : ℝ) ^ (1 / ((m : ℝ) * (k : ℝ)))) ^ (m : ℝ) :=
            Real.rpow_le_rpow (p.asympRank_nonneg a) hrank_pow_ge hm_nn

/-- Asymptotic rank is monotone under the asymptotic preorder -/
theorem asympRank_mono {a b : S} (h : AsympRel p a b) : p.asympRank a ≤ p.asympRank b := by
  -- From AsympRel, get witness x with sInf x_n^{1/n} = 1
  -- For all n ≥ 1: a^n ≤_P b^n * x_n
  obtain ⟨x, hbound, hxinf⟩ := h
  -- For each n ≥ 1: rank(a^n) ≤ rank(b^n * x_n) ≤ rank(b^n) * rank(x_n) = rank(b^n) * x_n
  have hrank_bound : ∀ n, n ≥ 1 → p.rank (a ^ n) ≤ p.rank (b ^ n) * x n := by
    intro n hn
    have h1 := hbound n hn
    have h2 := p.rank_mono h1
    have h3 := p.rank_mul_le (b ^ n) (x n : S)
    have h4 : p.rank ((x n : ℕ) : S) = x n := p.rank_natCast (x n)
    calc p.rank (a ^ n) ≤ p.rank (b ^ n * (x n : S)) := h2
      _ ≤ p.rank (b ^ n) * p.rank ((x n : ℕ) : S) := h3
      _ = p.rank (b ^ n) * x n := by rw [h4]
  -- Taking nth roots: rank(a^n)^{1/n} ≤ rank(b^n)^{1/n} * x_n^{1/n}
  have hrpow_bound : ∀ n : ℕ, n ≥ 1 →
      (p.rank (a ^ n) : ℝ) ^ (1 / (n : ℝ)) ≤
      (p.rank (b ^ n) : ℝ) ^ (1 / (n : ℝ)) * (x n : ℝ) ^ (1 / (n : ℝ)) := by
    intro n hn
    have hrank_a_nn : (0 : ℝ) ≤ p.rank (a ^ n) := Nat.cast_nonneg _
    have hrank_b_nn : (0 : ℝ) ≤ p.rank (b ^ n) := Nat.cast_nonneg _
    have hx_nn : (0 : ℝ) ≤ x n := Nat.cast_nonneg _
    have hn_pos : (0 : ℝ) < n :=
      Nat.cast_pos.mpr (Nat.one_le_iff_ne_zero.mp hn |> Nat.pos_of_ne_zero)
    have hexp_nn : 0 ≤ 1 / (n : ℝ) := div_nonneg (by norm_num) (le_of_lt hn_pos)
    calc (p.rank (a ^ n) : ℝ) ^ (1 / (n : ℝ))
        ≤ ((p.rank (b ^ n) * x n : ℕ) : ℝ) ^ (1 / (n : ℝ)) := by
          apply Real.rpow_le_rpow hrank_a_nn (Nat.cast_le.mpr (hrank_bound n hn)) hexp_nn
      _ = ((p.rank (b ^ n) : ℝ) * (x n : ℝ)) ^ (1 / (n : ℝ)) := by
          simp only [Nat.cast_mul]
      _ = (p.rank (b ^ n) : ℝ) ^ (1 / (n : ℝ)) * (x n : ℝ) ^ (1 / (n : ℝ)) :=
          Real.mul_rpow hrank_b_nn hx_nn
  -- Case split: either rank(a^n) = 0 for some n (giving asympRank(a) = 0), or rank ≥ 1 for all n
  by_cases hrank_a_zero : ∃ n, n ≥ 1 ∧ p.rank (a ^ n) = 0
  · -- Case 1: rank(a^n) = 0 for some n ≥ 1
    -- Then asympRank(a) = 0 ≤ asympRank(b)
    obtain ⟨n, hn, hrk⟩ := hrank_a_zero
    have hasymprk_a_le_zero : p.asympRank a ≤ 0 := by
      unfold asympRank
      have hn_ne : (n : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn)
      have h1n_ne : (1 : ℝ) / (n : ℝ) ≠ 0 := one_div_ne_zero hn_ne
      have hmem : (0 : ℝ) ∈ p.asympRankSet a := by
        simp only [asympRankSet, Set.mem_image, Set.mem_Ici]
        refine ⟨n, hn, ?_⟩
        simp only [hrk, Nat.cast_zero, Real.zero_rpow h1n_ne]
      exact csInf_le (p.asympRankSet_bddBelow a) hmem
    calc p.asympRank a ≤ 0 := hasymprk_a_le_zero
      _ ≤ p.asympRank b := p.asympRank_nonneg b
  · -- Case 2: rank(a^n) ≥ 1 for all n ≥ 1. Use Fekete and limit comparison.
    push_neg at hrank_a_zero
    -- x_n ≥ 1 for all n ≥ 1 (from sInf = 1)
    have hx_ge1 : ∀ n, n ≥ 1 → x n ≥ 1 := by
      intro n hn
      by_contra hlt
      push_neg at hlt
      have hxn0 : x n = 0 := Nat.lt_one_iff.mp hlt
      have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn)
      have h1n_ne : (1 : ℝ) / n ≠ 0 := one_div_ne_zero hn_ne
      have hval : (x n : ℝ) ^ ((1 : ℝ) / n) = 0 := by
        simp only [hxn0, Nat.cast_zero, Real.zero_rpow h1n_ne]
      have hmem : (0 : ℝ) ∈ (fun m => (x m : ℝ) ^ (1 / m : ℝ)) '' {m : ℕ | 1 ≤ m} :=
        ⟨n, hn, hval⟩
      have hbdd : BddBelow ((fun m => (x m : ℝ) ^ (1 / m : ℝ)) '' {m : ℕ | 1 ≤ m}) := by
        use 0; intro z hz; obtain ⟨m, _, rfl⟩ := hz
        exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hle := csInf_le hbdd hmem
      rw [hxinf] at hle; linarith
    -- Use submultClosure to get a submultiplicative witness
    let y := submultClosure x
    have hy_ge1 := submultClosure_ge_one x hx_ge1
    have hy_submult := submultClosure_submult x
    have hy_sInf : sInf ((fun n => (y n : ℝ) ^ (1 / n : ℝ)) '' {n : ℕ | 1 ≤ n}) = 1 :=
      submultClosure_sInf_eq_one_of x hx_ge1 hxinf
    -- The key is that submultClosure_bound gives: a^n ≤_P b^n * y_n
    -- So we can use the bound with y (submultiplicative) instead of x
    have hy_bound : ∀ n, n ≥ 1 → p.rel (a ^ n) (b ^ n * (y n : S)) :=
      submultClosure_bound p a b x hbound
    -- Derive the rank bound with y
    have hrank_bound_y : ∀ n, n ≥ 1 → p.rank (a ^ n) ≤ p.rank (b ^ n) * y n := by
      intro n hn
      have h1 := hy_bound n hn
      have h2 := p.rank_mono h1
      have h3 := p.rank_mul_le (b ^ n) (y n : S)
      have h4 : p.rank ((y n : ℕ) : S) = y n := p.rank_natCast (y n)
      calc p.rank (a ^ n) ≤ p.rank (b ^ n * (y n : S)) := h2
        _ ≤ p.rank (b ^ n) * p.rank ((y n : ℕ) : S) := h3
        _ = p.rank (b ^ n) * y n := by rw [h4]
    -- Taking nth roots with y
    have hrpow_bound_y : ∀ n : ℕ, n ≥ 1 →
        (p.rank (a ^ n) : ℝ) ^ (1 / (n : ℝ)) ≤
        (p.rank (b ^ n) : ℝ) ^ (1 / (n : ℝ)) * (y n : ℝ) ^ (1 / (n : ℝ)) := by
      intro n hn
      have hrank_a_nn : (0 : ℝ) ≤ p.rank (a ^ n) := Nat.cast_nonneg _
      have hrank_b_nn : (0 : ℝ) ≤ p.rank (b ^ n) := Nat.cast_nonneg _
      have hy_nn : (0 : ℝ) ≤ y n := Nat.cast_nonneg _
      have hn_pos : (0 : ℝ) < n :=
        Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn))
      have hexp_nn : 0 ≤ 1 / (n : ℝ) := div_nonneg (by norm_num) (le_of_lt hn_pos)
      calc (p.rank (a ^ n) : ℝ) ^ (1 / (n : ℝ))
          ≤ ((p.rank (b ^ n) * y n : ℕ) : ℝ) ^ (1 / (n : ℝ)) := by
            apply Real.rpow_le_rpow hrank_a_nn (Nat.cast_le.mpr (hrank_bound_y n hn)) hexp_nn
        _ = ((p.rank (b ^ n) : ℝ) * (y n : ℝ)) ^ (1 / (n : ℝ)) := by simp only [Nat.cast_mul]
        _ = (p.rank (b ^ n) : ℝ) ^ (1 / (n : ℝ)) * (y n : ℝ) ^ (1 / (n : ℝ)) :=
            Real.mul_rpow hrank_b_nn hy_nn
    -- Now use Fekete and limit comparison
    -- Define sequences
    let r_a : ℕ → ℝ := fun n => (p.rank (a ^ n) : ℝ)
    let r_b : ℕ → ℝ := fun n => (p.rank (b ^ n) : ℝ)
    let y_seq : ℕ → ℝ := fun n => (y n : ℝ)
    -- Fekete conditions for r_a
    have hra_ge1 : ∀ n, 1 ≤ r_a n := fun n => by
      by_cases hn : n = 0
      · simp only [hn, pow_zero, r_a]; have : p.rank (1 : S) = 1 := p.rank_one; simp [this]
      · exact Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr (hrank_a_zero n
            (Nat.one_le_iff_ne_zero.mpr hn)))
    have hra_submult : ∀ n m, r_a (n + m) ≤ r_a n * r_a m := fun n m => by
      simp only [r_a]
      have h := p.rank_mul_le (a ^ n) (a ^ m)
      calc (p.rank (a ^ (n + m)) : ℝ) = (p.rank (a ^ n * a ^ m) : ℝ) := by rw [pow_add]
        _ ≤ (p.rank (a ^ n) * p.rank (a ^ m) : ℕ) := Nat.cast_le.mpr h
        _ = (p.rank (a ^ n) : ℝ) * (p.rank (a ^ m) : ℝ) := by push_cast; ring
    -- Fekete conditions for r_b
    have hrb_ge1 : ∀ n, 1 ≤ r_b n := fun n => by
      by_cases hn : n = 0
      · simp only [hn, pow_zero, r_b]; have : p.rank (1 : S) = 1 := p.rank_one; simp [this]
      · -- From hrank_bound_y: rank(a^n) ≤ rank(b^n) * y_n
        -- If rank(b^n) = 0, then rank(a^n) ≤ 0, so rank(a^n) = 0, contradiction with hrank_a_zero
        by_contra hlt; push_neg at hlt
        have hrb0 : p.rank (b ^ n) = 0 := by
          have h1 : (p.rank (b ^ n) : ℝ) < 1 := hlt
          have h2 : p.rank (b ^ n) < 1 := by
            rw [← Nat.cast_one] at h1
            exact Nat.cast_lt.mp h1
          exact Nat.lt_one_iff.mp h2
        have hn_ge1 : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn
        have hbound := hrank_bound_y n hn_ge1
        rw [hrb0, Nat.zero_mul] at hbound
        have hra0 : p.rank (a ^ n) = 0 := Nat.le_zero.mp hbound
        exact hrank_a_zero n hn_ge1 hra0
    have hrb_submult : ∀ n m, r_b (n + m) ≤ r_b n * r_b m := fun n m => by
      simp only [r_b]
      have h := p.rank_mul_le (b ^ n) (b ^ m)
      calc (p.rank (b ^ (n + m)) : ℝ) = (p.rank (b ^ n * b ^ m) : ℝ) := by rw [pow_add]
        _ ≤ (p.rank (b ^ n) * p.rank (b ^ m) : ℕ) := Nat.cast_le.mpr h
        _ = (p.rank (b ^ n) : ℝ) * (p.rank (b ^ m) : ℝ) := by push_cast; ring
    -- Fekete conditions for y
    have hy_ge1_all : ∀ n, 1 ≤ y_seq n := by
      intro n
      by_cases hn : n = 0
      · subst hn; simp only [y_seq, y]; simp [submultClosure_zero]
      · exact Nat.one_le_cast.mpr (hy_ge1 n (Nat.one_le_iff_ne_zero.mpr hn))
    have hy0 : y 0 = 1 := submultClosure_zero x
    have hy_submult_cast : ∀ n m, y_seq (n + m) ≤ y_seq n * y_seq m := by
      intro n m; simp only [y_seq]
      -- submultClosure_submult requires n ≥ 1 and m ≥ 1
      -- For n = 0 or m = 0, submultClosure x 0 = 1,
      -- so the inequality becomes y m ≤ 1 * y m or similar
      by_cases hn : n = 0
      · subst hn; simp only [zero_add, hy0, Nat.cast_one, one_mul]; rfl
      by_cases hm : m = 0
      · subst hm; simp only [add_zero, hy0, Nat.cast_one, mul_one]; rfl
      have hn1 : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn
      have hm1 : m ≥ 1 := Nat.one_le_iff_ne_zero.mpr hm
      calc (y (n + m) : ℝ) ≤ (y n * y m : ℕ) := Nat.cast_le.mpr (hy_submult n m hn1 hm1)
        _ = (y n : ℝ) * (y m : ℝ) := by push_cast; ring
    -- Apply Fekete to get Tendsto
    have hfek_a := fekete_multiplicative hra_ge1 hra_submult
    have hfek_b := fekete_multiplicative hrb_ge1 hrb_submult
    have hfek_y := fekete_multiplicative hy_ge1_all hy_submult_cast
    -- The Fekete limits match asympRank and 1
    have hfek_a_eq :
        sInf ((fun n => r_a n ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n}) = p.asympRank a := by
      unfold asympRank asympRankSet; rfl
    have hfek_b_eq :
        sInf ((fun n => r_b n ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n}) = p.asympRank b := by
      unfold asympRank asympRankSet; rfl
    rw [hfek_a_eq] at hfek_a; rw [hfek_b_eq] at hfek_b; rw [hy_sInf] at hfek_y
    -- Pointwise bound for limit comparison
    have hpointwise : ∀ n, n ≥ 1 → r_a n ^ (1 / (n : ℝ)) ≤
        r_b n ^ (1 / (n : ℝ)) * y_seq n ^ (1 / (n : ℝ)) := by
      intro n hn; exact hrpow_bound_y n hn
    -- RHS = r_b^{1/n} * y^{1/n} tends to asympRank(b) * 1 = asympRank(b)
    have htend_rhs : Filter.Tendsto (fun n => r_b n ^ (1 / (n : ℝ)) * y_seq n ^ (1 / (n : ℝ)))
        Filter.atTop (nhds (p.asympRank b * 1)) := by
      apply Filter.Tendsto.mul hfek_b hfek_y
    rw [mul_one] at htend_rhs
    -- Apply limit comparison: LHS → asympRank(a), RHS → asympRank(b), LHS ≤ RHS
    apply le_of_tendsto_of_tendsto hfek_a htend_rhs
    filter_upwards [Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩] with n hn
    exact hpointwise n hn

/-- For natural numbers, asymptotic rank equals the number -/
theorem asympRank_natCast (n : ℕ) (_hn : 0 < n) : p.asympRank (n : S) = n := by
  -- asympRank(n) = sInf { rank(n^k)^{1/k} : k ≥ 1 } = sInf { n } = n
  -- Since rank(n^k) = n^k (by rank_natCast) and (n^k)^{1/k} = n
  have hrank : ∀ k : ℕ, 0 < k → p.rank ((n : S) ^ k) = n ^ k := by
    intro k _
    have : ((n : S) ^ k) = ((n ^ k : ℕ) : S) := by push_cast; ring
    rw [this, p.rank_natCast]
  -- The set is {n}
  have hset : p.asympRankSet (n : S) = {(n : ℝ)} := by
    ext x
    simp only [asympRankSet, Set.mem_image, Set.mem_Ici, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [hrank k hk]
      have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
      have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
      have hn_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      calc ((n ^ k : ℕ) : ℝ) ^ (1 / (k : ℝ))
          = ((n : ℝ) ^ k) ^ (1 / (k : ℝ)) := by push_cast; ring
        _ = ((n : ℝ) ^ k) ^ ((k : ℝ)⁻¹) := by rw [one_div]
        _ = (n : ℝ) := by rw [← Real.rpow_natCast (n : ℝ) k, ← Real.rpow_mul hn_nonneg,
                              mul_inv_cancel₀ hk_ne, Real.rpow_one]
    · intro hx
      refine ⟨1, Nat.le_refl 1, ?_⟩
      simp only [pow_one, one_div, Nat.cast_one, inv_one, Real.rpow_one]
      rw [p.rank_natCast n, hx]
  unfold asympRank
  rw [hset, csInf_singleton]

/-- For natural numbers, asymptotic subrank equals the number -/
theorem asympSubrank_natCast (n : ℕ) : p.asympSubrank (n : S) = n := by
  -- asympSubrank(n) = sSup { subrank(n^k)^{1/k} : k ≥ 1 } = sSup { n } = n
  -- Since subrank(n^k) = n^k (by subrank_natCast') and (n^k)^{1/k} = n
  have hsubrank : ∀ k : ℕ, 0 < k → p.subrank ((n : S) ^ k) = n ^ k := by
    intro k _
    have : ((n : S) ^ k) = ((n ^ k : ℕ) : S) := by push_cast; ring
    rw [this, p.subrank_natCast']
  -- The set is {n}
  have hset : p.asympSubrankSet (n : S) = {(n : ℝ)} := by
    ext x
    simp only [asympSubrankSet, Set.mem_image, Set.mem_Ici, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [hsubrank k hk]
      have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
      have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
      have hn_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      calc ((n ^ k : ℕ) : ℝ) ^ (1 / (k : ℝ))
          = ((n : ℝ) ^ k) ^ (1 / (k : ℝ)) := by push_cast; ring
        _ = ((n : ℝ) ^ k) ^ ((k : ℝ)⁻¹) := by rw [one_div]
        _ = (n : ℝ) := by rw [← Real.rpow_natCast (n : ℝ) k, ← Real.rpow_mul hn_nonneg,
                              mul_inv_cancel₀ hk_ne, Real.rpow_one]
    · intro hx
      refine ⟨1, Nat.le_refl 1, ?_⟩
      simp only [pow_one, one_div, Nat.cast_one, inv_one, Real.rpow_one]
      rw [p.subrank_natCast' n, hx]
  unfold asympSubrank
  rw [hset, csSup_singleton]

/-- 1 ≤ asympSubrank a ≤ asympRank a for all a ≥_P 1 -/
theorem one_le_asympSubrank_le_asympRank {a : S} (ha : p.rel 1 a) :
    1 ≤ p.asympSubrank a ∧ p.asympSubrank a ≤ p.asympRank a := by
  constructor
  · -- 1 ≤ asympSubrank a = sSup { subrank(a^n)^{1/n} : n ≥ 1 }
    -- The set contains subrank(a)^1 ≥ 1 since 1 ≤_P a implies subrank(a) ≥ 1
    unfold asympSubrank
    have h1le : 1 ≤ p.subrank a :=
      (p.le_subrank_iff a 1).mpr (by simp only [Nat.cast_one]; exact ha)
    have hmem : (p.subrank a : ℝ) ∈ p.asympSubrankSet a := by
      simp only [asympSubrankSet, Set.mem_image, Set.mem_Ici]
      refine ⟨1, Nat.le_refl 1, ?_⟩
      simp only [pow_one, one_div, Nat.cast_one, inv_one, Real.rpow_one]
    calc (1 : ℝ) ≤ (p.subrank a : ℝ) := Nat.one_le_cast.mpr h1le
      _ ≤ sSup (p.asympSubrankSet a) := le_csSup (p.asympSubrankSet_bddAbove a) hmem
  · -- asympSubrank a ≤ asympRank a
    -- Strategy: Use Fekete to show both are limits, then use limit comparison
    -- Step 1: Define the sequences
    let r : ℕ → ℝ := fun n => (p.rank (a ^ n) : ℝ)
    let s : ℕ → ℝ := fun n => (p.subrank (a ^ n) : ℝ)
    -- Step 2: Verify Fekete conditions for rank (submultiplicative, ≥ 1)
    have hr_ge1 : ∀ n, 1 ≤ r n := fun n => by
      by_cases hn : n = 0
      · simp only [hn, pow_zero, r]
        have : p.rank (1 : S) = 1 := by
          have h : (1 : S) = ((1 : ℕ) : S) := by simp
          rw [h, p.rank_natCast]
        simp [this]
      · exact Nat.one_le_cast.mpr (p.one_le_rank_pow_of_one_le ha n (Nat.pos_of_ne_zero hn))
    have hr_submult : ∀ n m, r (n + m) ≤ r n * r m := fun n m => by
      simp only [r]
      have h := p.rank_mul_le (a ^ n) (a ^ m)
      rw [← pow_add] at h
      calc (p.rank (a ^ (n + m)) : ℝ) ≤ (p.rank (a ^ n) * p.rank (a ^ m) : ℕ) :=
            Nat.cast_le.mpr h
        _ = (p.rank (a ^ n) : ℝ) * (p.rank (a ^ m) : ℝ) := by push_cast; ring
    -- Step 3: Verify Fekete conditions for subrank (supermultiplicative, ≥ 1, bounded)
    have hs_ge1 : ∀ n, 1 ≤ s n := fun n => by
      by_cases hn : n = 0
      · simp only [hn, pow_zero, s]
        have : p.subrank (1 : S) = 1 := by
          have h : (1 : S) = ((1 : ℕ) : S) := by simp
          rw [h, p.subrank_natCast']
        simp [this]
      · exact Nat.one_le_cast.mpr (p.one_le_subrank_pow_of_one_le ha n (Nat.pos_of_ne_zero hn))
    have hs_supermult : ∀ n m, s n * s m ≤ s (n + m) := fun n m => by
      simp only [s]
      have h := p.le_subrank_mul (a ^ n) (a ^ m)
      rw [← pow_add] at h
      calc (p.subrank (a ^ n) : ℝ) * (p.subrank (a ^ m) : ℝ)
          = ((p.subrank (a ^ n) * p.subrank (a ^ m) : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (p.subrank (a ^ (n + m)) : ℝ) := Nat.cast_le.mpr h
    have hs_bdd : ∀ n, s n ≤ (p.rank a : ℝ) ^ n := fun n => by
      simp only [s]
      calc (p.subrank (a ^ n) : ℝ) ≤ (p.rank (a ^ n) : ℝ) :=
            Nat.cast_le.mpr (p.subrank_le_rank _)
        _ ≤ ((p.rank a ^ n : ℕ) : ℝ) := Nat.cast_le.mpr (p.rank_pow_le a n)
        _ = (p.rank a : ℝ) ^ n := by push_cast; ring
    -- Step 4: Apply Fekete
    have hfek_r := fekete_multiplicative hr_ge1 hr_submult
    have hM : 1 ≤ (p.rank a : ℝ) := by
      have h := p.one_le_rank_pow_of_one_le ha 1 Nat.one_pos
      simp only [pow_one] at h
      exact Nat.one_le_cast.mpr h
    have hfek_s := fekete_supermultiplicative hs_ge1 hs_supermult (p.rank a : ℝ) hM hs_bdd
    -- Step 5: The sets in Fekete match our asympRankSet/asympSubrankSet
    -- Step 6: Use limit comparison: s^{1/n} ≤ r^{1/n} pointwise, so lim s^{1/n} ≤ lim r^{1/n}
    have hpointwise : ∀ n, 0 < n → s n ^ (1 / (n : ℝ)) ≤ r n ^ (1 / (n : ℝ)) := fun n hn => by
      apply Real.rpow_le_rpow (le_of_lt (by linarith [hs_ge1 n] : 0 < s n))
      · exact Nat.cast_le.mpr (p.subrank_le_rank _)
      · exact div_nonneg (by norm_num) (Nat.cast_nonneg n)
    -- By Filter.Tendsto and the pointwise inequality, limits satisfy the same inequality
    have hlim_le : sSup ((fun n => s n ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n}) ≤
                   sInf ((fun n => r n ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n}) := by
      -- Both limits exist by Fekete
      -- s^{1/n} → sSup, r^{1/n} → sInf
      -- s^{1/n} ≤ r^{1/n} pointwise, so sSup ≤ sInf by limit comparison
      apply le_of_tendsto_of_tendsto hfek_s hfek_r
      · filter_upwards [Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩] with n hn
        exact hpointwise n hn
    -- Convert to our definitions
    unfold asympSubrank asympRank asympSubrankSet asympRankSet
    convert hlim_le using 2

/-! ### Fekete's Lemma: Asymptotic Rank/Subrank as Limits

The following theorems establish that asympRank and asympSubrank can be expressed
either as inf/sup or as limits, using Fekete's lemma. -/

/-- Asymptotic rank equals the limit of rank(a^n)^{1/n}, by Fekete's lemma.
    Requires rank(a^n) ≥ 1 for all n ≥ 1 (equivalently, 1 ≤_P a). -/
theorem asympRank_eq_tendsto {a : S} (ha : p.rel 1 a) :
    Filter.Tendsto (fun n : ℕ => (p.rank (a ^ n) : ℝ) ^ (1 / (n : ℝ)))
      Filter.atTop (nhds (p.asympRank a)) := by
  -- Define the rank sequence
  let r : ℕ → ℝ := fun n => (p.rank (a ^ n) : ℝ)
  -- Verify Fekete conditions: r_n ≥ 1 and r_{n+m} ≤ r_n * r_m
  have hr_ge1 : ∀ n, 1 ≤ r n := fun n => by
    by_cases hn : n = 0
    · simp only [hn, pow_zero, r]
      have : p.rank (1 : S) = 1 := p.rank_one
      simp [this]
    · exact Nat.one_le_cast.mpr (p.one_le_rank_pow_of_one_le ha n (Nat.pos_of_ne_zero hn))
  have hr_submult : ∀ n m, r (n + m) ≤ r n * r m := fun n m => by
    simp only [r]
    have h := p.rank_mul_le (a ^ n) (a ^ m)
    rw [← pow_add] at h
    calc (p.rank (a ^ (n + m)) : ℝ) ≤ (p.rank (a ^ n) * p.rank (a ^ m) : ℕ) :=
          Nat.cast_le.mpr h
      _ = (p.rank (a ^ n) : ℝ) * (p.rank (a ^ m) : ℝ) := by push_cast; ring
  -- Apply Fekete's multiplicative lemma
  have hfek := fekete_multiplicative hr_ge1 hr_submult
  -- The limit is asympRank by definition
  have heq : sInf ((fun n => r n ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n}) = p.asympRank a := by
    unfold asympRank asympRankSet; rfl
  rw [heq] at hfek
  exact hfek

/-- Asymptotic subrank equals the limit of subrank(a^n)^{1/n}, by Fekete's lemma.
    Requires 1 ≤_P a to ensure subrank(a^n) ≥ 1 and boundedness. -/
theorem asympSubrank_eq_tendsto {a : S} (ha : p.rel 1 a) :
    Filter.Tendsto (fun n : ℕ => (p.subrank (a ^ n) : ℝ) ^ (1 / (n : ℝ)))
      Filter.atTop (nhds (p.asympSubrank a)) := by
  -- Define the subrank sequence
  let s : ℕ → ℝ := fun n => (p.subrank (a ^ n) : ℝ)
  -- Verify Fekete conditions for supermultiplicative sequences
  have hs_ge1 : ∀ n, 1 ≤ s n := fun n => by
    by_cases hn : n = 0
    · simp only [hn, pow_zero, s]
      have : p.subrank (1 : S) = 1 := p.subrank_one
      simp [this]
    · exact Nat.one_le_cast.mpr (p.one_le_subrank_pow_of_one_le ha n (Nat.pos_of_ne_zero hn))
  have hs_supermult : ∀ n m, s n * s m ≤ s (n + m) := fun n m => by
    simp only [s]
    have h := p.le_subrank_mul (a ^ n) (a ^ m)
    rw [← pow_add] at h
    calc (p.subrank (a ^ n) : ℝ) * (p.subrank (a ^ m) : ℝ)
        = ((p.subrank (a ^ n) * p.subrank (a ^ m) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (p.subrank (a ^ (n + m)) : ℝ) := Nat.cast_le.mpr h
  -- Upper bound: subrank(a^n) ≤ rank(a)^n
  have hs_bdd : ∀ n, s n ≤ (p.rank a : ℝ) ^ n := fun n => by
    simp only [s]
    calc (p.subrank (a ^ n) : ℝ) ≤ (p.rank (a ^ n) : ℝ) :=
          Nat.cast_le.mpr (p.subrank_le_rank _)
      _ ≤ ((p.rank a ^ n : ℕ) : ℝ) := Nat.cast_le.mpr (p.rank_pow_le a n)
      _ = (p.rank a : ℝ) ^ n := by push_cast; ring
  have hM : 1 ≤ (p.rank a : ℝ) := by
    have h := p.one_le_rank_pow_of_one_le ha 1 Nat.one_pos
    simp only [pow_one] at h
    exact Nat.one_le_cast.mpr h
  -- Apply Fekete's supermultiplicative lemma
  have hfek := fekete_supermultiplicative hs_ge1 hs_supermult (p.rank a : ℝ) hM hs_bdd
  -- The limit is asympSubrank by definition
  have heq : sSup ((fun n => s n ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n}) = p.asympSubrank a := by
    unfold asympSubrank asympSubrankSet; rfl
  rw [heq] at hfek
  exact hfek

/-- The asymptotic rank is the infimum of rank(a^n)^{1/n}, by definition. -/
theorem asympRank_eq_iInf {a : S} :
    p.asympRank a = sInf (p.asympRankSet a) := rfl

/-- The asymptotic subrank is the supremum of subrank(a^n)^{1/n}, by definition. -/
theorem asympSubrank_eq_iSup {a : S} :
    p.asympSubrank a = sSup (p.asympSubrankSet a) := rfl

end StrassenPreorder

end AsymptoticSpectrumDuality
