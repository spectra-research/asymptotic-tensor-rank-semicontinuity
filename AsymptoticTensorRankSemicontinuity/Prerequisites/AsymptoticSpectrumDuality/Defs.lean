/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.Analysis.Subadditive
import Mathlib.Data.Real.StarOrdered
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Strassen Preorders

This file defines Strassen preorders on commutative semirings, following
Strassen (1988) "The asymptotic spectrum of tensors".

## Main Definitions

* `StrassenPreorder` - A preorder on a semiring compatible with the semiring structure
* `AsympRel` - The asymptotic preorder derived from a Strassen preorder

## References

* Strassen (1988), The asymptotic spectrum of tensors
-/

namespace AsymptoticSpectrumDuality

open scoped NNReal

variable {S : Type*}

/-! ### Strassen Preorders -/

/-- A Strassen preorder on a commutative semiring S (with ℕ ⊆ S via the natural map)
    is a preorder satisfying three conditions:
    1. Compatibility with ℕ: n ≤ m in ℕ iff n ≤ m in S
    2. Monotonicity: a ≤ b and c ≤ d implies a+c ≤ b+d and ac ≤ bd
    3. Archimedean: for all a,b with b ≠ 0, there exists r ∈ ℕ with a ≤ r·b -/
structure StrassenPreorder (S : Type*) [CommSemiring S] where
  /-- The underlying relation -/
  rel : S → S → Prop
  /-- Reflexivity -/
  refl : ∀ a, rel a a
  /-- Transitivity -/
  trans : ∀ a b c, rel a b → rel b c → rel a c
  /-- Zero is least -/
  zero_le : ∀ a, rel 0 a
  /-- Compatibility with natural numbers -/
  nat_compat : ∀ n m : ℕ, n ≤ m ↔ rel (n : S) (m : S)
  /-- Monotonicity under addition -/
  add_mono : ∀ a b s, rel a b → rel (a + s) (b + s)
  /-- Monotonicity under multiplication -/
  mul_mono : ∀ a b s, rel a b → rel (a * s) (b * s)
  /-- Archimedean property -/
  archimedean : ∀ a b, b ≠ 0 → ∃ r : ℕ, rel a (r * b)

namespace StrassenPreorder

variable [CommSemiring S] (p : StrassenPreorder S)

/-- One is positive -/
theorem zero_le_one : p.rel (0 : S) 1 := p.zero_le 1

/-- Addition is monotone in both arguments -/
theorem add_mono_both {a b c d : S} (hab : p.rel a b) (hcd : p.rel c d) :
    p.rel (a + c) (b + d) := by
  have h1 : p.rel (a + c) (b + c) := p.add_mono a b c hab
  have h2 : p.rel (b + c) (b + d) := by
    rw [add_comm b c, add_comm b d]
    exact p.add_mono c d b hcd
  exact p.trans _ _ _ h1 h2

/-- Multiplication is monotone in both arguments -/
theorem mul_mono_both {a b c d : S} (hab : p.rel a b) (hcd : p.rel c d) :
    p.rel (a * c) (b * d) := by
  have h1 : p.rel (a * c) (b * c) := p.mul_mono a b c hab
  have h2 : p.rel (b * c) (b * d) := by
    rw [mul_comm b c, mul_comm b d]
    exact p.mul_mono c d b hcd
  exact p.trans _ _ _ h1 h2

/-- Natural number scalar multiplication is monotone -/
theorem nsmul_mono {a b : S} (n : ℕ) (hab : p.rel a b) : p.rel (n • a) (n • b) := by
  induction n with
  | zero => simp only [zero_smul]; exact p.refl 0
  | succ n ih =>
    simp only [succ_nsmul]
    exact p.add_mono_both ih hab

/-- Power is monotone -/
theorem pow_mono {a b : S} (n : ℕ) (hab : p.rel a b) : p.rel (a ^ n) (b ^ n) := by
  induction n with
  | zero => simp only [pow_zero]; exact p.refl 1
  | succ n ih =>
    simp only [pow_succ]
    exact p.mul_mono_both ih hab

/-- One is not less than or equal to zero -/
theorem not_rel_one_zero : ¬ p.rel 1 0 := by
  intro h
  have hnat : (1 : ℕ) ≤ 0 := (p.nat_compat 1 0).mpr (by simp only [Nat.cast_one, Nat.cast_zero, h])
  omega

end StrassenPreorder

/-! ### Asymptotic Preorder -/

/-- The asymptotic relation: a ≲ b if there exists a sequence (xₙ) with
    inf_{n≥1} xₙ^(1/n) = 1 such that aⁿ ≤ bⁿ · xₙ for all n ≥ 1.

    Following Strassen (1988). By Fekete's lemma, for submultiplicative sequences
    (x_{n+m} ≤ x_n · x_m), we have inf = lim. The witnesses are submultiplicative
    since a^{n+m} ≤ b^{n+m} · x_n · x_m follows from the individual bounds. -/
def AsympRel [CommSemiring S] (p : StrassenPreorder S) (a b : S) : Prop :=
  ∃ x : ℕ → ℕ, (∀ n, n ≥ 1 → p.rel (a ^ n) ((b ^ n) * (x n))) ∧
    sInf ((fun n => (x n : ℝ) ^ (1 / n : ℝ)) '' {n : ℕ | 1 ≤ n}) = 1

namespace AsympRel

variable [CommSemiring S] {p : StrassenPreorder S}

/-- The asymptotic relation is reflexive -/
theorem refl (a : S) : AsympRel p a a := by
  use fun _ => 1
  constructor
  · intro n _
    simp only [Nat.cast_one, mul_one]
    exact p.refl _
  · -- sInf of constant 1 sequence is 1
    have himg : (fun n : ℕ => ((1 : ℕ) : ℝ) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n} = {1} := by
      ext x
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨n, _, rfl⟩
        simp only [Nat.cast_one, Real.one_rpow]
      · intro hx
        exact ⟨1, Nat.le_refl 1, by simp [hx]⟩
    rw [himg]
    exact csInf_singleton 1

/-- If a ≤ b then a ≲ b -/
theorem of_le {a b : S} (hab : p.rel a b) : AsympRel p a b := by
  use fun _ => 1
  constructor
  · intro n _
    simp only [Nat.cast_one, mul_one]
    exact p.pow_mono n hab
  · -- sInf of constant 1 sequence is 1
    have himg : (fun n : ℕ => ((1 : ℕ) : ℝ) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n} = {1} := by
      ext x
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨n, _, rfl⟩
        simp only [Nat.cast_one, Real.one_rpow]
      · intro hx
        exact ⟨1, Nat.le_refl 1, by simp [hx]⟩
    rw [himg]
    exact csInf_singleton 1

end AsympRel

/-- If `x_n^{1/n} → 1` then `(x_n + 1)^{1/n} → 1`. The `+1` term is asymptotically
negligible at the `1/n` scale: `(x_n + 1)^{1/n}` is squeezed between `1` and
`(2 x_n)^{1/n} = 2^{1/n} · x_n^{1/n} → 1`. -/
theorem tendsto_succ_rpow_div_of_tendsto (x : ℕ → ℕ)
    (hx_tendsto : Filter.Tendsto (fun n => (x n : ℝ) ^ (1 / (n : ℝ))) Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun n => ((x n + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ))) Filter.atTop (nhds 1) := by
  rw [Metric.tendsto_atTop] at hx_tendsto ⊢
  intro ε hε
  set δ := min (ε / 4) 1 with hδ_def
  have hδ_pos : 0 < δ := lt_min (by linarith) one_pos
  have hδ_le1 : δ ≤ 1 := min_le_right _ _
  have hδ_le_ε4 : δ ≤ ε / 4 := min_le_left _ _
  obtain ⟨N₁, hN₁⟩ := hx_tendsto δ hδ_pos
  have h2 : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ (1 / (n : ℝ))) Filter.atTop (nhds 1) := by
    have hinv : Filter.Tendsto (fun n : ℕ => (1 / (n : ℝ))) Filter.atTop (nhds 0) := by
      simp only [one_div]
      exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hcont : Continuous (fun y : ℝ => (2 : ℝ) ^ y) :=
      Real.continuous_const_rpow (by norm_num)
    have h0 : (2 : ℝ) ^ (0 : ℝ) = 1 := Real.rpow_zero 2
    have htend0 : Filter.Tendsto (fun y : ℝ => (2 : ℝ) ^ y) (nhds 0) (nhds 1) := by
      rw [← h0]; exact hcont.continuousAt.tendsto
    exact htend0.comp hinv
  rw [Metric.tendsto_atTop] at h2
  obtain ⟨N₂, hN₂⟩ := h2 δ hδ_pos
  use max (max N₁ N₂) 1
  intro n hn
  have hn_ge1 : 1 ≤ n := le_of_max_le_right hn
  have hn_ge_N1 : N₁ ≤ n := le_trans (le_max_left _ _) (le_of_max_le_left hn)
  have hn_ge_N2 : N₂ ≤ n := le_trans (le_max_right _ _) (le_of_max_le_left hn)
  have hn_pos : (0 : ℝ) < n :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn_ge1))
  have hxn_dist := hN₁ n hn_ge_N1
  have h2n_dist := hN₂ n hn_ge_N2
  rw [Real.dist_eq] at hxn_dist h2n_dist ⊢
  by_cases hxn0 : x n = 0
  · simp only [hxn0, zero_add, Nat.cast_one, Real.one_rpow, sub_self, abs_zero]
    exact hε
  · have hxn_ge1 : 1 ≤ x n := Nat.one_le_iff_ne_zero.mpr hxn0
    have h2_bound : (2 : ℝ) ^ (1 / (n : ℝ)) < 1 + δ := by linarith [(abs_lt.mp h2n_dist).2]
    have hxn_upper : (x n : ℝ) ^ (1 / (n : ℝ)) < 1 + δ := by linarith [(abs_lt.mp hxn_dist).2]
    have hxn_lower : 1 - δ < (x n : ℝ) ^ (1 / (n : ℝ)) := by linarith [(abs_lt.mp hxn_dist).1]
    have hupper : ((x n + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ)) ≤
        (2 : ℝ) ^ (1 / (n : ℝ)) * (x n : ℝ) ^ (1 / (n : ℝ)) := by
      have h1 : ((x n + 1 : ℕ) : ℝ) ≤ 2 * (x n : ℕ) := by
        simp only [Nat.cast_add, Nat.cast_one]
        have : (x n : ℝ) ≥ 1 := Nat.one_le_cast.mpr hxn_ge1
        linarith
      calc ((x n + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ))
          ≤ (2 * (x n : ℝ)) ^ (1 / (n : ℝ)) := by
              apply Real.rpow_le_rpow (Nat.cast_nonneg _) h1
              exact div_nonneg (by norm_num) (le_of_lt hn_pos)
        _ = (2 : ℝ) ^ (1 / (n : ℝ)) * (x n : ℝ) ^ (1 / (n : ℝ)) := by
              rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg _)]
    have hlower : ((x n + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ)) ≥ (x n : ℝ) ^ (1 / (n : ℝ)) := by
      apply Real.rpow_le_rpow (Nat.cast_nonneg _)
      · simp only [Nat.cast_add, Nat.cast_one]; linarith
      · exact div_nonneg (by norm_num) (le_of_lt hn_pos)
    have h2_pos : 0 < (2 : ℝ) ^ (1 / (n : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have hxn_pos : 0 < (x n : ℝ) ^ (1 / (n : ℝ)) :=
      Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hxn0)) _
    have hprod_upper : (2 : ℝ) ^ (1 / (n : ℝ)) * (x n : ℝ) ^ (1 / (n : ℝ)) < 1 + ε := by
      have hprod_sq : (2 : ℝ) ^ (1 / (n : ℝ)) * (x n : ℝ) ^ (1 / (n : ℝ)) < (1 + δ) ^ 2 := by
        calc (2 : ℝ) ^ (1 / (n : ℝ)) * (x n : ℝ) ^ (1 / (n : ℝ))
            < (1 + δ) * (1 + δ) := by
                apply mul_lt_mul h2_bound (le_of_lt hxn_upper) hxn_pos (by linarith)
          _ = (1 + δ) ^ 2 := by ring
      have hsq_bound : (1 + δ) ^ 2 ≤ 1 + ε := by
        have hδ2 : δ ^ 2 ≤ δ := by nlinarith
        calc (1 + δ) ^ 2 = 1 + 2 * δ + δ ^ 2 := by ring
          _ ≤ 1 + 2 * δ + δ := by linarith
          _ = 1 + 3 * δ := by ring
          _ ≤ 1 + 3 * (ε / 4) := by linarith
          _ ≤ 1 + ε := by linarith
      linarith
    rw [abs_lt]
    refine ⟨?_, ?_⟩
    · calc -ε < -δ := by linarith
        _ < (x n : ℝ) ^ (1 / (n : ℝ)) - 1 := by linarith
        _ ≤ ((x n + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ)) - 1 := by linarith [hlower]
    · calc ((x n + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ)) - 1
          ≤ (2 : ℝ) ^ (1 / (n : ℝ)) * (x n : ℝ) ^ (1 / (n : ℝ)) - 1 := by linarith [hupper]
        _ < ε := by linarith [hprod_upper]

/-! ### Submultiplicative Closure -/

/-- The submultiplicative closure of x : ℕ → ℕ.
    For n ≥ 1: y_n = min over all compositions k₁+...+kₘ=n of ∏ x_{kᵢ}.
    Defined recursively: y_n = min(x_n, min_{1≤k<n} y_k * y_{n-k}).

    Key properties (proved below):
    - y is submultiplicative: y_{n+m} ≤ y_n * y_m
    - y ≤ x pointwise: y_n ≤ x_n
    - If p.rel (a^n) (b^n * x_n), then p.rel (a^n) (b^n * y_n) -/
def submultClosure (x : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => x 1
  | n + 2 =>
    -- For n+2, compute min of x(n+2) and min over k=1,...,n+1 of y_k * y_{n+2-k}
    -- Use Fin to carry the bound k < n+1
    min (x (n + 2))
      ((Finset.univ : Finset (Fin (n + 1))).inf'
        ⟨⟨0, Nat.zero_lt_succ n⟩, Finset.mem_univ _⟩
        (fun k : Fin (n + 1) =>
          submultClosure x (k.val + 1) * submultClosure x (n + 1 - k.val)))
  termination_by n => n
  decreasing_by all_goals omega

@[simp] theorem submultClosure_zero (x : ℕ → ℕ) : submultClosure x 0 = 1 := by
  unfold submultClosure; rfl
@[simp] theorem submultClosure_one (x : ℕ → ℕ) : submultClosure x 1 = x 1 := by
  unfold submultClosure; rfl

/-- Helper: The inf' in submultClosure x 2 equals x 1 * x 1 -/
private theorem submultClosure_two_inf' (x : ℕ → ℕ) :
    (Finset.univ : Finset (Fin 1)).inf' ⟨⟨0, Nat.zero_lt_one⟩, Finset.mem_univ _⟩
      (fun k : Fin 1 => submultClosure x (k.val + 1) * submultClosure x (1 - k.val)) =
      x 1 * x 1 := by
  -- Fin 1 has exactly one element: 0
  have huniv : (Finset.univ : Finset (Fin 1)) = {⟨0, Nat.zero_lt_one⟩} := by
    ext ⟨i, hi⟩
    simp only [Finset.mem_univ, Finset.mem_singleton, Fin.mk.injEq, true_iff]
    omega
  simp only [huniv, Finset.inf'_singleton, zero_add, Nat.sub_zero, submultClosure_one]

/-- The submultiplicative closure is submultiplicative -/
theorem submultClosure_submult (x : ℕ → ℕ) :
    ∀ n m, n ≥ 1 → m ≥ 1 → submultClosure x (n + m) ≤ submultClosure x n * submultClosure x m := by
  intro n m hn hm
  -- The key: submultClosure x n * submultClosure x m is one of the candidates in the min
  -- when computing submultClosure x (n+m). The partition at index k = n-1 gives this product.
  -- Case split on n and m to handle the definition's structure
  match n, m with
  | 1, 1 =>
    -- submultClosure x 2 = min(x 2, x 1 * x 1)
    -- submultClosure x 1 * submultClosure x 1 = x 1 * x 1
    simp only [submultClosure_one]
    conv_lhs => unfold submultClosure
    rw [submultClosure_two_inf']
    exact min_le_right (x 2) (x 1 * x 1)
  | 1, m + 2 =>
    -- submultClosure x (m+3) = min(x(m+3), inf'_{Fin(m+2)} f)
    -- At k=0: submultClosure x 1 * submultClosure x (m+2)
    have hLHS : submultClosure x (1 + (m + 2)) = submultClosure x (m + 3) := by ring_nf
    simp only [hLHS, submultClosure_one]
    conv_lhs => unfold submultClosure
    apply le_trans (min_le_right _ _)
    have hmem : (⟨0, Nat.zero_lt_succ (m + 1)⟩ : Fin (m + 2)) ∈ Finset.univ := Finset.mem_univ _
    have hle := Finset.inf'_le (s := Finset.univ) (f :=
      fun k : Fin (m + 2) => submultClosure x (k.val + 1) *
        submultClosure x (m + 1 + 1 - k.val)) hmem
    simp only [show (m + 1 + 1 : ℕ) - 0 = m + 2 from by omega, zero_add, submultClosure_one] at hle
    exact hle
  | n + 2, 1 =>
    -- submultClosure x (n+3) = min(x(n+3), inf'_{Fin(n+2)} f)
    -- At k=n+1: submultClosure x (n+2) * submultClosure x 1
    have hLHS : submultClosure x (n + 2 + 1) = submultClosure x (n + 3) := by ring_nf
    simp only [hLHS, submultClosure_one, mul_comm]
    conv_lhs => unfold submultClosure
    apply le_trans (min_le_right _ _)
    -- The definition unfolds to Fin (n + 2) with indices (k + 1) and (n + 1 + 1 - k)
    -- At k = n + 1: get submultClosure x (n + 2) * submultClosure x 1
    have hmem : (⟨n + 1, by omega⟩ : Fin (n + 2)) ∈ Finset.univ := Finset.mem_univ _
    have hle := Finset.inf'_le (s := Finset.univ) (f :=
      fun k : Fin (n + 2) => submultClosure x (k.val + 1) *
        submultClosure x (n + 1 + 1 - k.val)) hmem
    simp only [show n + 1 + 1 - (n + 1) = 1 from by omega, submultClosure_one,
      show (n + 1 : ℕ) + 1 = n + 2 from by omega] at hle
    calc (Finset.univ.inf' _ fun k : Fin (n + 2) =>
            submultClosure x (k.val + 1) * submultClosure x (n + 1 + 1 - k.val))
        ≤ submultClosure x (n + 2) * x 1 := hle
      _ = x 1 * submultClosure x (n + 2) := mul_comm _ _
  | n + 2, m + 2 =>
    -- submultClosure x (n+m+4) = min(x(n+m+4), inf'_{Fin(n+m+3)} f)
    -- At k=n+1: submultClosure x (n+2) * submultClosure x (m+2)
    have hLHS : submultClosure x (n + 2 + (m + 2)) = submultClosure x (n + m + 4) := by ring_nf
    rw [hLHS]
    conv_lhs => unfold submultClosure
    apply le_trans (min_le_right _ _)
    have hk : n + 1 < n + m + 3 := by omega
    have hmem : (⟨n + 1, hk⟩ : Fin (n + m + 3)) ∈ Finset.univ := Finset.mem_univ _
    have hle := Finset.inf'_le (s := Finset.univ) (f :=
      fun k : Fin (n + m + 3) => submultClosure x (k.val + 1) *
        submultClosure x (n + m + 2 + 1 - k.val)) hmem
    simp only [show (n + 1 : ℕ) + 1 = n + 2 from by omega,
      show n + m + 2 + 1 - (n + 1) = m + 2 from by omega] at hle
    exact hle

/-- The submultiplicative closure is at most x -/
theorem submultClosure_le (x : ℕ → ℕ) : ∀ n, n ≥ 1 → submultClosure x n ≤ x n := by
  intro n hn
  match n with
  | 1 => simp only [submultClosure_one, le_refl]
  | n + 2 =>
    -- submultClosure x (n+2) = min(x(n+2), ...)
    unfold submultClosure
    exact min_le_left _ _

/-- The bound holds for submultiplicative closure when it holds for x -/
theorem submultClosure_bound [CommSemiring S] (p : StrassenPreorder S) (a b : S) (x : ℕ → ℕ)
    (hx_rel : ∀ n, n ≥ 1 → p.rel (a ^ n) (b ^ n * x n)) :
    ∀ n, n ≥ 1 → p.rel (a ^ n) (b ^ n * submultClosure x n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    match n with
    | 1 =>
      -- submultClosure x 1 = x 1
      simp only [submultClosure_one]
      exact hx_rel 1 hn
    | n + 2 =>
      -- submultClosure x (n+2) = min(x(n+2), inf' ...)
      -- Either equals x(n+2) or some product
      unfold submultClosure
      -- The min is ≤ both arguments, so submultClosure x (n+2) ≤ x (n+2)
      -- and submultClosure x (n+2) ≤ some product
      -- We show the bound holds for EACH candidate, so it holds for their min
      -- Since min c₁ c₂ = c₁ or c₂, and we have bounds for both, we're done.
      -- The key: submultClosure ≤ x, so p.rel ... (submultClosure) follows from p.rel ... (x)
      -- via nat_compat and transitivity
      have hsub_le := submultClosure_le x (n + 2) (by omega : n + 2 ≥ 1)
      have hx_bound := hx_rel (n + 2) (by omega : n + 2 ≥ 1)
      -- From hsub_le : submultClosure x (n + 2) ≤ x (n + 2)
      -- Get p.rel (submultClosure x (n + 2)) (x (n + 2))
      have hnat := (p.nat_compat (submultClosure x (n + 2)) (x (n + 2))).mp hsub_le
      -- Get p.rel (b^(n+2) * submultClosure x (n + 2)) (b^(n+2) * x (n + 2))
      have hmul := p.mul_mono _ _ (b ^ (n + 2)) hnat
      simp only [mul_comm] at hmul
      -- Now chain: a^(n+2) ≤ b^(n+2) * x(n+2) ≤ ... wait, wrong direction
      -- We have: p.rel (b^n * submultClosure) (b^n * x) and p.rel (a^n) (b^n * x)
      -- We need p.rel (a^n) (b^n * submultClosure)
      -- This requires p.rel (b^n * submultClosure) (b^n * x) in the OPPOSITE direction
      -- or we need a different approach

      -- CORRECT APPROACH: submultClosure x (n+2) equals min(x(n+2), inf ...)
      -- Case 1: If min chooses x(n+2), use hx_rel directly (but rewriting submultClosure)
      -- Case 2: If min chooses inf ..., use induction on the product

      -- Since we can't case split on which min is taken, we use that
      -- submultClosure ≤ x means the bound for x implies the bound for submultClosure
      -- Hmm, but that's still the wrong direction.

      -- Actually, we need to prove this by induction on the structure,
      -- showing each candidate satisfies the bound, and the closure is one of them.
      -- The key lemma is: if p.rel a c for all candidates c, and y = min of candidates,
      -- then y is one of the candidates, so p.rel a y.

      -- Let's use that min a b ∈ {a, b}, and show the bound for each:
      by_cases hcase : x (n + 2) ≤ (Finset.univ.inf' ⟨⟨0, Nat.zero_lt_succ n⟩, Finset.mem_univ _⟩
        (fun k : Fin (n + 1) => submultClosure x (k.val + 1) * submultClosure x (n + 1 - k.val)))
      · -- Case: min = x (n + 2)
        simp only [min_eq_left hcase]
        exact hx_rel (n + 2) (by omega)
      · -- Case: min = inf' ...
        push_neg at hcase
        simp only [min_eq_right (le_of_lt hcase)]
        -- The inf' is achieved at some k₀
        have hnonempty : (Finset.univ : Finset (Fin (n + 1))).Nonempty :=
          ⟨⟨0, Nat.zero_lt_succ n⟩, Finset.mem_univ _⟩
        obtain ⟨k, _, hk_eq⟩ := Finset.exists_mem_eq_inf' hnonempty
          (fun k : Fin (n + 1) => submultClosure x (k.val + 1) * submultClosure x (n + 1 - k.val))
        -- Rewrite using hk_eq - the nonempty proofs are proof-irrelevant
        suffices h : p.rel (a ^ (n + 2)) (b ^ (n + 2) *
            ↑(submultClosure x (k.val + 1) * submultClosure x (n + 1 - k.val))) by
          convert h using 2
          simp only [← hk_eq]
        -- Need: p.rel (a ^ (n+2)) (b ^ (n+2) * (submultClosure x (k+1) * submultClosure x (n+1-k)))
        have hk1 : k.val + 1 ≥ 1 := by omega
        have hk2 : n + 1 - k.val ≥ 1 := by omega
        have hk1_lt : k.val + 1 < n + 2 := by omega
        have hk2_lt : n + 1 - k.val < n + 2 := by omega
        have h1 := ih (k.val + 1) hk1_lt hk1
        have h2 := ih (n + 1 - k.val) hk2_lt hk2
        -- h1: p.rel (a ^ (k+1)) (b ^ (k+1) * submultClosure x (k+1))
        -- h2: p.rel (a ^ (n+1-k)) (b ^ (n+1-k) * submultClosure x (n+1-k))
        -- Multiply: p.rel (a^(n+2)) (b^(n+2) * sc(k+1) * sc(n+1-k))
        have hmul1 := p.mul_mono _ _ (a ^ (n + 1 - k.val)) h1
        have hmul2 := p.mul_mono _ _ (b ^ (k.val + 1) * ↑(submultClosure x (k.val + 1))) h2
        -- hmul1: p.rel (a^(k+1) * a^(n+1-k)) ((b^(k+1) * sc(k+1)) * a^(n+1-k))
        -- hmul2: p.rel (a^(n+1-k) * (b^(k+1) * sc(k+1)))
        --              ((b^(n+1-k) * sc(n+1-k)) * (b^(k+1) * sc(k+1)))
        -- The RHS of hmul1 is (b^(k+1) * sc(k+1)) * a^(n+1-k)
        -- The LHS of hmul2 is a^(n+1-k) * (b^(k+1) * sc(k+1))
        -- These are equal by commutativity
        have heq_mid : b ^ (k.val + 1) * ↑(submultClosure x (k.val + 1)) * a ^ (n + 1 - k.val) =
            a ^ (n + 1 - k.val) * (b ^ (k.val + 1) * ↑(submultClosure x (k.val + 1))) := by ring
        have hchain := p.trans _ _ _ hmul1 (heq_mid ▸ hmul2)
        -- hchain: p.rel (a^(k+1) * a^(n+1-k)) ((b^(n+1-k) * sc(n+1-k)) * (b^(k+1) * sc(k+1)))
        -- Simplify to get b^(n+2) * (sc(k+1) * sc(n+1-k))
        have heq_lhs : a ^ (n + 2) = a ^ (k.val + 1) * a ^ (n + 1 - k.val) := by
          rw [← pow_add]; congr 1; omega
        have heq_rhs : b ^ (n + 1 - k.val) * ↑(submultClosure x (n + 1 - k.val)) *
            (b ^ (k.val + 1) * ↑(submultClosure x (k.val + 1))) =
            b ^ (n + 2) *
              (↑(submultClosure x (k.val + 1)) * ↑(submultClosure x (n + 1 - k.val))) := by
          have hpow : b ^ (n + 1 - k.val) * b ^ (k.val + 1) = b ^ (n + 2) := by
            rw [← pow_add]; congr 1; omega
          calc b ^ (n + 1 - k.val) * ↑(submultClosure x (n + 1 - k.val)) *
                  (b ^ (k.val + 1) * ↑(submultClosure x (k.val + 1)))
              = b ^ (n + 1 - k.val) * b ^ (k.val + 1) *
                  (↑(submultClosure x (n + 1 - k.val)) *
                   ↑(submultClosure x (k.val + 1))) := by ring
            _ = b ^ (n + 2) * (↑(submultClosure x (n + 1 - k.val)) *
                  ↑(submultClosure x (k.val + 1))) := by rw [hpow]
            _ = b ^ (n + 2) * (↑(submultClosure x (k.val + 1)) *
                  ↑(submultClosure x (n + 1 - k.val))) := by ring
        simp only [Nat.cast_mul]
        rw [heq_lhs, ← heq_rhs]
        exact hchain

/-- If x_n ≥ 1 for n ≥ 1, then submultClosure x_n ≥ 1 -/
theorem submultClosure_ge_one (x : ℕ → ℕ) (hx : ∀ n, n ≥ 1 → x n ≥ 1) :
    ∀ n, n ≥ 1 → submultClosure x n ≥ 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    match n with
    | 1 => simp only [submultClosure_one]; exact hx 1 (le_refl 1)
    | n + 2 =>
      unfold submultClosure
      apply le_min
      · exact hx (n + 2) (by omega)
      · apply Finset.le_inf'
        intro k _
        have h1 : k.val + 1 ≥ 1 := by omega
        have h2 : n + 1 - k.val ≥ 1 := by omega
        have hk1 : k.val + 1 < n + 2 := by omega
        have hk2 : n + 1 - k.val < n + 2 := by omega
        exact one_le_mul (ih (k.val + 1) hk1 h1) (ih (n + 1 - k.val) hk2 h2)

/-- sInf of submultClosure ≤ sInf of x (since submultClosure ≤ x pointwise) -/
theorem submultClosure_sInf_le (x : ℕ → ℕ) (hx_ge1 : ∀ n, n ≥ 1 → x n ≥ 1) :
    sInf ((fun n => (submultClosure x n : ℝ) ^ (1 / n : ℝ)) '' {n : ℕ | 1 ≤ n}) ≤
    sInf ((fun n => (x n : ℝ) ^ (1 / n : ℝ)) '' {n : ℕ | 1 ≤ n}) := by
  let S := (fun n => (submultClosure x n : ℝ) ^ (1 / n : ℝ)) '' {n : ℕ | 1 ≤ n}
  let T := (fun n => (x n : ℝ) ^ (1 / n : ℝ)) '' {n : ℕ | 1 ≤ n}
  have hS_ne : S.Nonempty := ⟨_, 1, le_refl 1, rfl⟩
  have hT_ne : T.Nonempty := ⟨_, 1, le_refl 1, rfl⟩
  have hS_bdd : BddBelow S := by
    use 1
    intro z hz
    simp only [Set.mem_image, Set.mem_setOf_eq, S] at hz
    obtain ⟨n, hn, rfl⟩ := hz
    have := submultClosure_ge_one x hx_ge1 n hn
    have hn_pos : (0 : ℝ) < n :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn))
    calc 1 = 1 ^ (1 / (n : ℝ)) := by simp
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) (Nat.one_le_cast.mpr this)
                (div_nonneg (by norm_num) (le_of_lt hn_pos))
  apply le_csInf hT_ne
  intro t ht
  simp only [Set.mem_image, Set.mem_setOf_eq, T] at ht
  obtain ⟨n, hn, rfl⟩ := ht
  have hs : (submultClosure x n : ℝ) ^ (1 / n : ℝ) ∈ S := ⟨n, hn, rfl⟩
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn))
  calc sInf S ≤ (submultClosure x n : ℝ) ^ (1 / n : ℝ) := csInf_le hS_bdd hs
    _ ≤ (x n : ℝ) ^ (1 / n : ℝ) := Real.rpow_le_rpow (Nat.cast_nonneg _)
        (Nat.cast_le.mpr (submultClosure_le x n hn)) (div_nonneg (by norm_num) (le_of_lt hn_pos))

/-- Both infima are ≥ 1 (since values are ≥ 1) -/
theorem submultClosure_sInf_ge_one (x : ℕ → ℕ) (hx_ge1 : ∀ n, n ≥ 1 → x n ≥ 1) :
    1 ≤ sInf ((fun n => (submultClosure x n : ℝ) ^ (1 / n : ℝ)) '' {n : ℕ | 1 ≤ n}) := by
  have hne : ((fun n => (submultClosure x n : ℝ) ^ (1 / n : ℝ)) '' {n : ℕ | 1 ≤ n}).Nonempty :=
    ⟨_, 1, le_refl 1, rfl⟩
  apply le_csInf hne
  intro z hz
  simp only [Set.mem_image, Set.mem_setOf_eq] at hz
  obtain ⟨n, hn, rfl⟩ := hz
  have := submultClosure_ge_one x hx_ge1 n hn
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn))
  calc 1 = 1 ^ (1 / (n : ℝ)) := by simp
    _ ≤ _ := Real.rpow_le_rpow (by norm_num) (Nat.one_le_cast.mpr this)
              (div_nonneg (by norm_num) (le_of_lt hn_pos))

theorem x_sInf_ge_one (x : ℕ → ℕ) (hx_ge1 : ∀ n, n ≥ 1 → x n ≥ 1) :
    1 ≤ sInf ((fun n => (x n : ℝ) ^ (1 / n : ℝ)) '' {n : ℕ | 1 ≤ n}) := by
  have hne : ((fun n => (x n : ℝ) ^ (1 / n : ℝ)) '' {n : ℕ | 1 ≤ n}).Nonempty :=
    ⟨_, 1, le_refl 1, rfl⟩
  apply le_csInf hne
  intro z hz
  simp only [Set.mem_image, Set.mem_setOf_eq] at hz
  obtain ⟨n, hn, rfl⟩ := hz
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn))
  calc 1 = 1 ^ (1 / (n : ℝ)) := by simp
    _ ≤ _ := Real.rpow_le_rpow (by norm_num) (Nat.one_le_cast.mpr (hx_ge1 n hn))
              (div_nonneg (by norm_num) (le_of_lt hn_pos))

/-- The key implication: sInf of x = 1 implies sInf of submultClosure = 1 -/
theorem submultClosure_sInf_eq_one_of (x : ℕ → ℕ) (hx_ge1 : ∀ n, n ≥ 1 → x n ≥ 1)
    (h : sInf ((fun n => (x n : ℝ) ^ (1 / n : ℝ)) '' {n : ℕ | 1 ≤ n}) = 1) :
    sInf ((fun n => (submultClosure x n : ℝ) ^ (1 / n : ℝ)) '' {n : ℕ | 1 ≤ n}) = 1 := by
  -- 1 ≤ sInf submult ≤ sInf x = 1, so sInf submult = 1
  have hle := submultClosure_sInf_le x hx_ge1
  have hge := submultClosure_sInf_ge_one x hx_ge1
  rw [h] at hle
  exact le_antisymm hle hge


/-! ### Fekete's Lemma and inf = lim equivalence -/

/-- Fekete's lemma (additive form): For subadditive sequences (x_{n+m} ≤ x_n + x_m),
    we have lim_{n→∞} x_n/n = inf_n x_n/n.

    Reference: Fekete (1923), Pólya-Szegő Problem 98. -/
theorem fekete_additive {x : ℕ → ℝ} (hx_nonneg : ∀ n, 0 ≤ x n)
    (hx_subadditive : ∀ n m, x (n + m) ≤ x n + x m) :
    Filter.Tendsto (fun n => x n / n) Filter.atTop
      (nhds (sInf ((fun n => x n / n) '' {n : ℕ | 1 ≤ n}))) := by
  -- Use mathlib's Subadditive.tendsto_lim (Fekete's lemma)
  have hsub : Subadditive x := hx_subadditive
  have hbdd : BddBelow (Set.range fun n => x n / n) := by
    refine ⟨0, fun y hy => ?_⟩
    obtain ⟨n, rfl⟩ := hy
    exact div_nonneg (hx_nonneg n) (Nat.cast_nonneg n)
  have htend := hsub.tendsto_lim hbdd
  -- Subadditive.lim is defined as sInf over Set.Ici 1, which equals our set
  convert htend using 2
  unfold Subadditive.lim
  congr 1

/-- Fekete's lemma (multiplicative form): For submultiplicative sequences (y_{n+m} ≤ y_n · y_m)
    with y_n ≥ 1, we have lim_{n→∞} y_n^{1/n} = inf_n y_n^{1/n}. -/
theorem fekete_multiplicative {y : ℕ → ℝ} (hy_ge1 : ∀ n, 1 ≤ y n)
    (hy_submult : ∀ n m, y (n + m) ≤ y n * y m) :
    Filter.Tendsto (fun n => (y n) ^ (1 / (n : ℝ))) Filter.atTop
      (nhds (sInf ((fun n => (y n) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n}))) := by
  -- Apply additive Fekete to log(y_n)
  set x := fun n => Real.log (y n) with hx_def
  have hx_nonneg : ∀ n, 0 ≤ x n := fun n => Real.log_nonneg (hy_ge1 n)
  have hx_subadditive : ∀ n m, x (n + m) ≤ x n + x m := by
    intro n m
    calc x (n + m) = Real.log (y (n + m)) := rfl
      _ ≤ Real.log (y n * y m) :=
          Real.log_le_log (by linarith [hy_ge1 (n + m)]) (hy_submult n m)
      _ = Real.log (y n) + Real.log (y m) :=
          Real.log_mul (by linarith [hy_ge1 n]) (by linarith [hy_ge1 m])
      _ = x n + x m := rfl
  -- By additive Fekete: lim x_n/n = inf x_n/n
  have hfek := fekete_additive hx_nonneg hx_subadditive
  -- y_n^{1/n} = exp(log(y_n)/n) = exp(x_n/n)
  have heq : ∀ n : ℕ, n ≠ 0 → (y n) ^ (1 / (n : ℝ)) = Real.exp (x n / n) := by
    intro n hn
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hy_pos : 0 < y n := by linarith [hy_ge1 n]
    rw [Real.rpow_def_of_pos hy_pos, one_div, hx_def]
    ring_nf
  -- The infimum also transforms: inf y_n^{1/n} = exp(inf x_n/n)
  have hinf_eq : sInf ((fun n => (y n) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n}) =
                 Real.exp (sInf ((fun n => x n / n) '' {n : ℕ | 1 ≤ n})) := by
    -- Transform the set via exp
    have himg_eq : (fun n => (y n) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n} =
                   Real.exp '' ((fun n => x n / n) '' {n : ℕ | 1 ≤ n}) := by
      ext z
      simp only [Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨n, hn, rfl⟩
        have hn' : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
        exact ⟨x n / n, ⟨n, hn, rfl⟩, (heq n hn').symm⟩
      · rintro ⟨w, ⟨n, hn, rfl⟩, rfl⟩
        have hn' : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
        exact ⟨n, hn, heq n hn'⟩
    rw [himg_eq]
    -- Use monotone + continuous exp preserves sInf
    have hne : ((fun n => x n / n) '' {n : ℕ | 1 ≤ n}).Nonempty := by
      refine ⟨x 1 / 1, 1, le_refl 1, ?_⟩; simp
    have hbdd : BddBelow ((fun n => x n / n) '' {n : ℕ | 1 ≤ n}) := by
      refine ⟨0, fun z hz => ?_⟩
      obtain ⟨n, _, rfl⟩ := hz
      exact div_nonneg (hx_nonneg n) (Nat.cast_nonneg n)
    -- exp maps infimum to infimum for continuous strictly monotone functions on bounded below sets
    apply le_antisymm
    · -- sInf (exp '' S) ≤ exp (sInf S)
      -- Use continuity: exp(sInf) is the limit of exp(elements approaching sInf)
      apply le_of_forall_pos_lt_add
      intro ε hε
      -- By continuity, ∃ δ > 0 such that |exp(x) - exp(sInf)| < ε when |x - sInf| < δ
      have hcont := Real.continuous_exp.continuousAt
          (x := sInf ((fun n => x n / n) '' {n : ℕ | 1 ≤ n}))
      obtain ⟨δ, hδ_pos, hδ_spec⟩ := Metric.continuousAt_iff.mp hcont ε hε
      -- By definition of sInf, ∃ element in set with value < sInf + δ
      have hexists := exists_lt_of_csInf_lt hne (by linarith : sInf _ < sInf _ + δ)
      obtain ⟨w, hw_mem, hw_lt⟩ := hexists
      -- exp(w) is in exp '' S
      have hmem_exp : Real.exp w ∈ Real.exp '' ((fun n => x n / n) '' {n : ℕ | 1 ≤ n}) :=
        Set.mem_image_of_mem _ hw_mem
      -- sInf (exp '' S) ≤ exp(w) < exp(sInf) + ε
      have hbdd_exp : BddBelow (Real.exp '' ((fun n => x n / n) '' {n : ℕ | 1 ≤ n})) := by
        refine ⟨1, fun z hz => ?_⟩
        obtain ⟨v, hv_mem, rfl⟩ := hz
        obtain ⟨n, hn, rfl⟩ := hv_mem
        exact Real.one_le_exp (div_nonneg (hx_nonneg n) (Nat.cast_nonneg n))
      have hw_ge : sInf ((fun n => x n / n) '' {n : ℕ | 1 ≤ n}) ≤ w := csInf_le hbdd hw_mem
      have hdist : dist w (sInf ((fun n => x n / n) '' {n : ℕ | 1 ≤ n})) < δ := by
        simp only [Real.dist_eq, abs_sub_lt_iff]
        constructor <;> linarith
      calc sInf (Real.exp '' ((fun n => x n / n) '' {n : ℕ | 1 ≤ n})) ≤ Real.exp w :=
            csInf_le hbdd_exp hmem_exp
        _ < Real.exp (sInf ((fun n => x n / n) '' {n : ℕ | 1 ≤ n})) + ε := by
            have := hδ_spec hdist
            simp only [Real.dist_eq] at this
            linarith [abs_lt.mp this]
    · -- exp (sInf S) ≤ sInf (exp '' S)
      apply le_csInf
      · exact hne.image _
      · intro z hz
        obtain ⟨w, hw, rfl⟩ := hz
        exact Real.exp_le_exp.mpr (csInf_le hbdd hw)
  -- Combine: exp is continuous, so Tendsto exp ∘ (x/n) = Tendsto y^{1/n}
  rw [hinf_eq]
  have htend_exp : Filter.Tendsto (fun n => Real.exp (x n / n)) Filter.atTop
      (nhds (Real.exp (sInf ((fun n => x n / n) '' {n : ℕ | 1 ≤ n})))) := hfek.rexp
  -- Need to show the composed function matches
  refine Filter.Tendsto.congr' ?_ htend_exp
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨{n : ℕ | 1 ≤ n}, ?_, ?_⟩
  · exact Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩
  · intro n hn
    exact (heq n (Nat.one_le_iff_ne_zero.mp hn)).symm

/-- Fekete's lemma (supermultiplicative form): For supermultiplicative sequences
    (y_{n+m} ≥ y_n · y_m) with 1 ≤ y_n ≤ M^n for some M,
    we have lim_{n→∞} y_n^{1/n} = sup_n y_n^{1/n}.

    The upper bound y_n ≤ M^n is needed since supermult gives lower bounds, not upper.
    In applications, this comes from subrank(a^n) ≤ rank(a^n) ≤ rank(a)^n.

    Proof: Apply Fekete to r_n = n*log(M) - log(y_n), which is subadditive and nonneg. -/
theorem fekete_supermultiplicative {y : ℕ → ℝ} (hy_ge1 : ∀ n, 1 ≤ y n)
    (hy_supermult : ∀ n m, y n * y m ≤ y (n + m))
    (M : ℝ) (hM : 1 ≤ M) (hy_bdd : ∀ n, y n ≤ M ^ n) :
    Filter.Tendsto (fun n => (y n) ^ (1 / (n : ℝ))) Filter.atTop
      (nhds (sSup ((fun n => (y n) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n}))) := by
  -- Define r_n = n*log(M) - log(y_n)
  have hM_pos : 0 < M := by linarith
  set r := fun n : ℕ => (n : ℝ) * Real.log M - Real.log (y n) with hr_def
  -- r is nonnegative since y_n ≤ M^n
  have hr_nonneg : ∀ n, 0 ≤ r n := by
    intro n
    simp only [hr_def, sub_nonneg]
    have hy_pos : 0 < y n := by linarith [hy_ge1 n]
    calc Real.log (y n) ≤ Real.log (M ^ n) := Real.log_le_log hy_pos (hy_bdd n)
      _ = (n : ℝ) * Real.log M := Real.log_pow M n
  -- r is subadditive since y is supermultiplicative
  have hr_subadditive : ∀ n m, r (n + m) ≤ r n + r m := by
    intro n m
    simp only [hr_def, Nat.cast_add]
    have hy_pos_nm : 0 < y n * y m := by
      have h1 : 0 < y n := by linarith [hy_ge1 n]
      have h2 : 0 < y m := by linarith [hy_ge1 m]
      positivity
    have hlog_le : Real.log (y n) + Real.log (y m) ≤ Real.log (y (n + m)) := by
      rw [← Real.log_mul (by linarith [hy_ge1 n]) (by linarith [hy_ge1 m])]
      exact Real.log_le_log hy_pos_nm (hy_supermult n m)
    linarith
  -- Apply additive Fekete: lim r_n/n = inf r_n/n
  have hfek := fekete_additive hr_nonneg hr_subadditive
  -- r_n/n = log(M) - log(y_n)/n, so lim log(y_n)/n = log(M) - inf(r_n/n)
  -- This means lim y_n^{1/n} = exp(log(M) - inf(r_n/n)) = M / exp(inf(r_n/n))
  -- = M * exp(-inf(r_n/n)) = M * exp(sup(-r_n/n)) = sup(M * exp(-r_n/n)) = sup(y_n^{1/n})
  -- The set {y_n^{1/n}} is bounded above by M
  have hset_bdd : BddAbove ((fun n => (y n) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n}) := by
    refine ⟨M, fun z hz => ?_⟩
    obtain ⟨n, hn, rfl⟩ := hz
    have hn' : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn')
    have hy_pos : 0 < y n := by linarith [hy_ge1 n]
    calc (y n) ^ (1 / (n : ℝ)) ≤ (M ^ n) ^ (1 / (n : ℝ)) := by
          apply Real.rpow_le_rpow (le_of_lt hy_pos) (hy_bdd n)
          exact div_nonneg (by norm_num) (le_of_lt hn_pos)
      _ = M := by rw [← Real.rpow_natCast M n, ← Real.rpow_mul (le_of_lt hM_pos),
                      mul_one_div_cancel (ne_of_gt hn_pos), Real.rpow_one]
  -- The set is nonempty
  have hset_ne : ((fun n => (y n) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n}).Nonempty :=
    ⟨y 1, 1, le_refl 1, by simp only [one_div, Nat.cast_one, inv_one, Real.rpow_one]⟩
  -- y_n^{1/n} = exp(log(y_n)/n) for n ≥ 1
  have hy_eq : ∀ n : ℕ, n ≠ 0 → (y n) ^ (1 / (n : ℝ)) = Real.exp (Real.log (y n) / n) := by
    intro n hn
    have hy_pos : 0 < y n := by linarith [hy_ge1 n]
    rw [Real.rpow_def_of_pos hy_pos, one_div, div_eq_mul_inv]
  -- log(y_n)/n = log(M) - r_n/n
  have hlog_eq : ∀ n : ℕ, n ≠ 0 → Real.log (y n) / n = Real.log M - r n / n := by
    intro n hn
    simp only [hr_def]
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    field_simp
    ring
  -- So y_n^{1/n} = exp(log(M) - r_n/n) = M * exp(-r_n/n) / 1 (for n ≥ 1)
  -- Actually, y_n^{1/n} = exp(log(M) - r_n/n)
  have hy_exp_eq : ∀ n : ℕ, n ≠ 0 → (y n) ^ (1 / (n : ℝ)) = Real.exp (Real.log M - r n / n) := by
    intro n hn
    rw [hy_eq n hn, hlog_eq n hn]
  -- sSup {y_n^{1/n}} = exp(sSup {log(M) - r_n/n}) = exp(log(M) - sInf {r_n/n})
  have hsSup_eq : sSup ((fun n => (y n) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n}) =
                  Real.exp (Real.log M - sInf ((fun n => r n / n) '' {n : ℕ | 1 ≤ n})) := by
    -- Transform the set
    have himg_eq : (fun n => (y n) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n} =
                   Real.exp '' ((fun n => Real.log M - r n / n) '' {n : ℕ | 1 ≤ n}) := by
      ext z
      simp only [Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨n, hn, rfl⟩
        have hn' : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
        exact ⟨Real.log M - r n / n, ⟨n, hn, rfl⟩, (hy_exp_eq n hn').symm⟩
      · rintro ⟨w, ⟨n, hn, rfl⟩, rfl⟩
        have hn' : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
        exact ⟨n, hn, hy_exp_eq n hn'⟩
    rw [himg_eq]
    -- {log(M) - r_n/n} = {log(M)} - {r_n/n} in the sense of image under (log(M) - ·)
    have hne_r : ((fun n => r n / n) '' {n : ℕ | 1 ≤ n}).Nonempty := by
      refine ⟨r 1 / 1, 1, le_refl 1, ?_⟩; simp
    have hbdd_r : BddBelow ((fun n => r n / n) '' {n : ℕ | 1 ≤ n}) := by
      refine ⟨0, fun z hz => ?_⟩
      obtain ⟨n, _, rfl⟩ := hz
      exact div_nonneg (hr_nonneg n) (Nat.cast_nonneg n)
    -- sSup {log(M) - r_n/n} = log(M) - sInf {r_n/n}
    have hsSup_sub : sSup ((fun n => Real.log M - r n / n) '' {n : ℕ | 1 ≤ n}) =
                     Real.log M - sInf ((fun n => r n / n) '' {n : ℕ | 1 ≤ n}) := by
      have himg_sub : (fun n => Real.log M - r n / n) '' {n : ℕ | 1 ≤ n} =
                      (fun t => Real.log M - t) '' ((fun n => r n / n) '' {n : ℕ | 1 ≤ n}) := by
        ext w
        simp only [Set.mem_image, Set.mem_setOf_eq]
        constructor
        · rintro ⟨n, hn, rfl⟩; exact ⟨r n / n, ⟨n, hn, rfl⟩, rfl⟩
        · rintro ⟨t, ⟨n, hn, rfl⟩, rfl⟩; exact ⟨n, hn, rfl⟩
      rw [himg_sub]
      -- sSup (c - S) = c - sInf S for bounded below S
      have h1 : sSup ((fun t => Real.log M - t) '' ((fun n => r n / n) '' {n : ℕ | 1 ≤ n})) =
                Real.log M - sInf ((fun n => r n / n) '' {n : ℕ | 1 ≤ n}) := by
        -- This is a standard property: sSup (c - S) = c - sInf S
        apply le_antisymm
        · apply csSup_le (hne_r.image _)
          intro z hz
          obtain ⟨t, ht, rfl⟩ := hz
          have : sInf ((fun n => r n / n) '' {n : ℕ | 1 ≤ n}) ≤ t := csInf_le hbdd_r ht
          linarith
        · -- Use le_csSup_iff: prove a ≤ sSup s by: for any upper bound b of s, a ≤ b
          have hbdd_img : BddAbove ((fun t => Real.log M - t) '' ((fun n => r n / n) ''
                                    {n : ℕ | 1 ≤ n})) := by
            refine ⟨Real.log M, fun z hz => ?_⟩
            obtain ⟨t, ht, rfl⟩ := hz
            have : 0 ≤ t := by
              obtain ⟨n, _, rfl⟩ := ht
              exact div_nonneg (hr_nonneg n) (Nat.cast_nonneg n)
            linarith
          rw [le_csSup_iff hbdd_img (hne_r.image _)]
          intro b hb
          -- hb: b is an upper bound, i.e., ∀ x ∈ {Real.log M - t : t ∈ S}, x ≤ b
          -- Need: Real.log M - sInf S ≤ b
          -- For any ε > 0, ∃ t ∈ S with t < sInf S + ε, so Real.log M - t > Real.log M - sInf S - ε
          -- Since Real.log M - t ≤ b, we get Real.log M - sInf S - ε < b for all ε > 0
          by_contra hcontra
          push_neg at hcontra
          -- hcontra: b < Real.log M - sInf S
          set ε := Real.log M - sInf ((fun n => r n / n) '' {n : ℕ | 1 ≤ n}) - b with hε_def
          have hε_pos : 0 < ε := by linarith
          -- There exists t ∈ S with t < sInf S + ε = Real.log M - b
          have h_target : sInf ((fun n => r n / n) '' {n : ℕ | 1 ≤ n}) + ε =
                          Real.log M - b := by ring
          have hsInf_lt : sInf ((fun n => r n / n) '' {n : ℕ | 1 ≤ n}) <
                          sInf ((fun n => r n / n) '' {n : ℕ | 1 ≤ n}) + ε := by linarith
          obtain ⟨t, ht, hlt⟩ := (csInf_lt_iff hbdd_r hne_r).mp hsInf_lt
          -- Contradiction: Real.log M - t ≤ b but Real.log M - t > b
          have h_in_set : Real.log M - t ∈
              (fun t => Real.log M - t) '' ((fun n => r n / n) '' {n : ℕ | 1 ≤ n}) :=
            ⟨t, ht, rfl⟩
          have h_le_b : Real.log M - t ≤ b := hb h_in_set
          have h_gt_b : b < Real.log M - t := by
            calc b = Real.log M - sInf ((fun n => r n / n) '' {n : ℕ | 1 ≤ n}) - ε := by ring
              _ < Real.log M - t := by linarith
          linarith
      exact h1
    -- sSup (exp '' S) = exp (sSup S) for bounded S
    have hbdd_sub : BddAbove ((fun n => Real.log M - r n / n) '' {n : ℕ | 1 ≤ n}) := by
      refine ⟨Real.log M, fun z hz => ?_⟩
      obtain ⟨n, _, rfl⟩ := hz
      have : 0 ≤ r n / n := div_nonneg (hr_nonneg n) (Nat.cast_nonneg n)
      linarith
    have hne_sub : ((fun n => Real.log M - r n / n) '' {n : ℕ | 1 ≤ n}).Nonempty := by
      refine ⟨Real.log M - r 1 / 1, 1, le_refl 1, ?_⟩; simp
    -- exp is strictly increasing and continuous, so exp (sSup S) = sSup (exp '' S)
    -- Goal: sSup (exp '' S) = exp (log M - sInf ...)
    -- Step 1: sSup (exp '' S) = exp (sSup S) by Monotone.map_csSup_of_continuousAt
    -- Step 2: exp (sSup S) = exp (log M - sInf ...) by hsSup_sub
    have hexp_csSup := Monotone.map_csSup_of_continuousAt
      Real.continuous_exp.continuousAt Real.exp_monotone hne_sub hbdd_sub
    rw [← hexp_csSup, hsSup_sub]
  -- Tendsto y_n^{1/n} = Tendsto exp(log(M) - r_n/n)
  rw [hsSup_eq]
  -- From Fekete: Tendsto (r_n/n) → sInf {r_n/n}
  -- So Tendsto (log(M) - r_n/n) → log(M) - sInf {r_n/n}
  -- And exp continuous: Tendsto exp(log(M) - r_n/n) → exp(log(M) - sInf)
  have htend_r := hfek
  have htend_sub : Filter.Tendsto (fun n => Real.log M - r n / n) Filter.atTop
      (nhds (Real.log M - sInf ((fun n => r n / n) '' {n : ℕ | 1 ≤ n}))) := by
    exact htend_r.const_sub (Real.log M)
  have htend_exp := htend_sub.rexp
  -- Now show the two sequences are eventually equal
  refine Filter.Tendsto.congr' ?_ htend_exp
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨{n : ℕ | 1 ≤ n}, Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩, ?_⟩
  intro n hn
  have hn' : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  exact (hy_exp_eq n hn').symm

/-- For submultiplicative witnesses in AsympRel, sInf = 1 iff Tendsto to 1.
    This justifies replacing inf by lim in the definition. -/
theorem sInf_eq_one_iff_tendsto {x : ℕ → ℕ} (hx_ge1 : ∀ n, 1 ≤ x n)
    (hx_submult : ∀ n m, x (n + m) ≤ x n * x m) :
    sInf ((fun n => (x n : ℝ) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n}) = 1 ↔
    Filter.Tendsto (fun n => (x n : ℝ) ^ (1 / (n : ℝ))) Filter.atTop (nhds 1) := by
  constructor
  · -- sInf = 1 implies Tendsto 1 (by Fekete, since sInf = lim for submultiplicative)
    intro hsInf
    have hfek := fekete_multiplicative (fun n => Nat.one_le_cast.mpr (hx_ge1 n))
        (fun n m => by exact_mod_cast hx_submult n m)
    simp only [hsInf] at hfek
    convert hfek using 1
  · -- Tendsto 1 implies sInf = 1
    intro htend
    apply le_antisymm
    · -- sInf ≤ 1: values approach 1
      apply le_of_forall_pos_lt_add
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htend ε hε
      have hmem : (x (max N 1) : ℝ) ^ (1 / ((max N 1 : ℕ) : ℝ)) ∈
          (fun n => (x n : ℝ) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n} := by
        refine ⟨max N 1, ?_, rfl⟩
        exact le_max_right N 1
      have hbdd : BddBelow ((fun n => (x n : ℝ) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n}) := by
        refine ⟨1, fun z hz => ?_⟩
        obtain ⟨n, hn, rfl⟩ := hz
        have hn_pos : (0 : ℝ) < n :=
          Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn))
        calc 1 = 1 ^ (1 / (n : ℝ)) := by simp
          _ ≤ (x n : ℝ) ^ (1 / (n : ℝ)) := by
              apply Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
              · exact Nat.one_le_cast.mpr (hx_ge1 n)
              · exact div_nonneg (by norm_num) (le_of_lt hn_pos)
      calc sInf _ ≤ (x (max N 1) : ℝ) ^ (1 / ((max N 1 : ℕ) : ℝ)) :=
            csInf_le hbdd hmem
        _ < 1 + ε := by
            have hspec := hN (max N 1) (le_max_left _ _)
            simp only [Real.dist_eq] at hspec
            linarith [(abs_lt.mp hspec).2]
    · -- 1 ≤ sInf: all values ≥ 1 since x n ≥ 1
      have hne : ((fun n => (x n : ℝ) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n}).Nonempty := by
        refine ⟨(x 1 : ℝ) ^ (1 / (1 : ℝ)), 1, le_refl 1, ?_⟩
        simp
      apply le_csInf hne
      intro z hz
      obtain ⟨n, hn, rfl⟩ := hz
      have hn_pos : (0 : ℝ) < n :=
        Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn))
      calc 1 = 1 ^ (1 / (n : ℝ)) := by simp
        _ ≤ (x n : ℝ) ^ (1 / (n : ℝ)) := by
            apply Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
            · exact Nat.one_le_cast.mpr (hx_ge1 n)
            · exact div_nonneg (by norm_num) (le_of_lt hn_pos)

/-- Alternative characterization of AsympRel using limit instead of infimum.
    Valid because witnesses can be assumed submultiplicative. -/
theorem AsympRel_iff_tendsto [CommSemiring S] (p : StrassenPreorder S) (a b : S) :
    AsympRel p a b ↔
    ∃ x : ℕ → ℕ, (∀ n, n ≥ 1 → p.rel (a ^ n) ((b ^ n) * (x n))) ∧
      Filter.Tendsto (fun n => (x n : ℝ) ^ (1 / (n : ℝ))) Filter.atTop (nhds 1) := by
  constructor
  · -- sInf version implies Tendsto version
    intro ⟨x, hx_rel, hx_sInf⟩
    -- Key insight (Strassen): Replace x by its submultiplicative closure y.
    -- For any partition k₁+...+kₘ=n, multiplying a^{kᵢ} ≤ b^{kᵢ}·x_{kᵢ} gives
    -- a^n ≤ b^n·∏x_{kᵢ}, so the bound holds for any such product.
    -- y_n = min over partitions is submultiplicative, y ≤ x, bound holds.
    -- By Fekete, Tendsto(y^{1/n}) = sInf(y^{1/n}) = 1.

    -- First establish x_n ≥ 1 for n ≥ 1 (from sInf = 1)
    have hx_ge1 : ∀ n, n ≥ 1 → x n ≥ 1 := by
      intro n hn
      by_contra hlt
      push_neg at hlt
      -- x n < 1 and x n : ℕ implies x n = 0
      have hxn0 : x n = 0 := Nat.lt_one_iff.mp hlt
      -- (x n)^{1/n} = 0^{1/n} = 0 (since 1/n ≠ 0 for n ≥ 1)
      have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn)
      have h1n_ne : (1 : ℝ) / n ≠ 0 := one_div_ne_zero hn_ne
      have hval : (x n : ℝ) ^ ((1 : ℝ) / n) = 0 := by
        simp only [hxn0, Nat.cast_zero, Real.zero_rpow h1n_ne]
      have hmem : (0 : ℝ) ∈ (fun m => (x m : ℝ) ^ (1 / m : ℝ)) '' {m : ℕ | 1 ≤ m} :=
        ⟨n, hn, hval⟩
      have hbdd : BddBelow ((fun m => (x m : ℝ) ^ (1 / m : ℝ)) '' {m : ℕ | 1 ≤ m}) := by
        use 0
        intro z hz
        obtain ⟨m, _, rfl⟩ := hz
        exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hle := csInf_le hbdd hmem
      rw [hx_sInf] at hle; linarith
    -- The full proof defines y_n = min over compositions of n of ∏ x_{kᵢ}.
    -- Then y is submultiplicative, y ≤ x, and a^n ≤ b^n · y_n holds.
    -- By Fekete, Tendsto(y^{1/n}) = sInf(y^{1/n}) ≤ sInf(x^{1/n}) = 1.
    -- Since y_n ≥ 1 (product of x's which are ≥ 1), sInf(y^{1/n}) ≥ 1.
    -- So sInf(y^{1/n}) = 1, and by Fekete, Tendsto = 1.
    --
    -- Use the submultiplicative closure of x
    let y := submultClosure x
    use y
    constructor
    · -- The bound holds for y by submultClosure_bound
      exact submultClosure_bound p a b x hx_rel
    · -- Tendsto (y n)^{1/n} → 1 by Fekete (y is submultiplicative with y ≥ 1)
      -- y is submultiplicative: submultClosure_submult
      -- y ≥ 1: submultClosure_ge_one (since x ≥ 1 by hx_ge1)
      -- sInf(y^{1/n}) = sInf(x^{1/n}) = 1: submultClosure_sInf
      -- By Fekete, Tendsto = sInf = 1
      have hy_ge1 := submultClosure_ge_one x hx_ge1
      have hy_submult := submultClosure_submult x
      have hy_sInf : sInf ((fun n => (y n : ℝ) ^ (1 / n : ℝ)) '' {n : ℕ | 1 ≤ n}) = 1 :=
        submultClosure_sInf_eq_one_of x hx_ge1 hx_sInf
      -- Apply Fekete to get Tendsto = sInf
      have hy_ge1_all : ∀ n, 1 ≤ (y n : ℝ) := by
        intro n
        by_cases hn : n = 0
        · subst hn; change (1 : ℝ) ≤ (submultClosure x 0 : ℕ); simp [submultClosure_zero]
        · exact Nat.one_le_cast.mpr (hy_ge1 n (Nat.one_le_iff_ne_zero.mpr hn))
      have hy_submult_cast : ∀ n m, (y (n + m) : ℝ) ≤ (y n : ℝ) * (y m : ℝ) := by
        intro n m
        -- Unfold y to submultClosure x
        change (submultClosure x (n + m) : ℝ) ≤ (submultClosure x n : ℝ) * (submultClosure x m : ℝ)
        by_cases hn : n = 0
        · subst hn
          simp only [zero_add, submultClosure_zero, Nat.cast_one, one_mul, le_refl]
        · by_cases hm : m = 0
          · subst hm
            simp only [add_zero, submultClosure_zero, Nat.cast_one, mul_one, le_refl]
          · have hn1 : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn
            have hm1 : m ≥ 1 := Nat.one_le_iff_ne_zero.mpr hm
            have h := Nat.cast_le (α := ℝ).mpr (hy_submult n m hn1 hm1)
            simp only [Nat.cast_mul] at h
            exact h
      have hfekete := fekete_multiplicative hy_ge1_all hy_submult_cast
      rw [hy_sInf] at hfekete
      exact hfekete
  · -- Tendsto version implies sInf version
    intro ⟨x, hx_rel, hx_tendsto⟩
    -- Use y = x + 1 as the witness, since y_n ≥ 1 ensures sInf ≥ 1
    use fun n => x n + 1
    constructor
    · -- p.rel (a^n) (b^n * (x n + 1))
      intro n hn
      have hx := hx_rel n hn
      -- b^n * (x n + 1) = b^n * x n + b^n ≥ b^n * x n (using add_mono and zero_le)
      have heq : (b ^ n) * ((x n + 1 : ℕ) : S) = (b ^ n) * (x n : S) + b ^ n := by
        simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      rw [heq]
      have hadd : p.rel ((b ^ n) * (x n : S)) ((b ^ n) * (x n : S) + b ^ n) := by
        have h0 := p.zero_le (b ^ n)
        have h1 := p.add_mono 0 (b ^ n) ((b ^ n) * (x n : S)) h0
        simp only [zero_add] at h1
        rwa [add_comm] at h1
      exact p.trans _ _ _ hx hadd
    · -- sInf{(x n + 1)^{1/n}} = 1
      -- Since x n + 1 ≥ 1, we have (x n + 1)^{1/n} ≥ 1, so sInf ≥ 1
      -- Tendsto (x n + 1)^{1/n} → 1 since (x+c)^{1/n} → 1 when x^{1/n} → 1
      have hy_ge1 : ∀ n, 1 ≤ x n + 1 := fun n => Nat.le_add_left 1 (x n)
      have htendsto_y : Filter.Tendsto (fun n => ((x n + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ)))
          Filter.atTop (nhds 1) := by
        -- (x n + 1)^{1/n} is squeezed between 1 and (2 * x n)^{1/n} → 1
        rw [Metric.tendsto_atTop] at hx_tendsto ⊢
        intro ε hε
        -- Use δ = min(ε/4, 1) so that (1+δ)^2 ≤ 1 + ε always holds
        set δ := min (ε / 4) 1 with hδ_def
        have hδ_pos : 0 < δ := lt_min (by linarith) one_pos
        have hδ_le1 : δ ≤ 1 := min_le_right _ _
        have hδ_le_ε4 : δ ≤ ε / 4 := min_le_left _ _
        obtain ⟨N₁, hN₁⟩ := hx_tendsto δ hδ_pos
        have h2 : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ (1 / (n : ℝ))) Filter.atTop (nhds 1) := by
          have hinv : Filter.Tendsto (fun n : ℕ => (1 / (n : ℝ))) Filter.atTop (nhds 0) := by
            simp only [one_div]
            exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
          have hcont : Continuous (fun y : ℝ => (2 : ℝ) ^ y) :=
            Real.continuous_const_rpow (by norm_num)
          have h0 : (2 : ℝ) ^ (0 : ℝ) = 1 := Real.rpow_zero 2
          have htend0 : Filter.Tendsto (fun y : ℝ => (2 : ℝ) ^ y) (nhds 0) (nhds 1) := by
            rw [← h0]; exact hcont.continuousAt.tendsto
          exact htend0.comp hinv
        rw [Metric.tendsto_atTop] at h2
        obtain ⟨N₂, hN₂⟩ := h2 δ hδ_pos
        use max (max N₁ N₂) 1
        intro n hn
        have hn_ge1 : 1 ≤ n := le_of_max_le_right hn
        have hn_ge_N1 : N₁ ≤ n := le_trans (le_max_left _ _) (le_of_max_le_left hn)
        have hn_ge_N2 : N₂ ≤ n := le_trans (le_max_right _ _) (le_of_max_le_left hn)
        have hn_pos : (0 : ℝ) < n :=
          Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn_ge1))
        have hxn_dist := hN₁ n hn_ge_N1
        have h2n_dist := hN₂ n hn_ge_N2
        rw [Real.dist_eq] at hxn_dist h2n_dist ⊢
        by_cases hxn0 : x n = 0
        · -- If x n = 0, then (x n + 1) = 1, so (x n + 1)^{1/n} = 1
          simp only [hxn0, zero_add, Nat.cast_one, Real.one_rpow, sub_self, abs_zero]
          exact hε
        · -- x n ≥ 1 (since x n > 0 and x n : ℕ)
          have hxn_ge1 : 1 ≤ x n := Nat.one_le_iff_ne_zero.mpr hxn0
          -- Bounds from the distance conditions
          have h2_bound : (2 : ℝ) ^ (1 / (n : ℝ)) < 1 + δ := by linarith [(abs_lt.mp h2n_dist).2]
          have hxn_upper : (x n : ℝ) ^ (1 / (n : ℝ)) < 1 + δ := by linarith [(abs_lt.mp hxn_dist).2]
          have hxn_lower : 1 - δ < (x n : ℝ) ^ (1 / (n : ℝ)) := by linarith [(abs_lt.mp hxn_dist).1]
          -- (x n + 1)^{1/n} ≤ (2 * x n)^{1/n} = 2^{1/n} * (x n)^{1/n}
          have hupper : ((x n + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ)) ≤
              (2 : ℝ) ^ (1 / (n : ℝ)) * (x n : ℝ) ^ (1 / (n : ℝ)) := by
            have h1 : ((x n + 1 : ℕ) : ℝ) ≤ 2 * (x n : ℕ) := by
              simp only [Nat.cast_add, Nat.cast_one]
              have : (x n : ℝ) ≥ 1 := Nat.one_le_cast.mpr hxn_ge1
              linarith
            calc ((x n + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ))
                ≤ (2 * (x n : ℝ)) ^ (1 / (n : ℝ)) := by
                    apply Real.rpow_le_rpow (Nat.cast_nonneg _) h1
                    exact div_nonneg (by norm_num) (le_of_lt hn_pos)
              _ = (2 : ℝ) ^ (1 / (n : ℝ)) * (x n : ℝ) ^ (1 / (n : ℝ)) := by
                    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg _)]
          -- Lower bound: (x n + 1)^{1/n} ≥ (x n)^{1/n} ≥ 1 - δ > 1 - ε
          have hlower : ((x n + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ)) ≥ (x n : ℝ) ^ (1 / (n : ℝ)) := by
            apply Real.rpow_le_rpow (Nat.cast_nonneg _)
            · simp only [Nat.cast_add, Nat.cast_one]; linarith
            · exact div_nonneg (by norm_num) (le_of_lt hn_pos)
          -- Upper bound: 2^{1/n} * x_n^{1/n} < (1 + δ)^2 ≤ 1 + 4δ ≤ 1 + ε
          have h2_pos : 0 < (2 : ℝ) ^ (1 / (n : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
          have hxn_pos : 0 < (x n : ℝ) ^ (1 / (n : ℝ)) :=
            Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hxn0)) _
          have hprod_upper : (2 : ℝ) ^ (1 / (n : ℝ)) * (x n : ℝ) ^ (1 / (n : ℝ)) < 1 + ε := by
            have hprod_sq : (2 : ℝ) ^ (1 / (n : ℝ)) * (x n : ℝ) ^ (1 / (n : ℝ)) < (1 + δ) ^ 2 := by
              calc (2 : ℝ) ^ (1 / (n : ℝ)) * (x n : ℝ) ^ (1 / (n : ℝ))
                  < (1 + δ) * (1 + δ) := by
                      apply mul_lt_mul h2_bound (le_of_lt hxn_upper) hxn_pos (by linarith)
                _ = (1 + δ) ^ 2 := by ring
            -- (1 + δ)^2 = 1 + 2δ + δ^2 ≤ 1 + 2δ + δ = 1 + 3δ ≤ 1 + 3(ε/4) ≤ 1 + ε
            have hsq_bound : (1 + δ) ^ 2 ≤ 1 + ε := by
              have hδ2 : δ ^ 2 ≤ δ := by nlinarith
              calc (1 + δ) ^ 2 = 1 + 2 * δ + δ ^ 2 := by ring
                _ ≤ 1 + 2 * δ + δ := by linarith
                _ = 1 + 3 * δ := by ring
                _ ≤ 1 + 3 * (ε / 4) := by linarith
                _ ≤ 1 + ε := by linarith
            linarith
          rw [abs_lt]
          constructor
          · calc -ε < -δ := by linarith
              _ < (x n : ℝ) ^ (1 / (n : ℝ)) - 1 := by linarith
              _ ≤ ((x n + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ)) - 1 := by linarith [hlower]
          · calc ((x n + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ)) - 1
                ≤ (2 : ℝ) ^ (1 / (n : ℝ)) * (x n : ℝ) ^ (1 / (n : ℝ)) - 1 := by linarith [hupper]
              _ < 1 + ε - 1 := by linarith [hprod_upper]
              _ = ε := by ring
      -- Now prove sInf = 1
      apply le_antisymm
      · -- sInf ≤ 1: use the limit
        apply le_of_forall_pos_lt_add
        intro δ hδ
        obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htendsto_y δ hδ
        have hmem : ((x (max N 1) + 1 : ℕ) : ℝ) ^ (1 / ((max N 1 : ℕ) : ℝ)) ∈
            (fun n => ((x n + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n} := by
          refine ⟨max N 1, le_max_right N 1, rfl⟩
        have hbdd : BddBelow
            ((fun n => ((x n + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n}) := by
          refine ⟨1, fun z hz => ?_⟩
          obtain ⟨n, hn, rfl⟩ := hz
          have hn_pos : (0 : ℝ) < n :=
            Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn))
          calc 1 = (1 : ℝ) ^ (1 / (n : ℝ)) := by simp
            _ ≤ ((x n + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ)) := by
                apply Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
                · exact Nat.one_le_cast.mpr (hy_ge1 n)
                · exact div_nonneg (by norm_num) (le_of_lt hn_pos)
        have hdist := hN (max N 1) (le_max_left _ _)
        rw [Real.dist_eq] at hdist
        calc sInf _ ≤ ((x (max N 1) + 1 : ℕ) : ℝ) ^ (1 / ((max N 1 : ℕ) : ℝ)) :=
            csInf_le hbdd hmem
          _ < 1 + δ := by linarith [(abs_lt.mp hdist).2]
      · -- 1 ≤ sInf: all values ≥ 1 since x n + 1 ≥ 1
        have hne :
            ((fun n => ((x n + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n}).Nonempty := by
          use ((x 1 + 1 : ℕ) : ℝ) ^ (1 / (1 : ℝ))
          simp only [Set.mem_image, Set.mem_setOf_eq]
          exact ⟨1, le_refl 1, by simp⟩
        apply le_csInf hne
        intro z hz
        obtain ⟨n, hn, rfl⟩ := hz
        have hn_pos : (0 : ℝ) < n :=
          Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn))
        calc 1 = (1 : ℝ) ^ (1 / (n : ℝ)) := by simp
          _ ≤ ((x n + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ)) := by
              apply Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
              · exact Nat.one_le_cast.mpr (hy_ge1 n)
              · exact div_nonneg (by norm_num) (le_of_lt hn_pos)

/-! ### Transitivity of Asymptotic Relation -/

/-- The asymptotic relation is transitive.

    The key insight from Strassen: witnesses can be assumed submultiplicative
    (x_{n+m} ≤ x_n · x_m). By Fekete's lemma, for such sequences inf = lim.
    With lim, we get lim(x·y) = lim(x) · lim(y) = 1.

    Proof strategy:
    1. Convert to Tendsto formulation via AsympRel_iff_tendsto
    2. Use product witness z_n = x_n * y_n
    3. Chain of transitivity gives p.rel (a^n) (c^n * z_n)
    4. Product of limits gives Tendsto z^{1/n} → 1 -/
theorem AsympRel.trans [CommSemiring S] {p : StrassenPreorder S} {a b c : S}
    (hab : AsympRel p a b) (hbc : AsympRel p b c) : AsympRel p a c := by
  -- Convert to Tendsto formulation
  rw [AsympRel_iff_tendsto] at hab hbc ⊢
  obtain ⟨x, hx_rel, hx_tendsto⟩ := hab
  obtain ⟨y, hy_rel, hy_tendsto⟩ := hbc
  -- Use product witness z_n = x_n * y_n
  use fun n => x n * y n
  constructor
  · -- Show p.rel (a^n) (c^n * (x n * y n)) for n ≥ 1
    intro n hn
    -- From hab: p.rel (a^n) (b^n * x_n)
    have h1 := hx_rel n hn
    -- From hbc: p.rel (b^n) (c^n * y_n)
    have h2 := hy_rel n hn
    -- Multiply h2 by x_n: p.rel (b^n * x_n) (c^n * y_n * x_n)
    have h3 : p.rel (b ^ n * (x n : S)) (c ^ n * (y n : S) * (x n : S)) :=
      p.mul_mono _ _ (x n : S) h2
    -- Rewrite RHS
    have heq : c ^ n * (y n : S) * (x n : S) = c ^ n * ((x n * y n : ℕ) : S) := by
      simp only [Nat.cast_mul]; ring
    rw [heq] at h3
    -- Chain: a^n ≤ b^n * x_n ≤ c^n * (x_n * y_n)
    exact p.trans _ _ _ h1 h3
  · -- Show Tendsto (x n * y n)^{1/n} → 1
    -- (x n * y n)^{1/n} = x_n^{1/n} * y_n^{1/n}
    have hprod : ∀ n : ℕ, n ≥ 1 → ((x n * y n : ℕ) : ℝ) ^ (1 / (n : ℝ)) =
        (x n : ℝ) ^ (1 / (n : ℝ)) * (y n : ℝ) ^ (1 / (n : ℝ)) := by
      intro n hn
      have hn_pos : (0 : ℝ) < n :=
        Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn))
      have hexp_pos : (0 : ℝ) < 1 / n := div_pos one_pos hn_pos
      simp only [Nat.cast_mul]
      exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    -- Filter.Tendsto for products
    have htend_prod := Filter.Tendsto.mul hx_tendsto hy_tendsto
    simp only [mul_one] at htend_prod
    -- Need to show the sequences are eventually equal
    rw [Metric.tendsto_atTop] at htend_prod ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := htend_prod ε hε
    use max N 1
    intro n hn
    have hn_ge1 : 1 ≤ n := le_of_max_le_right hn
    have hn_ge_N : N ≤ n := le_of_max_le_left hn
    rw [hprod n hn_ge1]
    exact hN n hn_ge_N

/-- **Asymptotic relation from a cofinal subsequence of finite restrictions.**

If, along a strictly increasing sequence of exponents `m k ≥ 1`, we have finite
restrictions `a^{m k} ≤ b^{m k} · c k` whose *rate* `c k ^ {1/(m k)} → 1`, and we
also have a uniform crude archimedean bound `a^n ≤ b^n · r^n` at *every* exponent
(with `r ≥ 1`), then `a ≲ b` asymptotically.

The witness is `r^n` by default, lowered to `min (r^n) (c k)` at the cofinal
exponents `n = m k`. Every exponent has a valid bound (the crude one), while the
infimum of the rate is driven to `1` along the cofinal subsequence. This is the
real-analysis packaging used to assemble `AsympRel` from Strassen's diagonal
descent (one overhead `q_n` per exponent `n`, evaluated at the diagonal power
`M = q_n`). -/
theorem asympRel_of_subseq [CommSemiring S] {p : StrassenPreorder S} {a b : S}
    (m : ℕ → ℕ) (c : ℕ → ℕ) (r : ℕ)
    (hm_mono : StrictMono m) (hm1 : ∀ k, 1 ≤ m k)
    (hr1 : 1 ≤ r) (hc1 : ∀ k, 1 ≤ c k)
    (hcrude : ∀ n, n ≥ 1 → p.rel (a ^ n) (b ^ n * ((r ^ n : ℕ) : S)))
    (hsub : ∀ k, p.rel (a ^ m k) (b ^ m k * ((c k : ℕ) : S)))
    (hrate : Filter.Tendsto (fun k => (c k : ℝ) ^ (1 / (m k : ℝ)))
      Filter.atTop (nhds 1)) :
    AsympRel p a b := by
  classical
  -- The witness: crude `r^n` everywhere, lowered to `min (r^n) (c k)` at `n = m k`.
  set x : ℕ → ℕ := fun n => if h : ∃ k, m k = n then min (r ^ n) (c h.choose) else r ^ n
    with hx_def
  -- `m k` is hit by exactly one `k` (strict monotonicity), namely `k` itself.
  have hchoose : ∀ k, (⟨k, rfl⟩ : ∃ j, m j = m k).choose = k := by
    intro k
    have hspec : m ((⟨k, rfl⟩ : ∃ j, m j = m k).choose) = m k :=
      (⟨k, rfl⟩ : ∃ j, m j = m k).choose_spec
    exact hm_mono.injective hspec
  -- Value of `x` at a cofinal exponent.
  have hx_at : ∀ k, x (m k) = min (r ^ m k) (c k) := by
    intro k
    have hex : ∃ j, m j = m k := ⟨k, rfl⟩
    simp only [hx_def, dif_pos hex]
    -- the chosen `j` equals `k`
    have : hex.choose = k := by
      have hspec : m hex.choose = m k := hex.choose_spec
      exact hm_mono.injective hspec
    rw [this]
  -- Every `x n ≥ 1`.
  have hx_ge1 : ∀ n, 1 ≤ x n := by
    intro n
    by_cases h : ∃ k, m k = n
    · simp only [hx_def, dif_pos h]
      exact le_min (Nat.one_le_pow _ _ (by omega)) (hc1 _)
    · simp only [hx_def, dif_neg h]
      exact Nat.one_le_pow _ _ (by omega)
  -- The relation bound holds at every `n ≥ 1`.
  have hx_rel : ∀ n, n ≥ 1 → p.rel (a ^ n) (b ^ n * ((x n : ℕ) : S)) := by
    intro n hn
    by_cases h : ∃ k, m k = n
    · obtain ⟨k, hk⟩ := h
      have hex : ∃ j, m j = n := ⟨k, hk⟩
      -- `x n = min (r^n) (c (choose))`; both crude & sub bounds are valid.
      have hxval : x n = min (r ^ n) (c hex.choose) := by
        simp only [hx_def, dif_pos hex]
      have hchoose_eq : m hex.choose = n := hex.choose_spec
      -- crude bound and subsequence bound (rewritten to exponent n)
      have hcr := hcrude n hn
      have hsb := hsub hex.choose
      rw [hchoose_eq] at hsb
      rw [hxval]
      rcases min_choice (r ^ n) (c hex.choose) with hmin | hmin
      · rw [hmin]; exact hcr
      · rw [hmin]; exact hsb
    · have hxval : x n = r ^ n := by simp only [hx_def, dif_neg h]
      rw [hxval]; exact hcrude n hn
  refine ⟨x, hx_rel, ?_⟩
  -- `sInf` of the rate sequence equals 1.
  set img := (fun n => (x n : ℝ) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n} with himg_def
  have hbdd : BddBelow img := by
    refine ⟨0, ?_⟩
    rintro z ⟨n, _, rfl⟩
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hne : img.Nonempty := ⟨(fun n => (x n : ℝ) ^ (1 / (n : ℝ))) 1, 1, le_refl 1, rfl⟩
  apply le_antisymm
  · -- `sInf ≤ 1`: cofinal subsequence drives the rate down to `1`.
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    -- Need: `sInf ≤ 1 + ε`. Find a cofinal element below `1 + ε`.
    rw [Metric.tendsto_atTop] at hrate
    obtain ⟨K, hK⟩ := hrate ε hε
    have hbound := hK K (le_refl K)
    rw [Real.dist_eq] at hbound
    -- `c K ^ {1/(m K)} < 1 + ε`
    have hcrate_lt : (c K : ℝ) ^ (1 / (m K : ℝ)) < 1 + ε := by
      have := (abs_lt.mp hbound).2; linarith
    -- `x (m K) ≤ c K`, and `m K ≥ 1`, so the rate element at `m K` is `≤ c K^{1/(m K)}`.
    have hmK1 : 1 ≤ m K := hm1 K
    have hmK_pos : (0 : ℝ) < (m K : ℝ) :=
      Nat.cast_pos.mpr (by omega)
    have hxle : (x (m K) : ℝ) ≤ (c K : ℝ) := by
      rw [hx_at K]; exact_mod_cast min_le_right _ _
    have helt : (x (m K) : ℝ) ^ (1 / (m K : ℝ)) ≤ (c K : ℝ) ^ (1 / (m K : ℝ)) := by
      apply Real.rpow_le_rpow (Nat.cast_nonneg _) hxle
      exact le_of_lt (div_pos one_pos hmK_pos)
    have hmem : (x (m K) : ℝ) ^ (1 / (m K : ℝ)) ∈ img := ⟨m K, hmK1, rfl⟩
    calc sInf img ≤ (x (m K) : ℝ) ^ (1 / (m K : ℝ)) := csInf_le hbdd hmem
      _ ≤ (c K : ℝ) ^ (1 / (m K : ℝ)) := helt
      _ ≤ 1 + ε := le_of_lt hcrate_lt
  · -- `1 ≤ sInf`: every rate element is `≥ 1` since `x n ≥ 1`.
    apply le_csInf hne
    rintro z ⟨n, hn, rfl⟩
    have hn_pos : (0 : ℝ) < n :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn))
    calc (1 : ℝ) = 1 ^ (1 / (n : ℝ)) := by simp
      _ ≤ (x n : ℝ) ^ (1 / (n : ℝ)) := by
          apply Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
          · exact_mod_cast hx_ge1 n
          · exact le_of_lt (div_pos one_pos hn_pos)

/-! ### Inclusion of Strassen Preorders -/

/-- One Strassen preorder contains another -/
def StrassenPreorder.le [CommSemiring S] (p q : StrassenPreorder S) : Prop :=
  ∀ a b, p.rel a b → q.rel a b

instance [CommSemiring S] : LE (StrassenPreorder S) where
  le := StrassenPreorder.le

/-- Strassen preorders form a partial order under inclusion -/
theorem StrassenPreorder.le_refl [CommSemiring S] (p : StrassenPreorder S) : p ≤ p :=
  fun _ _ h => h

theorem StrassenPreorder.le_trans [CommSemiring S] {p q r : StrassenPreorder S}
    (hpq : p ≤ q) (hqr : q ≤ r) : p ≤ r :=
  fun a b h => hqr a b (hpq a b h)

/-! ### Total Preorders -/

/-- A preorder is total if for all a, b: a ≤ b or b ≤ a -/
def StrassenPreorder.IsTotal [CommSemiring S] (p : StrassenPreorder S) : Prop :=
  ∀ a b : S, p.rel a b ∨ p.rel b a

/-! ### Maximality -/

/-- A Strassen preorder is maximal if it cannot be properly extended -/
def StrassenPreorder.IsMaximal [CommSemiring S] (p : StrassenPreorder S) : Prop :=
  ∀ q : StrassenPreorder S, p ≤ q → q ≤ p

/-! ### Monotone Envelope Convergence

The monotone envelope `y_n = max(1, x_1, ..., x_n)` of a sequence x with x^{1/n} → 1
also satisfies y^{1/n} → 1. This is used in the proof of add_mono. -/

/-- The monotone envelope of a sequence -/
def monotoneEnvelope (x : ℕ → ℕ) : ℕ → ℕ := fun n =>
  if n = 0 then 1 else Finset.sup' (Finset.range (n + 1))
    (by simp only [Finset.nonempty_range_iff]; omega)
    (fun k => if k = 0 then 1 else x k)

theorem monotoneEnvelope_ge_one (x : ℕ → ℕ) : ∀ n, monotoneEnvelope x n ≥ 1 := by
  intro n
  by_cases hn : n = 0
  · simp [hn, monotoneEnvelope]
  · simp only [monotoneEnvelope, hn, ↓reduceIte]
    have hne : (Finset.range (n + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
    have h0_mem : 0 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have h1_eq : (fun k : ℕ => if k = 0 then 1 else x k) 0 = 1 := by simp
    have : 1 ≤ Finset.sup' (Finset.range (n + 1)) hne (fun k => if k = 0 then 1 else x k) := by
      calc (1 : ℕ) = (fun k : ℕ => if k = 0 then 1 else x k) 0 := h1_eq.symm
        _ ≤ Finset.sup' (Finset.range (n + 1)) hne (fun k => if k = 0 then 1 else x k) :=
            Finset.le_sup' (fun k => if k = 0 then 1 else x k) h0_mem
    exact this

/-- Key lemma: If x^{1/n} → 1 and x_n ≥ 1, then (monotoneEnvelope x)^{1/n} → 1.
    Proof: The monotone envelope y_n = max{1, x_1, ..., x_n} satisfies:
    - Lower bound: y_n ≥ 1, so y_n^{1/n} ≥ 1
    - Upper bound: For large n, y_n ≤ max(C, (1+ε)^n), so y_n^{1/n} ≤ max(C^{1/n}, 1+ε) → 1+ε

    The proof follows this outline:
    1. For ε > 0, get K from hx_tendsto such that ∀k ≥ K, x_k^{1/k} < 1 + ε/2
    2. Let C = monotoneEnvelope x K (the prefix constant)
    3. Get N₁ such that C^{1/n} < 1 + ε/2 for n ≥ N₁
    4. For n ≥ max(K, N₁), show:
       - Lower: (monotoneEnvelope x n)^{1/n} ≥ 1 (since monotoneEnvelope ≥ 1)
       - Upper: (monotoneEnvelope x n)^{1/n} ≤ max(C^{1/n}, 1+ε/2) < 1+ε -/
theorem monotoneEnvelope_tendsto (x : ℕ → ℕ)
    (_ : ∀ n, n ≥ 1 → x n ≥ 1)
    (hx_tendsto : Filter.Tendsto (fun n => (x n : ℝ) ^ (1 / (n : ℝ))) Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun n => (monotoneEnvelope x n : ℝ) ^ (1 / (n : ℝ))) Filter.atTop (nhds 1) := by
  -- We use the squeeze theorem: 1 ≤ y_n^{1/n} ≤ upper_bound → 1
  rw [Metric.tendsto_atTop] at hx_tendsto ⊢
  intro ε hε
  -- Get K such that ∀k ≥ K, |x_k^{1/k} - 1| < ε/2
  obtain ⟨K, hK⟩ := hx_tendsto (ε / 2) (by linarith)
  -- Let C = monotoneEnvelope x (max K 1)
  let C := monotoneEnvelope x (max K 1)
  have hC_ge1 : C ≥ 1 := monotoneEnvelope_ge_one x (max K 1)
  -- Get N₁ such that C^{1/n} < 1 + ε/2 for n ≥ N₁
  -- C^{1/n} = exp(log(C)/n) → exp(0) = 1 as n → ∞
  have hC_pow : Filter.Tendsto (fun n : ℕ => (C : ℝ) ^ (1 / (n : ℝ))) Filter.atTop (nhds 1) := by
    have hC_pos : (0 : ℝ) < C := by positivity
    -- C^{1/n} = exp(log(C) * (1/n)) → exp(0) = 1
    have hexp : Filter.Tendsto (fun n : ℕ => Real.exp (Real.log C / n)) Filter.atTop
        (nhds 1) := by
      have htend_zero : Filter.Tendsto (fun n : ℕ => Real.log C / (n : ℝ)) Filter.atTop
          (nhds 0) := by
        exact tendsto_const_div_atTop_nhds_zero_nat (Real.log C)
      have hexp_cont := Real.continuous_exp.tendsto 0
      simp only [Real.exp_zero] at hexp_cont
      exact hexp_cont.comp htend_zero
    convert hexp using 1
    ext n
    by_cases hn : n = 0
    · simp [hn]
    · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      rw [Real.rpow_def_of_pos hC_pos, one_div, div_eq_mul_inv]
  rw [Metric.tendsto_atTop] at hC_pow
  obtain ⟨N₁, hN₁⟩ := hC_pow (ε / 2) (by linarith)
  -- For n ≥ max(max K 1, N₁), the monotone envelope satisfies the bound
  use max (max K 1) N₁
  intro n hn
  have hn_ge_K : n ≥ max K 1 := Nat.le_trans (le_max_left _ _) hn
  have hn_ge_N₁ : n ≥ N₁ := Nat.le_trans (le_max_right _ _) hn
  have hn_ge1 : n ≥ 1 := Nat.le_trans (le_max_right K 1) hn_ge_K
  have hn_pos : (0 : ℝ) < n :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn_ge1))
  have hy_ge1 := monotoneEnvelope_ge_one x n
  -- Lower bound: y_n^{1/n} ≥ 1
  have hlower : 1 ≤ (monotoneEnvelope x n : ℝ) ^ (1 / (n : ℝ)) := by
    calc 1 = 1 ^ (1 / (n : ℝ)) := by simp
      _ ≤ (monotoneEnvelope x n : ℝ) ^ (1 / (n : ℝ)) := by
          apply Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1)
          · exact Nat.one_le_cast.mpr hy_ge1
          · exact div_nonneg (by norm_num) (le_of_lt hn_pos)
  -- Upper bound: y_n ≤ max(C, max over k in [max K 1, n] of x_k)
  -- For k ≥ max K 1, x_k^{1/k} < 1 + ε/2, so x_k < (1 + ε/2)^k ≤ (1 + ε/2)^n
  have hupper : (monotoneEnvelope x n : ℝ) ^ (1 / (n : ℝ)) ≤
      max ((C : ℝ) ^ (1 / (n : ℝ))) (1 + ε / 2) := by
    -- Step 1: Show monotoneEnvelope x n ≤ max(C, (1+ε/2)^n)
    have hε2_pos : 1 + ε / 2 > 1 := by linarith
    have hε2_ge1 : 1 + ε / 2 ≥ 1 := le_of_lt hε2_pos
    -- For k with max K 1 < k ≤ n: x_k < (1+ε/2)^k ≤ (1+ε/2)^n
    have hxk_bound : ∀ k, max K 1 < k → k ≤ n → (x k : ℝ) < (1 + ε / 2) ^ n := by
      intro k hk_lo hk_hi
      have hk_ge_K : k ≥ K := Nat.le_trans (le_max_left K 1) (le_of_lt hk_lo)
      have hk_ge1 : k ≥ 1 := Nat.le_trans (le_max_right K 1) (le_of_lt hk_lo)
      have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero
          (Nat.one_le_iff_ne_zero.mp hk_ge1))
      -- From hK: |x_k^{1/k} - 1| < ε/2
      have hdist := hK k hk_ge_K
      rw [Real.dist_eq] at hdist
      have hxk_lt : (x k : ℝ) ^ (1 / (k : ℝ)) < 1 + ε / 2 := by
        have := abs_sub_lt_iff.mp hdist
        linarith
      -- x_k < (1+ε/2)^k
      have hxk_lt_pow : (x k : ℝ) < (1 + ε / 2) ^ k := by
        have h1 : (x k : ℝ) = ((x k : ℝ) ^ (1 / (k : ℝ))) ^ (k : ℝ) := by
          have hxk_nonneg : (0 : ℝ) ≤ x k := Nat.cast_nonneg _
          rw [← Real.rpow_mul hxk_nonneg]
          simp only [one_div, inv_mul_cancel₀ (ne_of_gt hk_pos), Real.rpow_one]
        rw [h1]
        calc ((x k : ℝ) ^ (1 / (k : ℝ))) ^ (k : ℝ)
            < (1 + ε / 2) ^ (k : ℝ) := by
                apply Real.rpow_lt_rpow
                · apply Real.rpow_nonneg (Nat.cast_nonneg _)
                · exact hxk_lt
                · exact hk_pos
          _ = (1 + ε / 2) ^ k := Real.rpow_natCast _ _
      -- (1+ε/2)^k ≤ (1+ε/2)^n since k ≤ n and 1+ε/2 > 1
      calc (x k : ℝ) < (1 + ε / 2) ^ k := hxk_lt_pow
        _ ≤ (1 + ε / 2) ^ n := by
            exact pow_le_pow_right₀ hε2_ge1 hk_hi
    -- monotoneEnvelope x n ≤ max(C, (1+ε/2)^n)
    have henv_bound : (monotoneEnvelope x n : ℝ) ≤ max (C : ℝ) ((1 + ε / 2) ^ n) := by
      simp only [monotoneEnvelope]
      split_ifs with hn0
      · -- n = 0 case
        simp only [hn0, Nat.cast_one]
        apply le_max_of_le_left
        exact Nat.one_le_cast.mpr hC_ge1
      · -- n ≠ 0 case
        have hne : (Finset.range (n + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
        -- The sup' is the max of (if k=0 then 1 else x k) over k in {0,...,n}
        -- We'll show each element ≤ max C ((1+ε/2)^n), then sup' ≤ max
        have helem_bound : ∀ k ∈ Finset.range (n + 1),
            ((fun j => if j = 0 then 1 else x j) k : ℝ) ≤ max (C : ℝ) ((1 + ε / 2) ^ n) := by
          intro k hk_mem
          have hk_le_n : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk_mem)
          by_cases hk0 : k = 0
          · -- k = 0: value is 1
            simp only [hk0, ↓reduceIte, Nat.cast_one]
            apply le_max_of_le_left
            exact Nat.one_le_cast.mpr hC_ge1
          · -- k ≠ 0: value is x k
            simp only [hk0, ↓reduceIte]
            by_cases hk_small : k ≤ max K 1
            · -- k ≤ max K 1: x k ≤ C since C = monotoneEnvelope x (max K 1)
              apply le_max_of_le_left
              -- x k ≤ monotoneEnvelope x (max K 1) for k ≤ max K 1, k ≠ 0
              have hmaxK1_ne0 : max K 1 ≠ 0 := by omega
              have hne' : (Finset.range (max K 1 + 1)).Nonempty :=
                  ⟨0, Finset.mem_range.mpr (by omega)⟩
              have hk_mem' : k ∈ Finset.range (max K 1 + 1) :=
                  Finset.mem_range.mpr (by omega)
              have hC_unfold : C = (Finset.range (max K 1 + 1)).sup' hne'
                  (fun j => if j = 0 then 1 else x j) := by
                change monotoneEnvelope x (max K 1) = _
                simp only [monotoneEnvelope, hmaxK1_ne0, ↓reduceIte]
              rw [hC_unfold]
              apply Nat.cast_le.mpr
              have hle : x k ≤ (Finset.range (max K 1 + 1)).sup' hne'
                  (fun j => if j = 0 then 1 else x j) := by
                have h1 : (fun j => if j = 0 then 1 else x j) k = x k := by simp [hk0]
                rw [← h1]
                exact Finset.le_sup' (fun j => if j = 0 then 1 else x j) hk_mem'
              exact hle
            · -- k > max K 1: x k < (1+ε/2)^n
              push_neg at hk_small
              apply le_max_of_le_right
              exact le_of_lt (hxk_bound k hk_small hk_le_n)
        -- The goal is: (sup' (...) : ℝ) ≤ max C ((1+ε/2)^n)
        -- For each k ∈ [0..n], f(k) is bounded. We show sup' ≤ bound.
        -- The sup' of ℕ values equals some value f(k_max), so cast and use helem_bound.
        let f := fun k => if k = 0 then 1 else x k
        -- The sup' is the max of f over the range, which equals f(some index)
        -- For finite linearly ordered types, sup' = max element = f(argmax)
        -- We use that casting preserves ≤ for each element
        have hcast_bound : ∀ k ∈ Finset.range (n + 1),
            (f k : ℝ) ≤ max (C : ℝ) ((1 + ε / 2) ^ n) := by
          intro k' hk'
          exact helem_bound k' hk'
        -- Now use Finset.sup'_le for ℕ → ℝ
        -- Actually we need to show ↑(sup' f) ≤ bound
        -- For ℕ with usual order, sup' f = f(argmax)
        -- So ↑(sup' f) = ↑(f(argmax)) ≤ bound by hcast_bound
        -- Get the index where sup' is achieved
        have hmax_exists := Finset.exists_max_image (Finset.range (n + 1)) f
            ⟨0, Finset.mem_range.mpr (by omega)⟩
        obtain ⟨k_max, hk_max_mem, hk_max_prop⟩ := hmax_exists
        have hsup_eq_fmax : (Finset.range (n + 1)).sup' hne f = f k_max := by
          apply le_antisymm
          · apply Finset.sup'_le hne
            intro k' hk'
            exact hk_max_prop k' hk'
          · exact Finset.le_sup' f hk_max_mem
        rw [hsup_eq_fmax]
        exact hcast_bound k_max hk_max_mem
    -- Step 2: Taking 1/n power
    have hdiv_pos : 0 < 1 / (n : ℝ) := by positivity
    calc (monotoneEnvelope x n : ℝ) ^ (1 / (n : ℝ))
        ≤ (max (C : ℝ) ((1 + ε / 2) ^ n)) ^ (1 / (n : ℝ)) := by
            apply Real.rpow_le_rpow (Nat.cast_nonneg _) henv_bound (le_of_lt hdiv_pos)
      _ = max ((C : ℝ) ^ (1 / (n : ℝ))) (((1 + ε / 2) ^ n) ^ (1 / (n : ℝ))) := by
          rw [Real.rpow_max (Nat.cast_nonneg _) (by positivity : (0:ℝ) ≤ (1+ε/2)^n)
              (le_of_lt hdiv_pos)]
      _ = max ((C : ℝ) ^ (1 / (n : ℝ))) (1 + ε / 2) := by
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ 1 + ε / 2)]
          simp [Nat.one_le_iff_ne_zero.mp hn_ge1]
  -- Combine: |y_n^{1/n} - 1| < ε
  have hC_bound : |((C : ℝ) ^ (1 / (n : ℝ))) - 1| < ε / 2 := hN₁ n hn_ge_N₁
  have hC_lt : (C : ℝ) ^ (1 / (n : ℝ)) < 1 + ε / 2 := by
    have := abs_sub_lt_iff.mp hC_bound
    linarith
  have hmax_lt : max ((C : ℝ) ^ (1 / (n : ℝ))) (1 + ε / 2) ≤ 1 + ε / 2 := by
    simp only [max_le_iff]
    exact ⟨le_of_lt hC_lt, le_refl _⟩
  calc |(monotoneEnvelope x n : ℝ) ^ (1 / (n : ℝ)) - 1|
      = (monotoneEnvelope x n : ℝ) ^ (1 / (n : ℝ)) - 1 := by
          apply abs_of_nonneg; linarith
    _ ≤ max ((C : ℝ) ^ (1 / (n : ℝ))) (1 + ε / 2) - 1 := by linarith [hupper]
    _ ≤ (1 + ε / 2) - 1 := by linarith [hmax_lt]
    _ = ε / 2 := by ring
    _ < ε := by linarith

end AsymptoticSpectrumDuality
