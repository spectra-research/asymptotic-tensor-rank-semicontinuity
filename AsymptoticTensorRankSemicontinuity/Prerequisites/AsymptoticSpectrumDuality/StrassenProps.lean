/-
Copyright (c) 2024 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.AsymptoticSpectrumDuality.Defs

set_option linter.style.emptyLine false

/-!
# Properties of Strassen Preorders

This file proves key properties of Strassen preorders, following Lemma str_props
from Strassen (1988).

## Main Results

* `asymp_of_add_cancel` : If a + b ≤ a' + b then a ≲ a' (Lemma str_props (i))
* `asymp_of_mul_cancel` : If ab ≤ a'b with b ≠ 0 then a ≲ a' (Lemma str_props (ii))
* `asymp_idempotent` : ≲≲ = ≲ (Lemma str_props (iii))

## References

* Strassen (1988), The asymptotic spectrum of tensors, Lemma str_props
-/

namespace AsymptoticSpectrumDuality

open StrassenPreorder

variable {S : Type*} [CommSemiring S]

/-! ### Properties from Lemma str_props -/

/-- Lemma str_props (ii): If ab ≤ a'b with b ≠ 0 then a ≲ a'.
    Proof: By induction, (ab)^N ≤ (a'b)^N, i.e., a^N · b^N ≤ a'^N · b^N.
    Then find m, r with 1 ≤ mb ≤ r, giving a^N ≤ a'^N · r. -/
theorem StrassenPreorder.asymp_of_mul_cancel (p : StrassenPreorder S)
    {a a' b : S} (hb : b ≠ 0) (h : p.rel (a * b) (a' * b)) :
    AsympRel p a a' := by
  -- Step 1: By induction, a^N * b ≤ a'^N * b for all N
  have hpow : ∀ N : ℕ, p.rel (a ^ N * b) (a' ^ N * b) := by
    intro N
    induction N with
    | zero => simp only [pow_zero, one_mul]; exact p.refl b
    | succ N ih =>
      -- a^{N+1} * b = a * (a^N * b) ≤ a * (a'^N * b) by ih
      have h1 : p.rel (a ^ N * b * a) (a' ^ N * b * a) := p.mul_mono _ _ a ih
      have eq1 : a ^ N * b * a = a ^ (N + 1) * b := by ring
      have eq1' : a' ^ N * b * a = a * a' ^ N * b := by ring
      rw [eq1, eq1'] at h1
      -- a * (a'^N * b) ≤ a' * (a'^N * b) = a'^{N+1} * b by h
      have h2 : p.rel (a * b * a' ^ N) (a' * b * a' ^ N) := p.mul_mono _ _ (a' ^ N) h
      have eq2 : a * b * a' ^ N = a * a' ^ N * b := by ring
      have eq2' : a' * b * a' ^ N = a' ^ (N + 1) * b := by ring
      rw [eq2, eq2'] at h2
      exact p.trans _ _ _ h1 h2
  -- Step 2: Find m, r with 1 ≤ mb ≤ r using archimedean
  have hone : (1 : S) ≠ 0 := by
    intro h
    -- If 1 = 0 in S, then p.rel (1 : S) (0 : S) by reflexivity (both are 0)
    have hrel : p.rel (1 : S) (0 : S) := by rw [h]; exact p.refl 0
    -- By nat_compat, this means 1 ≤ 0 as naturals
    exact p.not_rel_one_zero hrel
  obtain ⟨m, hm⟩ := p.archimedean 1 b hb
  obtain ⟨r, hr⟩ := p.archimedean (m * b) 1 hone
  simp only [mul_one] at hr
  -- Step 3: Construct witness: a^N ≤ a'^N * r
  use fun _ => r
  constructor
  · intro N _
    have h1 : p.rel (a ^ N) (a ^ N * (m * b)) := by
      have := p.mul_mono _ _ (a ^ N) hm
      simp only [one_mul] at this
      convert this using 1; ring
    have h2 : p.rel (a ^ N * (m * b)) (a' ^ N * (m * b)) := by
      have := p.mul_mono _ _ m (hpow N)
      convert this using 1 <;> ring
    have h3 : p.rel (a' ^ N * (m * b)) (a' ^ N * r) := by
      have := p.mul_mono _ _ (a' ^ N) hr
      convert this using 1 <;> ring
    exact p.trans _ _ _ (p.trans _ _ _ h1 h2) h3
  · -- sInf {r^{1/N} | N ≥ 1} = 1 (constant sequence)
    -- For constant r, r^{1/N} is decreasing and → 1 as N → ∞
    by_cases hr0 : r = 0
    · -- 0^{1/n} = 0 for n ≥ 1
      -- But this case is impossible: if r = 0 and 1 ≤ mb ≤ r = 0, then 1 ≤ 0
      exfalso
      have h1 : p.rel 1 (m * b) := hm
      have h2 : p.rel (m * b) 0 := by simp only [hr0, Nat.cast_zero] at hr; exact hr
      have h3 : p.rel 1 0 := p.trans _ _ _ h1 h2
      exact p.not_rel_one_zero h3
    · have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hr0)
      -- Show sInf {r^{1/N} | N ≥ 1} = 1
      apply le_antisymm
      · -- sInf ≤ 1: Since r^{1/N} → 1 as N → ∞, for any ε > 0 there's N with r^{1/N} < 1 + ε
        -- First establish the tendsto result
        have htend : Filter.Tendsto (fun n : ℕ => (r : ℝ) ^ (1 / (n : ℝ)))
            Filter.atTop (nhds 1) := by
          have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) := by
            simp only [one_div]
            exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
          have h2 : ContinuousAt (fun x : ℝ => (r : ℝ) ^ x) 0 :=
            Real.continuousAt_const_rpow (ne_of_gt hr_pos)
          have h3 := h2.tendsto.comp h1
          simp only [Function.comp_def, Real.rpow_zero] at h3
          exact h3
        -- sInf ≤ 1 via le_of_forall_pos_lt_add
        apply le_of_forall_pos_lt_add
        intro ε hε
        -- There exists N with r^{1/N} < 1 + ε
        have hnear := Metric.tendsto_atTop.mp htend ε hε
        obtain ⟨N, hN⟩ := hnear
        specialize hN (max N 1) (le_max_left _ _)
        simp only [Real.dist_eq] at hN
        have habs := (abs_lt.mp hN).2
        have hN_ge1 : 1 ≤ max N 1 := le_max_right _ _
        -- sInf ≤ r^{1/(max N 1)} < 1 + ε
        have hmem : (r : ℝ) ^ (1 / ((max N 1 : ℕ) : ℝ)) ∈
            (fun n : ℕ => (r : ℝ) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n} :=
          ⟨max N 1, hN_ge1, rfl⟩
        calc sInf ((fun n : ℕ => (r : ℝ) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n})
            ≤ (r : ℝ) ^ (1 / ((max N 1 : ℕ) : ℝ)) := by
              apply csInf_le
              · refine ⟨0, fun x hx => ?_⟩
                obtain ⟨n, _, rfl⟩ := hx
                apply Real.rpow_nonneg (Nat.cast_nonneg _)
              · exact hmem
          _ < 1 + ε := by linarith
      · -- 1 ≤ sInf: All values r^{1/N} ≥ 1 when r ≥ 1
        apply le_csInf
        · exact ⟨_, ⟨1, Nat.le_refl 1, rfl⟩⟩
        · intro x hx
          obtain ⟨n, hn, rfl⟩ := hx
          -- r^{1/n} ≥ 1 when r ≥ 1
          -- Actually we need r ≥ 1 for this. Let's check: we have 1 ≤ mb ≤ r
          -- so r ≥ 1
          have hr_ge1 : (1 : ℝ) ≤ r := by
            have h1 : p.rel 1 (m * b) := hm
            have h2 : p.rel (m * b) r := hr
            have h3 : p.rel 1 r := p.trans _ _ _ h1 h2
            rw [← Nat.cast_one] at h3
            have hnat := (p.nat_compat 1 r).mpr h3
            exact Nat.one_le_cast.mpr hnat
          calc (1 : ℝ) = 1 ^ (1 / (n : ℝ)) := by simp
            _ ≤ (r : ℝ) ^ (1 / (n : ℝ)) := by
                apply Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hr_ge1
                apply div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg n)

/-- Sum of terms bounded in the Strassen preorder is bounded -/
lemma StrassenPreorder.sum_rel (p : StrassenPreorder S) {ι : Type*} (s : Finset ι)
    (f g : ι → S) (h : ∀ i ∈ s, p.rel (f i) (g i)) : p.rel (s.sum f) (s.sum g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact p.refl 0
  | @insert a s' ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    apply p.add_mono_both
    · exact h a (Finset.mem_insert_self a s')
    · apply ih
      intro i hi
      exact h i (Finset.mem_insert_of_mem hi)

/-- The asymptotic preorder associated to p -/
def asympPreorder (p : StrassenPreorder S) : StrassenPreorder S where
  rel := AsympRel p
  refl := AsympRel.refl
  trans := fun a b c hab hbc => AsympRel.trans hab hbc
  zero_le := fun a => AsympRel.of_le (p.zero_le a)
  nat_compat := by
    intro n m
    constructor
    · intro hnm
      exact AsympRel.of_le ((p.nat_compat n m).mp hnm)
    · intro hasymp
      by_contra hlt
      push_neg at hlt
      obtain ⟨x, hx_rel, hx_lim⟩ := hasymp
      have h1 := hx_rel 1 (le_refl 1)
      simp only [pow_one] at h1
      have hnat : (n : ℕ) ≤ m * x 1 := by
        have h2 : p.rel (n : S) ((m : S) * (x 1 : S)) := h1
        have h3 : (m : S) * (x 1 : S) = ((m * x 1 : ℕ) : S) := by simp [Nat.cast_mul]
        rw [h3] at h2
        exact (p.nat_compat n (m * x 1)).mpr h2
      by_cases hm0 : m = 0
      · have hn_pos : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
          (Nat.lt_of_le_of_lt (Nat.zero_le m) hlt))
        subst hm0
        have h1' := hx_rel 1 (le_refl 1)
        simp only [pow_one, Nat.cast_zero, zero_mul] at h1'
        have hcontra : (n : ℕ) ≤ 0 := by
          have h1'' : p.rel (n : S) ((0 : ℕ) : S) := by convert h1' using 2; simp
          exact (p.nat_compat n 0).mpr h1''
        omega
      · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
        have hn_pos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le m) hlt
        have hratio : 1 < (n : ℝ) / m := by
          rw [one_lt_div₀ (Nat.cast_pos.mpr hm_pos)]
          exact Nat.cast_lt.mpr hlt
        set r := (n : ℝ) / m with hr_def
        have hr_pos : 0 < r := by positivity
        have heps : 0 < r - 1 := by linarith
        have hsInf := hx_lim
        have hnear : ∃ k, k ≥ 1 ∧ (x k : ℝ) ^ (1 / (k : ℝ)) < r := by
          have hlt_r : sInf ((fun n => (x n : ℝ) ^ (1 / n : ℝ)) '' {n : ℕ | 1 ≤ n}) < r := by
            rw [hsInf]; exact hratio
          have hne : ((fun n => (x n : ℝ) ^ (1 / n : ℝ)) '' {n : ℕ | 1 ≤ n}).Nonempty :=
            ⟨_, ⟨1, Nat.le_refl 1, rfl⟩⟩
          obtain ⟨y, hy_mem, hy_lt⟩ := exists_lt_of_csInf_lt hne hlt_r
          obtain ⟨k, hk_ge, rfl⟩ := hy_mem
          exact ⟨k, hk_ge, hy_lt⟩
        obtain ⟨k, hk_ge, hxk_lt⟩ := hnear
        have hk_ne : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk_ge
        have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk_ne)
        have hxk_lt' : (x k : ℝ) < r ^ k := by
          have h2 : ((x k : ℝ) ^ (1 / (k : ℝ))) ^ (k : ℝ) < r ^ (k : ℝ) := by
            apply Real.rpow_lt_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) hxk_lt hk_pos
          rw [← Real.rpow_mul (Nat.cast_nonneg _), one_div, inv_mul_cancel₀ (ne_of_gt hk_pos),
              Real.rpow_one, Real.rpow_natCast] at h2
          exact h2
        have hrel := hx_rel k hk_ge
        have hm_pow_pos : (0 : ℝ) < (m : ℝ) ^ k := by positivity
        have hnat' : (n : ℕ) ^ k ≤ m ^ k * x k := by
          have h' : p.rel ((n ^ k : ℕ) : S) ((m ^ k * x k : ℕ) : S) := by
            simp only [Nat.cast_pow, Nat.cast_mul] at hrel ⊢
            convert hrel using 2
          exact (p.nat_compat (n ^ k) (m ^ k * x k)).mpr h'
        have hbound : r ^ k ≤ (x k : ℝ) := by
          calc r ^ k = ((n : ℝ) / m) ^ k := by rfl
            _ = (n : ℝ) ^ k / (m : ℝ) ^ k := by rw [div_pow]
            _ ≤ (x k : ℝ) := by
                rw [div_le_iff₀ hm_pow_pos]
                calc (n : ℝ) ^ k = ((n ^ k : ℕ) : ℝ) := by push_cast; ring
                  _ ≤ ((m ^ k * x k : ℕ) : ℝ) := by exact mod_cast hnat'
                  _ = (x k : ℝ) * (m : ℝ) ^ k := by push_cast; ring
        linarith
  add_mono := by
    intro a b s hab
    obtain ⟨x, hx_rel, hx_lim⟩ := hab
    -- First prove x n ≥ 1 for n ≥ 1 (from sInf = 1)
    have hx_ge1 : ∀ n, n ≥ 1 → x n ≥ 1 := by
      intro n hn
      by_contra h_neg
      push_neg at h_neg
      -- x n < 1 for ℕ means x n = 0
      have hxn0 : x n = 0 := by omega
      -- x n = 0 means (x n : ℝ)^{1/n} = 0, so sInf ≤ 0 < 1, contradiction
      have hn_pos : (1 : ℝ) / n ≠ 0 := by positivity
      have h0_mem : (0 : ℝ) ∈ ((fun m => (x m : ℝ) ^ (1 / (m : ℝ))) '' {m : ℕ | 1 ≤ m}) :=
        ⟨n, hn, by simp only [hxn0, Nat.cast_zero, Real.zero_rpow hn_pos]⟩
      have hbdd : BddBelow ((fun m => (x m : ℝ) ^ (1 / (m : ℝ))) '' {m : ℕ | 1 ≤ m}) := by
        use 0; intro c hc; obtain ⟨k, _, rfl⟩ := hc; positivity
      have hsInf_le : sInf ((fun m => (x m : ℝ) ^ (1 / (m : ℝ))) '' {m : ℕ | 1 ≤ m}) ≤ 0 :=
        csInf_le hbdd h0_mem
      linarith
    -- Use submultClosure for the witness (submultiplicative, same sInf, Fekete applies)
    let x' := submultClosure x
    have hx'_rel : ∀ n, n ≥ 1 → p.rel (a ^ n) (b ^ n * x' n) :=
      submultClosure_bound p a b x hx_rel
    have hx'_lim : sInf ((fun n => (x' n : ℝ) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n}) = 1 :=
      submultClosure_sInf_eq_one_of x hx_ge1 hx_lim
    have hx'_ge1 : ∀ n, n ≥ 1 → x' n ≥ 1 := submultClosure_ge_one x hx_ge1
    -- Witness: y_n = max(1, x'_1, ..., x'_n) for n ≥ 1
    let y : ℕ → ℕ := fun n => if n = 0 then 1 else Finset.sup' (Finset.range (n + 1))
        (by simp only [Finset.nonempty_range_iff]; omega)
        (fun k => if k = 0 then 1 else x' k)
    refine ⟨y, ?_, ?_⟩
    · -- Bound: (a+s)^n ≤ (b+s)^n * y_n via binomial expansion
      intro n hn
      have hn_ne : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
      let f : ℕ → ℕ := fun i => if i = 0 then 1 else x' i
      -- y_n ≥ 1
      have hy_ge_1 : 1 ≤ y n := by
        simp only [y, hn_ne, ↓reduceIte]
        have h0_mem : 0 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
        calc 1 = f 0 := by simp [f]
          _ ≤ _ := Finset.le_sup' f h0_mem
      -- x'_m ≤ y_n for all m ∈ [1, n]
      have hxm_le : ∀ m, 1 ≤ m → m ≤ n → x' m ≤ y n := by
        intro m hm_ge hm_le
        simp only [y, hn_ne, ↓reduceIte]
        have hm_mem : m ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
        have hm_ne : m ≠ 0 := Nat.one_le_iff_ne_zero.mp hm_ge
        calc x' m = f m := by simp [f, hm_ne]
          _ ≤ _ := Finset.le_sup' f hm_mem
      -- Use binomial expansion and compare termwise
      rw [add_pow a s n, add_pow b s n]
      have hfactor : (Finset.range (n + 1)).sum (fun m => b ^ m * s ^ (n - m) * (n.choose m)) *
          (y n : S) = (Finset.range (n + 1)).sum
          (fun m => b ^ m * s ^ (n - m) * (n.choose m) * (y n : S)) := by rw [Finset.sum_mul]
      rw [hfactor]
      apply p.sum_rel
      intro m hm
      simp only [Finset.mem_range] at hm
      by_cases hm0 : m = 0
      · -- m = 0 case: s^n ≤ s^n * y_n since y_n ≥ 1
        subst hm0
        simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
        have hrel : p.rel (1 : S) (y n : S) := by
          rw [← Nat.cast_one]; exact (p.nat_compat 1 (y n)).mp hy_ge_1
        have h := p.mul_mono 1 (y n : S) (s ^ n) hrel
        simp only [one_mul] at h; rw [mul_comm] at h; exact h
      · -- m ≥ 1 case: a^m * stuff ≤ b^m * x'_m * stuff ≤ b^m * y_n * stuff
        have hm_ge : m ≥ 1 := Nat.one_le_iff_ne_zero.mpr hm0
        have hm_le : m ≤ n := by omega
        have ha_bound := hx'_rel m hm_ge
        have hxm := hxm_le m hm_ge hm_le
        have hxm_rel : p.rel (x' m : S) (y n : S) := (p.nat_compat (x' m) (y n)).mp hxm
        have h1 : p.rel (a ^ m * (s ^ (n - m) * (n.choose m)))
            (b ^ m * (x' m : S) * (s ^ (n - m) * (n.choose m))) :=
          p.mul_mono _ _ _ ha_bound
        have h2 : p.rel (b ^ m * (x' m : S) * (s ^ (n - m) * (n.choose m)))
                        (b ^ m * (y n : S) * (s ^ (n - m) * (n.choose m))) := by
          have := p.mul_mono (x' m : S) (y n : S) (b ^ m) hxm_rel
          rw [mul_comm (x' m : S) (b ^ m), mul_comm (y n : S) (b ^ m)] at this
          exact p.mul_mono _ _ _ this
        have htrans := p.trans _ _ _ h1 h2
        have eq1 : a ^ m * s ^ (n - m) * (n.choose m) =
            a ^ m * (s ^ (n - m) * (n.choose m)) := by ring
        have eq2 : b ^ m * s ^ (n - m) * (n.choose m) * (y n : S) =
                   b ^ m * (y n : S) * (s ^ (n - m) * (n.choose m)) := by ring
        rw [eq1, eq2]; exact htrans
    · -- sInf(y^{1/n}) = 1
      -- Strategy: sInf ≥ 1 since y_n ≥ 1, and sInf ≤ 1 by showing y_n^{1/n} → 1
      let f : ℕ → ℕ := fun i => if i = 0 then 1 else x' i
      apply le_antisymm
      · -- sInf ≤ 1: Use Tendsto to show values get arbitrarily close to 1
        -- Key: x' is submultiplicative, so Fekete's lemma gives lim = sInf = 1.
        -- The monotone envelope y_n of x' inherits convergence: y_n^{1/n} → 1.
        -- Key insight: x' is submultiplicative with sInf = 1, so by Fekete, x'^{1/n} → 1.
        -- The monotone envelope y_n = max{x'_k : k ≤ n} satisfies y^{1/n} → 1 as well.
        have htendsto : Filter.Tendsto (fun n : ℕ => (y n : ℝ) ^ (1 / (n : ℝ)))
            Filter.atTop (nhds 1) := by
          -- By Fekete, x' has Tendsto (x'^{1/n}) → 1 (since x' submultiplicative, sInf = 1)
          have hx'_submult := submultClosure_submult x
          have hx'_ge1_all : ∀ n, 1 ≤ (x' n : ℝ) := by
            intro n
            rcases Nat.eq_or_lt_of_le (Nat.zero_le n) with hn | hn
            · subst hn; simp only [x', submultClosure_zero, Nat.cast_one]; exact le_rfl
            · exact Nat.one_le_cast.mpr (hx'_ge1 n hn)
          have hx'_submult_cast : ∀ n m, (x' (n + m) : ℝ) ≤ (x' n : ℝ) * (x' m : ℝ) := by
            intro n m
            rcases Nat.eq_or_lt_of_le (Nat.zero_le n) with hn | hn
            · subst hn
              simp only [zero_add, x', submultClosure_zero, Nat.cast_one, one_mul]
              exact le_rfl
            · rcases Nat.eq_or_lt_of_le (Nat.zero_le m) with hm | hm
              · subst hm
                simp only [add_zero, x', submultClosure_zero, Nat.cast_one, mul_one]
                exact le_rfl
              · exact_mod_cast Nat.cast_le.mpr (hx'_submult n m hn hm)
          have hfekete := fekete_multiplicative hx'_ge1_all hx'_submult_cast
          rw [hx'_lim] at hfekete
          -- y is the monotone envelope of x'. Apply monotoneEnvelope_tendsto.
          -- Note: y n = monotoneEnvelope x' n by definition
          have hy_eq : ∀ n, y n = monotoneEnvelope x' n := by
            intro n
            simp only [y, monotoneEnvelope]
          simp_rw [hy_eq]
          exact monotoneEnvelope_tendsto x' hx'_ge1 hfekete
        have hbdd : BddBelow ((fun n => (y n : ℝ) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n}) := by
          use 0; intro c hc; obtain ⟨n, _, rfl⟩ := hc
          apply Real.rpow_nonneg (Nat.cast_nonneg _)
        rw [csInf_le_iff hbdd ⟨_, ⟨1, Nat.le_refl 1, rfl⟩⟩]
        intro b hb
        by_contra h_neg
        push_neg at h_neg
        have heps : 0 < b - 1 := by linarith
        have := htendsto.eventually (Metric.ball_mem_nhds 1 heps)
        simp only [Real.dist_eq] at this
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp this
        set M := max N 1 with hM_def
        have hM_ge : M ≥ 1 := le_max_right _ _
        specialize hN M (le_max_left _ _)
        have hb_le : b ≤ (y M : ℝ) ^ (1 / (M : ℝ)) := hb ⟨M, hM_ge, rfl⟩
        have h_bound := abs_sub_lt_iff.mp hN
        linarith
      · -- sInf ≥ 1: Since y_n ≥ 1, we have y_n^{1/n} ≥ 1
        have hne : ((fun n => (y n : ℝ) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n}).Nonempty :=
          ⟨_, ⟨1, Nat.le_refl 1, rfl⟩⟩
        apply le_csInf hne
        intro c hc
        obtain ⟨n, hn, rfl⟩ := hc
        have hn_ne : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
        have hy_ge : 1 ≤ y n := by
          simp only [y, hn_ne, ↓reduceIte]
          have h0_mem : 0 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
          calc 1 = f 0 := by simp [f]
            _ ≤ _ := Finset.le_sup' f h0_mem
        apply Real.one_le_rpow (mod_cast hy_ge)
        positivity
  mul_mono := by
    intro a b s hab
    obtain ⟨x, hx_rel, hx_lim⟩ := hab
    refine ⟨x, ?_, hx_lim⟩
    intro n hn
    have h := hx_rel n hn
    have h1 : p.rel (a ^ n * s ^ n) (b ^ n * x n * s ^ n) := p.mul_mono _ _ (s ^ n) h
    have eq1 : a ^ n * s ^ n = (a * s) ^ n := (mul_pow a s n).symm
    have eq2 : b ^ n * (x n : S) * s ^ n = (b * s) ^ n * (x n : S) := by
      rw [mul_pow b s n]; ring
    rw [eq1, eq2] at h1
    exact h1
  archimedean := by
    intro a b hb
    obtain ⟨r, hr⟩ := p.archimedean a b hb
    exact ⟨r, AsympRel.of_le hr⟩

/-- Lemma str_props (iii): (≲)≲ = ≲.
    That is, the asymptotic preorder is idempotent.
    Proof uses diagonal argument following Strassen (1988):
    If a ≲≲ b, then a^{NM} ≤ b^{NM} * x_N^M * y_{N,M}.
    Choose M_N such that y_{N,M_N}^{1/M_N} ≤ 2.
    Then (x_N^{M_N} * y_{N,M_N})^{1/(NM_N)} = x_N^{1/N} * 2^{1/N} → 1. -/
theorem asymp_asymp_eq_asymp (p : StrassenPreorder S) :
    AsympRel (asympPreorder p) = AsympRel p := by
  ext a b
  constructor
  · intro h
    obtain ⟨x, hx_rel, hx_lim⟩ := h
    have hinner : ∀ N, N ≥ 1 → ∃ y : ℕ → ℕ,
        (∀ M, M ≥ 1 → p.rel (a ^ (N * M)) (b ^ (N * M) * x N ^ M * y M)) ∧
        sInf ((fun m => (y m : ℝ) ^ (1 / m : ℝ)) '' {m : ℕ | 1 ≤ m}) = 1 := by
      intro N hN
      have hr := hx_rel N hN
      obtain ⟨y, hy_rel, hy_lim⟩ := hr
      refine ⟨y, ?_, hy_lim⟩
      intro M hM
      have hyM := hy_rel M hM
      simp only [← pow_mul] at hyM ⊢
      have eq1 : (b ^ N * (x N : S)) ^ M = b ^ (N * M) * (x N : S) ^ M := by
        rw [mul_pow, pow_mul]
      rw [eq1] at hyM
      exact hyM
    by_cases hb : b = 0
    · subst hb
      use fun _ => 1
      constructor
      · intro n hn
        have haN := hx_rel n hn
        obtain ⟨z, hz_rel, _⟩ := haN
        have h1 := hz_rel 1 (le_refl 1)
        have hn' : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
        simp only [pow_one, zero_pow hn', zero_mul] at h1
        simp only [Nat.cast_one, mul_one, zero_pow hn']
        exact h1
      · have himg : (fun n : ℕ => ((1 : ℕ) : ℝ) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n} = {1} := by
          ext x
          simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
          constructor
          · rintro ⟨n, _, rfl⟩
            simp only [Nat.cast_one, Real.one_rpow]
          · intro hx
            exact ⟨1, Nat.le_refl 1, by simp [hx]⟩
        rw [himg]
        exact csInf_singleton 1
    · obtain ⟨C, hC⟩ := p.archimedean a b hb
      -- Following tex proof: use diagonal argument.
      -- For each N ≥ 1, find M_N such that (y_N)_{M_N}^{1/M_N} ≤ 2.
      -- Then z at index N*M_N = x_N^{M_N} * y_{N,M_N} has z^{1/(N*M_N)} → 1.

      -- Step 1: For each N ≥ 1, find M_N with (y_N)_M^{1/M} ≤ 2
      have hM_exists : ∀ N (hN : N ≥ 1), ∃ M, M ≥ 1 ∧
          ((hinner N hN).choose M : ℝ) ^ (1 / (M : ℝ)) ≤ 2 := by
        intro N hN
        let y := (hinner N hN).choose
        have hy_lim := (hinner N hN).choose_spec.2
        -- sInf = 1 < 2, so ∃ M ≥ 1 with y_M^{1/M} < 2
        -- Use: sInf + 1 = 2, and Real.lt_sInf_add_pos gives element < sInf + 1
        have hbdd : BddBelow ((fun m => (y m : ℝ) ^ (1 / (m : ℝ))) '' {m : ℕ | 1 ≤ m}) := by
          use 0; intro c hc; obtain ⟨k, _, rfl⟩ := hc; positivity
        have hne : ((fun m => (y m : ℝ) ^ (1 / (m : ℝ))) '' {m : ℕ | 1 ≤ m}).Nonempty :=
          ⟨(y 1 : ℝ) ^ (1 / (1 : ℝ)), ⟨1, Nat.le_refl 1, by simp⟩⟩
        have hex := Real.lt_sInf_add_pos hne (by norm_num : (0 : ℝ) < 1)
        -- hex : ∃ a ∈ set, a < sInf set + 1. Since sInf = 1, this gives a < 2.
        obtain ⟨v, hv_mem, hv_lt⟩ := hex
        obtain ⟨M, hM_ge1, hM_eq⟩ := hv_mem
        refine ⟨M, hM_ge1, ?_⟩
        -- Goal: (y M)^(1/M) ≤ 2. We have hM_eq: (y M)^(1/M) = v and v < 2.
        rw [hy_lim] at hv_lt
        have hv_lt2 : v < 2 := by linarith
        calc ((hinner N hN).choose M : ℝ) ^ (1 / (M : ℝ))
            = (y M : ℝ) ^ (1 / (M : ℝ)) := by rfl
          _ = v := hM_eq
          _ ≤ 2 := le_of_lt hv_lt2

      -- Step 2: Define M_N for each N
      let M_of : ∀ N, N ≥ 1 → ℕ := fun N hN => (hM_exists N hN).choose
      have hM_ge1 : ∀ N hN, M_of N hN ≥ 1 := fun N hN => (hM_exists N hN).choose_spec.1
      have hM_bound : ∀ N hN,
          ((hinner N hN).choose (M_of N hN) : ℝ) ^ (1 / ((M_of N hN) : ℝ)) ≤ 2 :=
        fun N hN => (hM_exists N hN).choose_spec.2

      -- Step 3: Define the witness using the DIAGONAL: at index N*M_N, use
      -- x_N^{M_N} * y_{N,M_N}. For non-diagonal indices, use the factorization k = k*1.
      -- Key insight: witness only needs sInf = 1, not that every z_k^{1/k} → 1.
      -- The diagonal indices provide sInf ≤ 1, and z_k ≥ 1 gives sInf ≥ 1.

      -- Define z using the MINIMUM over factorizations.
      -- For each k ≥ 1, z_k = min { x_n^m * y_{n,m} | n*m = k, n ≥ 1, m ≥ 1 }
      -- This ensures:
      -- 1. The bound holds: min is attained at some factorization
      -- 2. sInf = 1: at diagonal k = N*M_N, z_k ≤ diagonal value, diagonal → 1

      -- Helper: compute the value at a factorization (n, m) where n divides k and m = k/n
      let factorVal : (k : ℕ) → (n : ℕ) → (hn : n ∈ k.divisors) → ℕ := fun k n hn =>
        let m := k / n
        -- n ∈ k.divisors means n ∣ k and k ≠ 0, so n ≥ 1
        have hdiv : n ∣ k ∧ k ≠ 0 := Nat.mem_divisors.mp hn
        have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr
          (fun h => hdiv.2 (Nat.eq_zero_of_zero_dvd (h ▸ hdiv.1)))
        x n ^ m * (hinner n hn1).choose m

      -- The witness z using Finset.min' over all factorizations
      let z : ℕ → ℕ := fun k =>
        if hk : k ≥ 1 then
          -- k.divisors is nonempty since k ≥ 1 (it contains 1 and k)
          have hne : k.divisors.Nonempty := Nat.nonempty_divisors.mpr (Nat.one_le_iff_ne_zero.mp hk)
          -- Use attach to carry membership proofs, then image to get values
          let valsAttach := k.divisors.attach.image (fun ⟨n, hn⟩ => factorVal k n hn)
          have hne' : valsAttach.Nonempty := by
            rw [Finset.image_nonempty, Finset.attach_nonempty_iff]
            exact hne
          valsAttach.min' hne'
        else 1

      use z
      constructor
      · -- Prove the bound: a^n ≤ b^n * z_n
        -- z_n is the min over factorizations (d, n/d) of x_d^(n/d) * y_{d, n/d}
        -- The min is attained at some factorization, and that factorization satisfies the bound
        intro n hn
        simp only [z, hn, dite_true]

        have hne : n.divisors.Nonempty := Nat.nonempty_divisors.mpr (Nat.one_le_iff_ne_zero.mp hn)
        let valsAttach := n.divisors.attach.image (fun ⟨d, hd⟩ => factorVal n d hd)
        have hne' : valsAttach.Nonempty := by
          rw [Finset.image_nonempty, Finset.attach_nonempty_iff]
          exact hne

        -- The min is achieved at some element
        have hmin_mem : valsAttach.min' hne' ∈ valsAttach := Finset.min'_mem _ hne'
        rw [Finset.mem_image] at hmin_mem
        obtain ⟨⟨d, hd_mem⟩, _, hmin_eq⟩ := hmin_mem

        -- Get the bound from inner witness at index d
        have hdiv : d ∣ n ∧ n ≠ 0 := Nat.mem_divisors.mp hd_mem
        have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr
          (fun h => hdiv.2 (Nat.eq_zero_of_zero_dvd (h ▸ hdiv.1)))
        have hd_pos : 0 < d := Nat.one_le_iff_ne_zero.mp hd1 |> Nat.pos_of_ne_zero
        let m := n / d
        have hm1 : 1 ≤ m := Nat.one_le_div_iff hd_pos |>.mpr
          (Nat.le_of_dvd (Nat.pos_of_ne_zero hdiv.2) hdiv.1)
        have hnm : d * m = n := Nat.mul_div_cancel' hdiv.1

        -- Inner witness y at index d gives: p.rel (a^(d*m)) (b^(d*m) * x d ^ m * y_d m)
        have hy := (hinner d hd1).choose_spec
        have hy_rel := hy.1 m hm1

        -- factorVal n d hd_mem = x d ^ m * y_d m
        have hfv : (⟨d, hd_mem⟩ : n.divisors).1 = d := rfl
        simp only [] at hmin_eq
        -- Rewrite using d * m = n
        have hpow_a : a ^ n = a ^ (d * m) := by rw [← hnm]
        have hpow_b : b ^ n = b ^ (d * m) := by rw [← hnm]

        have hfv2 : factorVal n d hd_mem = x d ^ m * (hinner d hd1).choose m := by
          simp only [factorVal, m]

        rw [← hmin_eq, hfv2]
        have hcast : (b ^ n : S) * ((x d ^ m * (hinner d hd1).choose m : ℕ) : S) =
                     b ^ (d * m) * (x d : S) ^ m * ((hinner d hd1).choose m : S) := by
          rw [← hnm]; simp only [Nat.cast_mul, Nat.cast_pow]; ring
        rw [hpow_a, hcast]
        exact hy_rel

      · -- Prove sInf(z^{1/k}) = 1 using the diagonal argument from Strassen (tex lines 577-589).
        -- PROOF OUTLINE:
        -- Lower bound (sInf ≥ 1): z_k ≥ 1 for all k, so z_k^{1/k} ≥ 1
        -- Upper bound (sInf ≤ 1): At diagonal k = N*M_N:
        --   z_k ≤ x_N^{M_N} * y_{N,M_N}, so
        --   z_k^{1/k} ≤ x_N^{1/N} * (y_{N,M_N}^{1/M_N})^{1/N} ≤ x_N^{1/N} * 2^{1/N} → 1
        --
        -- Technical steps (each uses standard analysis):
        -- 1. sInf(x^{1/n}) = 1 implies ∃ N₁ with x_{N₁}^{1/N₁} < 1 + ε/2
        -- 2. sInf(2^{1/n}) = 1 implies ∃ N₂ with 2^{1/N₂} < 1 + ε/2
        -- 3. At k = N*M where N = max(N₁, N₂): z_k^{1/k} < (1+ε/2)² < 1+ε
        -- 4. z_k ≥ 1 follows from x_d, y_{d,m} ≥ 1 (each has sInf = 1 ≥ 1)
        apply le_antisymm

        -- Upper bound (sInf ≤ 1):
        · apply le_of_forall_pos_lt_add
          intro ε hε
          -- From hx_lim (sInf = 1), find N₁ with x_{N₁}^{1/N₁} < 1 + ε/4
          have hx_set_ne : ((fun n => (x n : ℝ) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n}).Nonempty :=
            ⟨(x 1 : ℝ) ^ 1, 1, Nat.le_refl 1, by simp⟩
          have hex := Real.lt_sInf_add_pos hx_set_ne (by linarith : (0 : ℝ) < ε / 4)
          rw [hx_lim] at hex
          obtain ⟨v, ⟨N₁, hN₁_ge1, hN₁_eq⟩, hv_lt⟩ := hex
          -- v = x_{N₁}^{1/N₁} < 1 + ε/4

          -- APPROACH: Split on ε to use appropriate bounds.
          -- For ε ≥ 2: use M_of (with y^{1/M} ≤ 2), bound (1+ε/4)*2 ≤ 1+ε
          -- For ε < 2: use M from ε/4 sInf (with y^{1/M} < 1+ε/4), bound (1+ε/4)² < 1+ε

          -- Use N = N₁ from the ε/4 bound (always works)
          let N := N₁
          have hN_ge1 : N ≥ 1 := hN₁_ge1

          -- x_N^{1/N} < 1 + ε/4
          have hx_N_bound : (x N : ℝ) ^ (1 / (N : ℝ)) < 1 + ε / 4 := by
            have : (x N : ℝ) ^ (1 / (N : ℝ)) = v := hN₁_eq
            rw [this]; exact hv_lt

          have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero
              (Nat.one_le_iff_ne_zero.mp hN_ge1))

          -- Common helper: y witness set is nonempty
          have hy_set_ne : ((fun m => ((hinner N hN_ge1).choose m : ℝ) ^ (1 / (m : ℝ))) ''
              {m : ℕ | 1 ≤ m}).Nonempty :=
            ⟨((hinner N hN_ge1).choose 1 : ℝ) ^ 1, 1, Nat.le_refl 1, by simp⟩
          have hy_lim : sInf ((fun m => ((hinner N hN_ge1).choose m : ℝ) ^ (1 / (m : ℝ))) ''
              {m : ℕ | 1 ≤ m}) = 1 := (hinner N hN_ge1).choose_spec.2

          -- x_N ≥ 1 (from sInf = 1)
          have hx_ge1 : x N ≥ 1 := by
            by_contra hc; push_neg at hc
            have hxn0 : x N = 0 := Nat.lt_one_iff.mp hc
            have hmem' : (x N : ℝ) ^ (1 / (N : ℝ)) ∈
                (fun j => (x j : ℝ) ^ (1 / (j : ℝ))) '' {j : ℕ | 1 ≤ j} := ⟨N, hN_ge1, rfl⟩
            have hbdd' : BddBelow ((fun j => (x j : ℝ) ^ (1 / (j : ℝ))) '' {j : ℕ | 1 ≤ j}) := by
              use 0; intro c hc'; obtain ⟨m, _, rfl⟩ := hc'; positivity
            have hge := csInf_le hbdd' hmem'
            rw [hx_lim] at hge
            have h1_div_ne : 1 / (N : ℝ) ≠ 0 := one_div_ne_zero (ne_of_gt hN_pos)
            have h0_rpow : (0 : ℝ) ^ (1 / (N : ℝ)) = 0 := Real.zero_rpow h1_div_ne
            simp only [hxn0, Nat.cast_zero, h0_rpow] at hge
            linarith

          have hx_pos : (0 : ℝ) < x N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero
              (Nat.one_le_iff_ne_zero.mp hx_ge1))

          -- Split on ε to choose appropriate M
          by_cases hε2 : ε ≥ 2
          · -- Case ε ≥ 2: Use M_of with y^{1/M} ≤ 2
            let M := M_of N hN_ge1
            have hM1 : M ≥ 1 := hM_ge1 N hN_ge1
            have hy_M_le2 : ((hinner N hN_ge1).choose M : ℝ) ^ (1 / (M : ℝ)) ≤ 2 :=
              hM_bound N hN_ge1

            let k := N * M
            have hk_ge1 : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
                (Nat.one_le_iff_ne_zero.mp hN_ge1) (Nat.one_le_iff_ne_zero.mp hM1))

            have hmem : (z k : ℝ) ^ (1 / (k : ℝ)) ∈
                (fun j => (z j : ℝ) ^ (1 / (j : ℝ))) '' {j : ℕ | 1 ≤ j} := ⟨k, hk_ge1, rfl⟩
            have hbdd : BddBelow ((fun j => (z j : ℝ) ^ (1 / (j : ℝ))) '' {j : ℕ | 1 ≤ j}) := by
              use 0; intro c hc; obtain ⟨m, _, rfl⟩ := hc; positivity

            have hM_pos : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero
                (Nat.one_le_iff_ne_zero.mp hM1))
            have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero
                (Nat.one_le_iff_ne_zero.mp hk_ge1))

            -- z_k ≤ x_N^M * y_{N,M}
            have hz_le : z k ≤ x N ^ M * (hinner N hN_ge1).choose M := by
              have hdiv : N ∣ k ∧ k ≠ 0 := ⟨⟨M, rfl⟩, Nat.mul_ne_zero
                  (Nat.one_le_iff_ne_zero.mp hN_ge1) (Nat.one_le_iff_ne_zero.mp hM1)⟩
              have hN_mem : N ∈ k.divisors := Nat.mem_divisors.mpr hdiv
              have hm_eq : k / N = M := Nat.mul_div_cancel_left M
                  (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hN_ge1))
              simp only [z, dif_pos hk_ge1]
              apply Finset.min'_le
              simp only [Finset.mem_image]
              use ⟨N, hN_mem⟩
              constructor
              · exact Finset.mem_attach _ _
              · simp only [factorVal, hm_eq]

            -- z_k^{1/k} ≤ x_N^{1/N} * (y^{1/M})^{1/N}
            -- Use abbreviation for the long witness expression
            set y_N_M := (hinner N hN_ge1).choose M with hy_def
            have hz_rpow_le : (z k : ℝ) ^ (1 / (k : ℝ)) ≤
                (x N : ℝ) ^ (1 / (N : ℝ)) *
                  ((y_N_M : ℝ) ^ (1 / (M : ℝ))) ^ (1 / (N : ℝ)) := by
              have hcast : ((x N ^ M * y_N_M : ℕ) : ℝ) =
                  (x N : ℝ) ^ M * (y_N_M : ℝ) := by
                simp [Nat.cast_mul, Nat.cast_pow]
              calc (z k : ℝ) ^ (1 / (k : ℝ))
                  ≤ ((x N ^ M * y_N_M : ℕ) : ℝ) ^ (1 / (k : ℝ)) := by
                      apply Real.rpow_le_rpow (Nat.cast_nonneg _)
                        (Nat.cast_le.mpr hz_le)
                      exact div_nonneg (by norm_num) (le_of_lt hk_pos)
                _ = ((x N : ℝ) ^ M * (y_N_M : ℝ)) ^ (1 / (k : ℝ)) := by
                    rw [hcast]
                _ = (x N : ℝ) ^ ((M : ℝ) / (k : ℝ)) *
                    (y_N_M : ℝ) ^ (1 / (k : ℝ)) := by
                    rw [Real.mul_rpow (pow_nonneg (Nat.cast_nonneg _) _)
                      (Nat.cast_nonneg _)]
                    congr 1
                    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
                    ring_nf
                _ = (x N : ℝ) ^ (1 / (N : ℝ)) * (y_N_M : ℝ) ^ (1 / (k : ℝ)) := by
                    congr 1
                    have hk_eq : (k : ℝ) = (N : ℝ) * (M : ℝ) := by
                      simp [k, Nat.cast_mul]
                    rw [hk_eq]; field_simp
                _ = (x N : ℝ) ^ (1 / (N : ℝ)) *
                    ((y_N_M : ℝ) ^ (1 / (M : ℝ))) ^ (1 / (N : ℝ)) := by
                    congr 1; rw [← Real.rpow_mul (Nat.cast_nonneg _)]; congr 1
                    have hk_eq : (k : ℝ) = (N : ℝ) * (M : ℝ) := by
                      simp [k, Nat.cast_mul]
                    rw [hk_eq]; field_simp

            -- (y^{1/M})^{1/N} ≤ 2 since y^{1/M} ≤ 2 and N ≥ 1
            have hy_rpow_le2 :
                ((y_N_M : ℝ) ^ (1 / (M : ℝ))) ^ (1 / (N : ℝ)) ≤ 2 := by
              have hN_ge1_real : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN_ge1
              have hexp_le1 : 1 / (N : ℝ) ≤ 1 := by
                rw [div_le_one hN_pos]; exact hN_ge1_real
              have hbase_ge1 : (1 : ℝ) ≤ (y_N_M : ℝ) ^ (1 / (M : ℝ)) := by
                have hmem' : (y_N_M : ℝ) ^ (1 / (M : ℝ)) ∈
                    (fun m => ((hinner N hN_ge1).choose m : ℝ) ^
                      (1 / (m : ℝ))) '' {m : ℕ | 1 ≤ m} :=
                  ⟨M, hM1, rfl⟩
                have hbdd' : BddBelow ((fun m =>
                    ((hinner N hN_ge1).choose m : ℝ) ^
                      (1 / (m : ℝ))) '' {m : ℕ | 1 ≤ m}) := by
                  use 0; intro c hc'; obtain ⟨m, _, rfl⟩ := hc'; positivity
                have hge := csInf_le hbdd' hmem'
                rw [hy_lim] at hge; linarith
              calc (((hinner N hN_ge1).choose M : ℝ) ^ (1 / (M : ℝ))) ^ (1 / (N : ℝ))
                  ≤ (((hinner N hN_ge1).choose M : ℝ) ^ (1 / (M : ℝ))) ^ (1 : ℝ) := by
                    apply Real.rpow_le_rpow_of_exponent_le hbase_ge1 hexp_le1
                _ = ((hinner N hN_ge1).choose M : ℝ) ^ (1 / (M : ℝ)) := Real.rpow_one _
                _ ≤ 2 := hy_M_le2

            calc sInf _ ≤ (z k : ℝ) ^ (1 / (k : ℝ)) := csInf_le hbdd hmem
              _ ≤ (x N : ℝ) ^ (1 / (N : ℝ)) *
                  (((hinner N hN_ge1).choose M : ℝ) ^ (1 / (M : ℝ))) ^ (1 / (N : ℝ)) := hz_rpow_le
              _ ≤ (x N : ℝ) ^ (1 / (N : ℝ)) * 2 := by
                  apply mul_le_mul_of_nonneg_left hy_rpow_le2
                  exact le_of_lt (Real.rpow_pos_of_pos hx_pos _)
              _ < (1 + ε / 4) * 2 := by
                  apply mul_lt_mul_of_pos_right hx_N_bound (by norm_num : (0:ℝ) < 2)
              _ ≤ 1 + ε := by linarith  -- (1+ε/4)*2 = 2+ε/2 ≤ 1+ε iff ε ≥ 2

          · -- Case ε < 2: Use M from ε/4 sInf bound with y^{1/M} < 1+ε/4
            push_neg at hε2
            have hy_ex := Real.lt_sInf_add_pos hy_set_ne (by linarith : (0 : ℝ) < ε / 4)
            rw [hy_lim] at hy_ex
            obtain ⟨_, ⟨M, hM_ge1, hM_eq⟩, hM_lt⟩ := hy_ex

            have hM1 : M ≥ 1 := hM_ge1
            have hy_M_bound : ((hinner N hN_ge1).choose M : ℝ) ^ (1 / (M : ℝ)) < 1 + ε / 4 := by
              simp only [] at hM_eq; rw [hM_eq]; exact hM_lt
            let k := N * M
            have hk_ge1 : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
                (Nat.one_le_iff_ne_zero.mp hN_ge1) (Nat.one_le_iff_ne_zero.mp hM1))

            have hmem : (z k : ℝ) ^ (1 / (k : ℝ)) ∈
                (fun j => (z j : ℝ) ^ (1 / (j : ℝ))) '' {j : ℕ | 1 ≤ j} := ⟨k, hk_ge1, rfl⟩
            have hbdd : BddBelow ((fun j => (z j : ℝ) ^ (1 / (j : ℝ))) '' {j : ℕ | 1 ≤ j}) := by
              use 0; intro c hc; obtain ⟨m, _, rfl⟩ := hc; positivity

            have hM_pos : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero
                (Nat.one_le_iff_ne_zero.mp hM1))
            have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero
                (Nat.one_le_iff_ne_zero.mp hk_ge1))

            -- z_k ≤ x_N^M * y_{N,M}
            have hz_le : z k ≤ x N ^ M * (hinner N hN_ge1).choose M := by
              have hdiv : N ∣ k ∧ k ≠ 0 := ⟨⟨M, rfl⟩, Nat.mul_ne_zero
                  (Nat.one_le_iff_ne_zero.mp hN_ge1) (Nat.one_le_iff_ne_zero.mp hM1)⟩
              have hN_mem : N ∈ k.divisors := Nat.mem_divisors.mpr hdiv
              have hm_eq : k / N = M := Nat.mul_div_cancel_left M
                  (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hN_ge1))
              simp only [z, dif_pos hk_ge1]
              apply Finset.min'_le
              simp only [Finset.mem_image]
              use ⟨N, hN_mem⟩
              constructor
              · exact Finset.mem_attach _ _
              · simp only [factorVal, hm_eq]

            -- z_k^{1/k} ≤ x_N^{1/N} * (y^{1/M})^{1/N}
            -- Use abbreviation for the long witness expression
            set y_N_M := (hinner N hN_ge1).choose M with hy_def
            have hz_rpow_le : (z k : ℝ) ^ (1 / (k : ℝ)) ≤
                (x N : ℝ) ^ (1 / (N : ℝ)) *
                  ((y_N_M : ℝ) ^ (1 / (M : ℝ))) ^ (1 / (N : ℝ)) := by
              have hcast : ((x N ^ M * y_N_M : ℕ) : ℝ) =
                  (x N : ℝ) ^ M * (y_N_M : ℝ) := by
                simp [Nat.cast_mul, Nat.cast_pow]
              calc (z k : ℝ) ^ (1 / (k : ℝ))
                  ≤ ((x N ^ M * y_N_M : ℕ) : ℝ) ^ (1 / (k : ℝ)) := by
                      apply Real.rpow_le_rpow (Nat.cast_nonneg _)
                        (Nat.cast_le.mpr hz_le)
                      exact div_nonneg (by norm_num) (le_of_lt hk_pos)
                _ = ((x N : ℝ) ^ M * (y_N_M : ℝ)) ^ (1 / (k : ℝ)) := by
                    rw [hcast]
                _ = (x N : ℝ) ^ ((M : ℝ) / (k : ℝ)) *
                    (y_N_M : ℝ) ^ (1 / (k : ℝ)) := by
                    rw [Real.mul_rpow (pow_nonneg (Nat.cast_nonneg _) _)
                      (Nat.cast_nonneg _)]
                    congr 1
                    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
                    ring_nf
                _ = (x N : ℝ) ^ (1 / (N : ℝ)) * (y_N_M : ℝ) ^ (1 / (k : ℝ)) := by
                    congr 1
                    have hk_eq : (k : ℝ) = (N : ℝ) * (M : ℝ) := by
                      simp [k, Nat.cast_mul]
                    rw [hk_eq]; field_simp
                _ = (x N : ℝ) ^ (1 / (N : ℝ)) *
                    ((y_N_M : ℝ) ^ (1 / (M : ℝ))) ^ (1 / (N : ℝ)) := by
                    congr 1; rw [← Real.rpow_mul (Nat.cast_nonneg _)]; congr 1
                    have hk_eq : (k : ℝ) = (N : ℝ) * (M : ℝ) := by
                      simp [k, Nat.cast_mul]
                    rw [hk_eq]; field_simp

            -- (y^{1/M})^{1/N} < (1+ε/4)^{1/N} ≤ 1+ε/4
            have hy_final : ((y_N_M : ℝ) ^ (1 / (M : ℝ))) ^ (1 / (N : ℝ)) <
                (1 + ε / 4) ^ (1 / (N : ℝ)) := by
              apply Real.rpow_lt_rpow (by positivity) hy_M_bound
              exact div_pos (by norm_num : (0 : ℝ) < 1) hN_pos

            have hexp_bound : (1 + ε / 4) ^ (1 / (N : ℝ)) ≤ 1 + ε / 4 := by
              have hN_ge1_real : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN_ge1
              have hexp_le1 : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one hN_pos]; exact hN_ge1_real
              have hbase_ge1 : (1 : ℝ) ≤ 1 + ε / 4 := by linarith
              calc (1 + ε / 4) ^ (1 / (N : ℝ)) ≤ (1 + ε / 4) ^ (1 : ℝ) := by
                      apply Real.rpow_le_rpow_of_exponent_le hbase_ge1 hexp_le1
                _ = 1 + ε / 4 := Real.rpow_one _

            -- (1+ε/4)² < 1+ε since ε < 8
            have hsq_bound : (1 + ε / 4) * (1 + ε / 4) < 1 + ε := by
              have h1 : (1 + ε / 4) * (1 + ε / 4) = 1 + ε / 2 + (ε / 4) ^ 2 := by ring
              have h3 : (ε / 4) ^ 2 < ε / 2 := by
                have hε4 : ε / 4 < 2 := by linarith
                have hε4_pos : 0 < ε / 4 := by linarith
                calc (ε / 4) ^ 2 = (ε / 4) * (ε / 4) := sq _
                  _ < (ε / 4) * 2 := by apply mul_lt_mul_of_pos_left hε4 hε4_pos
                  _ = ε / 2 := by ring
              linarith

            calc sInf _ ≤ (z k : ℝ) ^ (1 / (k : ℝ)) := csInf_le hbdd hmem
              _ ≤ (x N : ℝ) ^ (1 / (N : ℝ)) *
                  (((hinner N hN_ge1).choose M : ℝ) ^ (1 / (M : ℝ))) ^ (1 / (N : ℝ)) := hz_rpow_le
              _ < (x N : ℝ) ^ (1 / (N : ℝ)) * (1 + ε / 4) := by
                  apply mul_lt_mul_of_pos_left (lt_of_lt_of_le hy_final hexp_bound)
                  exact Real.rpow_pos_of_pos hx_pos _
              _ < (1 + ε / 4) * (1 + ε / 4) := by
                  apply mul_lt_mul_of_pos_right hx_N_bound (by linarith)
              _ < 1 + ε := hsq_bound

        -- Lower bound (1 ≤ sInf):
        -- z_k ≥ 1 for all k ≥ 1, so z_k^{1/k} ≥ 1.
        · have hne : ((fun j => (z j : ℝ) ^ (1 / (j : ℝ))) '' {j : ℕ | 1 ≤ j}).Nonempty :=
            ⟨(z 1 : ℝ) ^ 1, 1, Nat.le_refl 1, by simp⟩
          apply le_csInf hne
          intro v hv
          obtain ⟨k, hk, rfl⟩ := hv
          have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero
              (Nat.one_le_iff_ne_zero.mp hk))
          -- Need z k ≥ 1
          -- First establish x_n ≥ 1 for n ≥ 1 (from sInf = 1)
          have hx_ge1 : ∀ n, n ≥ 1 → x n ≥ 1 := by
            intro n hn
            by_contra hc; push_neg at hc
            have hxn0 : x n = 0 := Nat.lt_one_iff.mp hc
            have hmem : (x n : ℝ) ^ (1 / (n : ℝ)) ∈
                (fun j => (x j : ℝ) ^ (1 / (j : ℝ))) '' {j : ℕ | 1 ≤ j} := ⟨n, hn, rfl⟩
            have hbdd : BddBelow ((fun j => (x j : ℝ) ^ (1 / (j : ℝ))) '' {j : ℕ | 1 ≤ j}) := by
              use 0; intro c hc'; obtain ⟨m, _, rfl⟩ := hc'; positivity
            have hge := csInf_le hbdd hmem
            rw [hx_lim] at hge
            have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero
                (Nat.one_le_iff_ne_zero.mp hn))
            have h1_div_ne : 1 / (n : ℝ) ≠ 0 := one_div_ne_zero (ne_of_gt hn_pos)
            have h0_rpow : (0 : ℝ) ^ (1 / (n : ℝ)) = 0 := Real.zero_rpow h1_div_ne
            simp only [hxn0, Nat.cast_zero, h0_rpow] at hge
            linarith

          -- Similarly, y_{d,m} ≥ 1 for m ≥ 1 (from each inner sInf = 1)
          have hy_ge1 : ∀ d (hd1 : d ≥ 1) m, m ≥ 1 → (hinner d hd1).choose m ≥ 1 := by
            intro d hd1 m hm
            let y := (hinner d hd1).choose
            have hy_lim := (hinner d hd1).choose_spec.2
            by_contra hc; push_neg at hc
            have hym0 : y m = 0 := Nat.lt_one_iff.mp hc
            have hmem : (y m : ℝ) ^ (1 / (m : ℝ)) ∈
                (fun j => (y j : ℝ) ^ (1 / (j : ℝ))) '' {j : ℕ | 1 ≤ j} := ⟨m, hm, rfl⟩
            have hbdd : BddBelow ((fun j => (y j : ℝ) ^ (1 / (j : ℝ))) '' {j : ℕ | 1 ≤ j}) := by
              use 0; intro c hc'; obtain ⟨j, _, rfl⟩ := hc'; positivity
            have hge := csInf_le hbdd hmem
            rw [hy_lim] at hge
            have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero
                (Nat.one_le_iff_ne_zero.mp hm))
            have h1_div_ne : 1 / (m : ℝ) ≠ 0 := one_div_ne_zero (ne_of_gt hm_pos)
            have h0_rpow : (0 : ℝ) ^ (1 / (m : ℝ)) = 0 := Real.zero_rpow h1_div_ne
            simp only [hym0, Nat.cast_zero, h0_rpow] at hge
            linarith

          have hz_ge1 : z k ≥ 1 := by
            -- z k = min' over factorizations of x_d^m * y_{d,m}
            -- Each product ≥ 1, so min ≥ 1
            have hk1 : k ≥ 1 := hk
            simp only [z, hk1, dite_true]
            have hne : k.divisors.Nonempty := Nat.nonempty_divisors.mpr
                (Nat.one_le_iff_ne_zero.mp hk1)
            let valsAttach := k.divisors.attach.image (fun ⟨d, hd⟩ => factorVal k d hd)
            have hne' : valsAttach.Nonempty := by
              rw [Finset.image_nonempty, Finset.attach_nonempty_iff]; exact hne
            -- Every element in valsAttach is ≥ 1
            have hall_ge1 : ∀ v ∈ valsAttach, v ≥ 1 := by
              intro v hv
              rw [Finset.mem_image] at hv
              obtain ⟨⟨d, hd_mem⟩, _, rfl⟩ := hv
              -- factorVal k d hd_mem = x d ^ m * (hinner d hd1).choose m
              simp only [factorVal]
              have hdiv : d ∣ k ∧ k ≠ 0 := Nat.mem_divisors.mp hd_mem
              have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr
                  (fun h => hdiv.2 (Nat.eq_zero_of_zero_dvd (h ▸ hdiv.1)))
              let m := k / d
              have hm1 : 1 ≤ m := by
                have hd_pos : 0 < d := Nat.one_le_iff_ne_zero.mp hd1 |> Nat.pos_of_ne_zero
                exact Nat.one_le_div_iff hd_pos |>.mpr
                    (Nat.le_of_dvd (Nat.pos_of_ne_zero hdiv.2) hdiv.1)
              have hxd : x d ≥ 1 := hx_ge1 d hd1
              have hym : (hinner d hd1).choose m ≥ 1 := hy_ge1 d hd1 m hm1
              calc x d ^ m * (hinner d hd1).choose m
                  ≥ 1 ^ m * 1 := Nat.mul_le_mul (Nat.pow_le_pow_left hxd m) hym
                _ = 1 := by simp
            exact Finset.le_min' valsAttach hne' 1 hall_ge1
          calc 1 = 1 ^ (1 / (k : ℝ)) := by simp
            _ ≤ (z k : ℝ) ^ (1 / (k : ℝ)) := by
                apply Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
                · exact Nat.one_le_cast.mpr hz_ge1
                · exact div_nonneg (by norm_num) (le_of_lt hk_pos)
  · intro h; exact AsympRel.of_le h

/-- Lemma str_props (iv): If ∀n ∈ ℕ, na ≤ na' + s, then a ≲ a'.

    Proof from Strassen (tex file):
    1. Assume a' ≠ 0. Find k with s ≤ k·a' (archimedean).
    2. Substitute m = k·n in the original bound:
       (kn)·a ≤ (kn)·a' + s ≤ (kn)·a' + k·a' = k·(n+1)·a'.
       This is: (n·a)·k ≤ ((n+1)·a')·k.
    3. Apply asymp_of_mul_cancel (ii) with b = k to get: n·a ≲ (n+1)·a'.
    4. By induction using transitivity of ≲:
       a^N ≲ a^{N-1}·a'·2 ≲ ... ≲ (a')^N·(N+1).
    5. Since (N+1)^{1/N} → 1, we get a ≲≲ a' (double asymptotic).
    6. Apply asymp_asymp_eq_asymp (iii) to collapse to a ≲ a'. -/
theorem StrassenPreorder.asymp_of_bounded_diff (p : StrassenPreorder S)
    {a a' : S} (s : S) (ha' : a' ≠ 0) (h : ∀ n : ℕ, p.rel (n • a) (n • a' + s)) :
    AsympRel p a a' := by
  -- Following tex proof of str_props (iv): "We may assume a_1 ≠ 0"
  obtain ⟨k, hk⟩ := p.archimedean s a' ha'
  -- Step 1: Substitute m = k·n in the original bound to get (n·a)·k ≤ ((n+1)·a')·k
  -- From h applied to m = k·n: (k·n)·a ≤ (k·n)·a' + s ≤ (k·n)·a' + k·a' = k·(n+1)·a'
  have hlinear : ∀ n : ℕ, p.rel ((n • a) * k) (((n + 1) • a') * k) := by
      intro n
      -- Apply h with m = k * n
      have h1 := h (k * n)
      -- h1 : (k*n)•a ≤ (k*n)•a' + s
      -- Since s ≤ k*a', we have (k*n)•a' + s ≤ (k*n)•a' + k*a' = (k*n + k)•a' = k*(n+1)•a'
      have h2 : p.rel ((k * n) • a' + s) ((k * n) • a' + k * a') := by
        have hks : p.rel s (k * a') := hk
        have := p.add_mono s (k * a') ((k * n) • a') hks
        simp only [add_comm ((k * n) • a')] at this ⊢
        exact this
      have h3 : (k * n) • a' + k * a' = (k * (n + 1)) • a' := by
        rw [Nat.mul_add, Nat.mul_one, add_smul]
        simp only [nsmul_eq_mul, Nat.cast_mul]
      rw [h3] at h2
      have hbound : p.rel ((k * n) • a) ((k * (n + 1)) • a') := p.trans _ _ _ h1 h2
      -- Rewrite (k*n)•a = (n•a)·k and (k*(n+1))•a' = ((n+1)•a')·k
      have eq1 : (k * n) • a = (n • a) * k := by
        simp only [nsmul_eq_mul, Nat.cast_mul]; ring
      have eq2 : (k * (n + 1)) • a' = ((n + 1) • a') * k := by
        simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]; ring
      rw [eq1, eq2] at hbound
      exact hbound
  -- Step 2: Apply asymp_of_mul_cancel to get n·a ≲ (n+1)·a' for each n
  -- This requires k ≠ 0 in S. Handle the case k = 0 separately.
  by_cases hk0 : (k : S) = 0
  · -- If k = 0 in S, then s ≤ 0 in the preorder (since s ≤ k*a' = 0*a' = 0).
    -- Combined with 0 ≤ s (zero_le), this means s ≈ 0.
    -- Then the original bound becomes n•a ≤ n•a' + 0 = n•a'.
    -- From 1•a ≤ 1•a', i.e., a ≤ a', gives a ≲ a' via AsympRel.of_le.
    have hs0 : p.rel s 0 := by
      have hks : p.rel s (k * a') := hk
      simp only [hk0, zero_mul] at hks
      exact hks
    have hbound_simple : ∀ n : ℕ, p.rel (n • a) (n • a') := by
      intro n
      have := h n
      have h0 : p.rel (n • a' + s) (n • a' + 0) := by
        have h0s := p.add_mono s 0 (n • a') hs0
        simp only [add_comm (n • a')] at h0s ⊢
        exact h0s
      simp only [add_zero] at h0
      exact p.trans _ _ _ this h0
    -- From 1•a ≤ 1•a', i.e., a ≤ a'
    have ha_le_a' : p.rel a a' := by
      have := hbound_simple 1
      simp only [one_smul] at this
      exact this
    exact AsympRel.of_le ha_le_a'
  · -- k ≠ 0 in S: Apply asymp_of_mul_cancel
    have hasym_step : ∀ n : ℕ, AsympRel p (n • a) ((n + 1) • a') := by
      intro n
      have hrel := hlinear n
      exact p.asymp_of_mul_cancel hk0 hrel
    -- Step 3: By induction, show a ≲≲ a' using hasym_step
    -- The tex proof: a^N ≲ a^{N-1}·a'·2 ≲ ... ≲ (a')^N·(N+1)
    -- This is a double asymptotic: outer witness (N+1), inner from each step
    have hasym2 : AsympRel (asympPreorder p) a a' := by
      -- Use witness (N+1) for the outer relation
      -- At each N: (asympPreorder p).rel (a^N) ((a')^N * (N+1))
      -- means AsympRel p (a^N) ((a')^N * (N+1))
      use fun N => N + 1
      constructor
      · -- Show AsympRel p (a^N) ((a')^N * (N+1)) for N ≥ 1
        -- By induction: a^N ≲ a^{N-1}·a'·2 ≲ ... ≲ (a')^N·(N+1)
        -- Each step uses hasym_step: k·a ≲ (k+1)·a'
        intro N hN
        -- Induction on N
        induction N with
        | zero => omega
        | succ N ih =>
          by_cases hN' : N = 0
          · -- Base: a^1 ≲ a'·2
            subst hN'
            have hbase := hasym_step 1
            simp only [one_smul, nsmul_eq_mul] at hbase
            -- hbase : AsympRel p a (↑(1+1) * a')
            -- Need: (asympPreorder p).rel (a^1) (a'^1 * 2)
            change (asympPreorder p).rel (a^1) (a'^1 * ↑2)
            simp only [pow_one]
            -- ↑(1+1) * a' = a' * ↑2
            have heq : (↑(1 + 1 : ℕ) : S) * a' = a' * ↑(2 : ℕ) := by norm_cast; ring
            rw [heq] at hbase
            exact hbase
          · -- Inductive: a^{N+1} ≲ (a')^{N+1}·(N+2)
            -- From IH: a^N ≲ (a')^N·(N+1)
            -- From hasym_step(N+1): (N+1)·a ≲ (N+2)·a'
            --
            -- The tex approach: a^{N+1} = a · a^N
            -- Chain: a·a^N ≲ a·(a')^N·(N+1) = (a')^N·((N+1)·a)
            --        ≲ (a')^N·((N+2)·a') = (a')^{N+1}·(N+2)
            have hN1 : N ≥ 1 := Nat.one_le_iff_ne_zero.mpr hN'
            have hih := ih hN1
            -- Step 1: a * a^N ≲ a * (a')^N * (N+1)
            have hmul_ih : AsympRel p (a * a^N) (a * (a'^N * ↑(N + 1))) := by
              have := (asympPreorder p).mul_mono (a^N) (a'^N * ↑(N + 1)) a hih
              simp only [mul_comm a] at this ⊢
              exact this
            -- Rewrite: a * (a')^N * (N+1) = (a')^N * ((N+1) * a)
            have hmul_ih' : AsympRel p (a * a^N) (a'^N * (↑(N + 1) * a)) := by
              have heq : a * (a'^N * ↑(N + 1)) = a'^N * (↑(N + 1) * a) := by ring
              rw [← heq]; exact hmul_ih
            -- Step 2: (a')^N * ((N+1)*a) ≲ (a')^N * ((N+2)*a')
            have hstep := hasym_step (N + 1)
            simp only [nsmul_eq_mul] at hstep
            have hmul_step : AsympRel p (a'^N * (↑(N + 1) * a)) (a'^N * (↑(N + 2) * a')) := by
              have := (asympPreorder p).mul_mono (↑(N + 1) * a) (↑(N + 2) * a') (a'^N) hstep
              have heq1 : (↑(N + 1) * a) * a'^N = a'^N * (↑(N + 1) * a) := by ring
              have heq2 : (↑(N + 2) * a') * a'^N = a'^N * (↑(N + 2) * a') := by ring
              rw [heq1, heq2] at this; exact this
            -- Chain the two
            have hchain := AsympRel.trans hmul_ih' hmul_step
            -- Now show a^{N+1} = a * a^N and (a')^{N+1}*(N+2) = (a')^N * (N+2) * a'
            change (asympPreorder p).rel (a^(N+1)) (a'^(N+1) * ↑(N + 2))
            have hlhs : a^(N+1) = a * a^N := by rw [pow_succ]; ring
            have hrhs : a'^(N+1) * ↑(N + 2) = a'^N * (↑(N + 2) * a') := by
              rw [pow_succ]; ring
            rw [hlhs, hrhs]; exact hchain
      · -- sInf((N+1)^{1/N}) = 1
        -- Standard analysis: (N+1)^{1/N} → 1 as N → ∞
        have htendsto : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ)))
            Filter.atTop (nhds 1) := by
          have hreal : Filter.Tendsto (fun x : ℝ => x ^ (1 / (1 * x + (-1))))
              Filter.atTop (nhds 1) := tendsto_rpow_div_mul_add 1 1 (-1) (by norm_num)
          simp only [one_mul] at hreal
          have hnat : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ))
              Filter.atTop Filter.atTop := by
            rw [Filter.tendsto_atTop_atTop]
            intro b
            use max 0 ⌈b⌉₊
            intro n hn
            simp only [Nat.cast_add, Nat.cast_one]
            calc b ≤ max 0 (⌈b⌉₊ : ℝ) := by simp only [le_max_iff, or_true, Nat.le_ceil]
              _ ≤ (n : ℝ) := by exact_mod_cast hn
              _ ≤ n + 1 := by linarith
          have hcomp := hreal.comp hnat
          simp only [Function.comp_def] at hcomp
          refine hcomp.congr ?_
          intro n
          simp only [Nat.cast_add, Nat.cast_one]
          congr 1; ring
        apply le_antisymm
        · apply le_of_forall_pos_lt_add
          intro ε hε
          rw [Metric.tendsto_atTop] at htendsto
          obtain ⟨N, hN⟩ := htendsto ε hε
          let M := max N 1
          have hM1 : M ≥ 1 := le_max_right N 1
          have hMN : M ≥ N := le_max_left N 1
          have hmem : ((M + 1 : ℕ) : ℝ) ^ (1 / (M : ℝ)) ∈
              (fun n => ((n + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n} := by
            use M; exact ⟨hM1, rfl⟩
          have hbdd : BddBelow ((fun n => ((n + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ))) ''
              {n : ℕ | 1 ≤ n}) := by
            use 1; intro z hz; obtain ⟨n, hn, rfl⟩ := hz
            have hn_pos : (0 : ℝ) < n :=
              Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn))
            calc 1 = 1 ^ (1 / (n : ℝ)) := by simp
              _ ≤ ((n + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ)) := by
                  apply Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
                  · simp only [Nat.cast_add, Nat.cast_one]; linarith
                  · exact div_nonneg (by norm_num) (le_of_lt hn_pos)
          have hdist := hN M hMN
          rw [Real.dist_eq] at hdist
          calc sInf _ ≤ ((M + 1 : ℕ) : ℝ) ^ (1 / (M : ℝ)) := csInf_le hbdd hmem
            _ < 1 + ε := by linarith [(abs_lt.mp hdist).2]
        · have hne : ((fun n => ((n + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ))) ''
              {n : ℕ | 1 ≤ n}).Nonempty := by
            use ((1 + 1 : ℕ) : ℝ) ^ (1 / (1 : ℝ)); use 1; simp
          apply le_csInf hne
          intro z hz; obtain ⟨n, hn, rfl⟩ := hz
          have hn_pos : (0 : ℝ) < n :=
            Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn))
          calc 1 = 1 ^ (1 / (n : ℝ)) := by simp
            _ ≤ ((n + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ)) := by
                apply Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
                · simp only [Nat.cast_add, Nat.cast_one]; linarith
                · exact div_nonneg (by norm_num) (le_of_lt hn_pos)
    -- Apply asymp_asymp_eq_asymp to collapse ≲≲ to ≲
    rw [asymp_asymp_eq_asymp] at hasym2
    exact hasym2

/-- Lemma str_props (i): If a + b ≤ a' + b then a ≲ a'.
    Proof: From add_cancel_induction, ∀n, na + b ≤ na' + b, i.e., na ≤ na' + b.
    Then apply asymp_of_bounded_diff.
    Special case when a' = 0: Either a = 0 (trivial) or we get contradiction via 2r ≤ r. -/
theorem StrassenPreorder.asymp_of_add_cancel (p : StrassenPreorder S)
    {a a' b : S} (h : p.rel (a + b) (a' + b)) :
    AsympRel p a a' := by
  -- Case split on a' = 0
  by_cases ha' : a' = 0
  · -- Case a' = 0: From a + b ≤ b, either a = 0 or we get contradiction
    subst ha'
    simp only [zero_add] at h
    -- h : a + b ≤ b
    by_cases ha : a = 0
    · -- If a = 0: 0 ≲ 0 by reflexivity
      subst ha; exact AsympRel.refl 0
    · -- If a ≠ 0: Derive contradiction via tex proof
      -- From a + b ≤ b, by induction: ∀q, q•a + b ≤ b
      have hq : ∀ q : ℕ, p.rel (q • a + b) b := by
        intro q
        induction q with
        | zero => simp only [zero_smul, zero_add]; exact p.refl b
        | succ q ih =>
          -- (q+1)a + b = qa + (a + b) ≤ qa + b [by h] ≤ b [by ih]
          have h1 : p.rel (q • a + (a + b)) (q • a + b) := by
            have := p.add_mono (a + b) b (q • a) h
            simp only [add_comm (q • a)] at this ⊢; exact this
          have h12 : p.rel (q • a + (a + b)) b := p.trans _ _ _ h1 ih
          simp only [succ_nsmul] at h12 ⊢
          convert h12 using 1; ring
      -- By archimedean on b and 1: ∃r, b ≤ r
      by_cases h1 : (1 : S) = 0
      · -- If 1 = 0 in S, then S is trivial and everything is 0
        have ha0 : a = 0 := by
          have : a = a * 1 := by ring
          rw [this, h1, mul_zero]
        exact absurd ha0 ha
      · -- 1 ≠ 0: Use archimedean
        obtain ⟨r, hr⟩ := p.archimedean b 1 h1
        simp only [mul_one] at hr
        -- By archimedean on 2r and a: ∃q, 2r ≤ q•a
        obtain ⟨q, hq2r⟩ := p.archimedean (2 * r) a ha
        -- From hq: q•a + b ≤ b ≤ r
        have hqab_le_r : p.rel (q • a + b) r := p.trans _ _ _ (hq q) hr
        -- q•a ≤ q•a + b (by zero_le on b)
        have hqa_le_qab : p.rel (q • a) (q • a + b) := by
          have hzero := p.zero_le b
          have h1 : p.rel (0 + q • a) (b + q • a) := p.add_mono 0 b (q • a) hzero
          simp only [zero_add] at h1
          have eq : b + q • a = q • a + b := by ring
          rw [eq] at h1; exact h1
        -- Chain: 2r ≤ q*a ≤ q•a + b ≤ r (where q•a = q*a)
        -- First, note that hq2r gives rel (2 * ↑r) (↑q * a)
        -- And q•a = ↑q * a, so hqa_le_qab gives rel (↑q * a) (↑q * a + b)
        simp only [nsmul_eq_mul] at hqa_le_qab hqab_le_r
        -- Now chain: 2↑r ≤ ↑q*a ≤ ↑q*a + b ≤ ↑r
        have h2r_le_r : p.rel ((2 : ℕ) * r : S) (r : S) := by
          have h1 : p.rel (2 * (r : S)) (↑q * a) := hq2r
          have h2 : p.rel (↑q * a) (↑q * a + b) := hqa_le_qab
          have h3 : p.rel (↑q * a + b) (r : S) := hqab_le_r
          exact p.trans _ _ _ h1 (p.trans _ _ _ h2 h3)
        -- 2r ≤ r in S means 2r ≤ r in ℕ by nat_compat
        have hcast : ((2 : ℕ) * r : S) = ((2 * r : ℕ) : S) := by simp [Nat.cast_mul]
        rw [hcast] at h2r_le_r
        have hnat := (p.nat_compat (2 * r) r).mpr h2r_le_r
        -- 2r ≤ r in ℕ means r = 0 (since 2r > r for r ≥ 1)
        have hr0 : r = 0 := by omega
        -- If r = 0, then b ≤ 0 and 0 ≤ q * a, giving 0 ≤ q * a ≤ q * a + b ≤ 0
        subst hr0
        simp only [Nat.cast_zero, mul_zero] at hr hq2r
        -- hr : b ≤ 0, hq2r : 0 ≤ q * a, hqab_le_r : q * a + b ≤ 0
        simp only [Nat.cast_zero] at hqab_le_r
        -- From 0 ≤ a (zero_le) and q * a + b ≤ 0
        -- We have 0 ≤ q * a (from hq2r) and q * a ≤ q * a + b (from zero_le b)
        -- And q * a + b ≤ 0. So if q ≥ 1, we get a ≤ q * a ≤ 0, giving a ≤ 0.
        -- Combined with 0 ≤ a, we have 0 ≈ a.
        -- But we need a = 0. In the semiring, from 0 ≤ a ≤ 0, use nat_compat...
        -- Actually, we can't prove a = 0 without antisymmetry.
        -- But from a + b ≤ b ≤ 0 and 0 ≤ 1*a = a, if we take q = 1:
        -- From hq 1: 1*a + b ≤ b, i.e., a + b ≤ b
        -- This gives a + b ≤ b ≤ 0 and 0 ≤ a ≤ a + b (by zero_le on b)
        -- So a ≤ a + b ≤ 0, giving a ≤ 0, i.e., p.rel a 0
        have ha_le_0 : p.rel a 0 := by
          -- From hq2r: 0 ≤ q * a, i.e., p.rel 0 (q * a)
          -- Need: p.rel a 0
          -- Chain: a ≤ a + b (zero_le on b) and a + b ≤ b (from hq 1) and b ≤ 0 (hr)
          have hab_le_b := hq 1
          simp only [one_smul] at hab_le_b
          -- hab_le_b : a + b ≤ b
          have hb_le_0 : p.rel b 0 := hr
          have hab_le_0 : p.rel (a + b) 0 := p.trans _ _ _ hab_le_b hb_le_0
          -- a ≤ a + b (via zero_le on b and add)
          have ha_le_ab : p.rel a (a + b) := by
            have h0b := p.zero_le b
            have := p.add_mono 0 b a h0b
            simp only [zero_add, add_comm b a] at this; exact this
          exact p.trans _ _ _ ha_le_ab hab_le_0
        -- Now we have both p.rel 0 a (zero_le) and p.rel a 0
        -- But a ≠ 0 by assumption. This seems like we can't get a true contradiction
        -- without antisymmetry. Let's use nat_compat on 0 and 1.
        -- If p.rel 1 0, then by nat_compat, 1 ≤ 0 in ℕ, contradiction.
        -- From a ≤ 0 and 0 ≤ a, can we derive 1 ≤ 0?
        -- Not directly... but we can use archimedean on a.
        -- Since a ≠ 0, ∃m, 1 ≤ m * a. Then 1 ≤ m * a ≤ m * 0 = 0 gives 1 ≤ 0.
        obtain ⟨m, hm⟩ := p.archimedean 1 a ha
        have hma_le_0 : p.rel (m * a) 0 := by
          have := p.mul_mono a 0 m ha_le_0
          simp only [zero_mul] at this
          rw [mul_comm a (m : S)] at this; exact this
        have h1_le_0 : p.rel (1 : S) 0 := p.trans _ _ _ hm hma_le_0
        exact (p.not_rel_one_zero h1_le_0).elim
  · -- Case a' ≠ 0: Use asymp_of_bounded_diff
    -- Step 1: Prove ∀q, qa + b ≤ qa' + b by induction
    have hq : ∀ q : ℕ, p.rel (q • a + b) (q • a' + b) := by
      intro q
      induction q with
      | zero => simp only [zero_smul, zero_add]; exact p.refl b
      | succ q ih =>
        have h1 : p.rel (q • a + (a + b)) (q • a + (a' + b)) := by
          have := p.add_mono (a + b) (a' + b) (q • a) h
          simp only [add_comm (q • a)] at this ⊢; exact this
        have h2 : p.rel (q • a + (a' + b)) ((q • a' + b) + a') := by
          have h_ih : p.rel ((q • a + b) + a') ((q • a' + b) + a') := p.add_mono _ _ a' ih
          have eq1 : q • a + (a' + b) = (q • a + b) + a' := by ring
          rw [eq1]; exact h_ih
        have h3 : p.rel ((q • a' + b) + a') ((q + 1) • a' + b) := by
          have eq : (q • a' + b) + a' = (q + 1) • a' + b := by simp only [succ_nsmul]; ring
          rw [eq]; exact p.refl _
        have h12 : p.rel (q • a + (a + b)) ((q • a' + b) + a') := p.trans _ _ _ h1 h2
        have h123 : p.rel (q • a + (a + b)) ((q + 1) • a' + b) := p.trans _ _ _ h12 h3
        simp only [succ_nsmul] at h123 ⊢
        convert h123 using 1; ring
    -- Step 2: Get ∀n, na ≤ na' + b
    have hbounded : ∀ n : ℕ, p.rel (n • a) (n • a' + b) := by
      intro n
      have hle : p.rel (n • a) (n • a + b) := by
        have hzero := p.zero_le b
        have h1 : p.rel (0 + n • a) (b + n • a) := p.add_mono 0 b (n • a) hzero
        simp only [zero_add] at h1
        have eq : b + n • a = n • a + b := by ring
        rw [eq] at h1; exact h1
      exact p.trans _ _ _ hle (hq n)
    -- Step 3: Apply asymp_of_bounded_diff
    exact asymp_of_bounded_diff p b ha' hbounded

end AsymptoticSpectrumDuality
