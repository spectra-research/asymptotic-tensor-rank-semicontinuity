/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.AsymptoticSpectrumDuality.Maximal

/-!
# Completeness of Maximal Strassen Preorders

This file proves the completeness lemma: the asymptotic preorder coincides with
the intersection of all maximal Strassen preorders.

## Main Results

* `asymp_iff_forall_maximal` : a ≲ b ↔ ∀ maximal p, a ≤_p b (Lemma str_complete)

## References

* Strassen (1988), The asymptotic spectrum of tensors
-/

namespace AsymptoticSpectrumDuality

open StrassenPreorder

variable {S : Type*} [CommSemiring S]

/-! ### Completeness Lemma -/

/-- Forward direction: if a ≲ b then a ≤ b for all maximal preorders.
    This uses that maximal preorders are closed under asymptotic. -/
theorem asymp_implies_maximal (p : StrassenPreorder S) (hmax : p.IsMaximal)
    {a b : S} (hasym : AsympRel p a b) : p.rel a b := by
  -- By maximal_eq_asymp, p is asymptotically closed, so p.rel = (asympPreorder p).rel
  have hclosed := maximal_eq_asymp p hmax
  -- hasym : AsympRel p a b, and we want p.rel a b
  -- Since p.rel = AsympRel p (from hclosed), this is direct
  rw [hclosed]
  exact hasym

/-- Helper: In the extended preorder from extend_strassen, a ̸≤ b.
    Proof: q.rel a b = ∃s, pa.rel (a + s*a) (b + s*b) = ∃s, pa.rel ((1+s)*a) ((1+s)*b).
    For s=0, this is pa.rel a b = hpa_not (false).
    For s≠0, by asymp_of_mul_cancel with (1+s)≠0: a ≲_{pa} b, but pa is closed so pa.rel a b,
    contradicting hpa_not. -/
private theorem extend_strassen_not_rel (pa : StrassenPreorder S)
    (hpa_closed : pa.rel = (asympPreorder pa).rel)
    (a b : S) (hpa_not : ¬pa.rel a b)
    (q : StrassenPreorder S) (_hpaq : pa ≤ q) (_hqba : q.rel b a)
    (hq_ext : ∀ x y, q.rel x y ↔ ∃ s : S, pa.rel (x + s * a) (y + s * b)) :
    ¬q.rel a b := by
  intro hqab
  rw [hq_ext] at hqab
  obtain ⟨s, hs⟩ := hqab
  -- hs : pa.rel (a + s*a) (b + s*b) = pa.rel ((1+s)*a) ((1+s)*b)
  have heq1 : a + s * a = (1 + s) * a := by ring
  have heq2 : b + s * b = (1 + s) * b := by ring
  rw [heq1, heq2] at hs
  by_cases h0 : 1 + s = 0
  · -- In a semiring, 1 + s = 0 is typically false (no additive inverses).
    -- We need 0 ≤ 1 (by zero_le) and 0 ≤ s, so 0 ≤ 1 + s.
    -- If 1 + s = 0 and 0 ≤ 1 + s, then 0 = 1 + s ≥ 0, which is fine,
    -- but we also need 1 + s ≥ 1 (since 1 + s = 1 + s with s ≥ 0).
    -- Actually, from pa.rel ((1+s)*a) ((1+s)*b) and 1+s=0:
    -- pa.rel (0*a) (0*b) = pa.rel 0 0, which is reflexivity.
    -- This doesn't immediately give a contradiction...
    -- If 1 + s = 0, derive a contradiction via nat_compat.
    -- From 0 ≤ s and add_mono, we get 1 ≤ 1 + s = 0, i.e., pa.rel 1 0.
    -- By nat_compat, this implies 1 ≤ 0 as naturals, contradiction.
    simp only [h0, zero_mul] at hs
    exfalso
    have h1 : pa.rel 0 s := pa.zero_le s
    -- pa.add_mono 0 1 s gives pa.rel (0 + s) (1 + s) = pa.rel s (1 + s)
    have h2 : pa.rel s (1 + s) := by
      have h := pa.add_mono 0 1 s (pa.zero_le 1)
      simp only [zero_add] at h
      exact h
    rw [h0] at h2
    -- h2 : pa.rel s 0
    have h3 : pa.rel 0 1 := pa.zero_le 1
    -- pa.add_mono 0 s 1 gives pa.rel (0 + 1) (s + 1). Need to convert s + 1 to 1 + s.
    have h4 : pa.rel 1 (1 + s) := by
      have h := pa.add_mono 0 s 1 h1
      simp only [zero_add] at h
      -- h : pa.rel 1 (s + 1). Goal: pa.rel 1 (1 + s)
      rw [add_comm] at h
      exact h
    rw [h0] at h4
    -- h4 : pa.rel 1 0
    -- Now use nat_compat: 1 ≤ 0 ↔ pa.rel ↑1 ↑0. Since h4, we have 1 ≤ 0, contradiction.
    exact pa.not_rel_one_zero h4
  · -- 1 + s ≠ 0: Apply asymp_of_mul_cancel
    -- From hs : pa.rel ((1+s)*a) ((1+s)*b) and h0 : 1+s ≠ 0
    -- Rewrite using commutativity: (1+s)*a = a*(1+s)
    have hs' : pa.rel (a * (1 + s)) (b * (1 + s)) := by
      simp only [mul_comm a (1 + s), mul_comm b (1 + s)] at hs ⊢; exact hs
    -- By asymp_of_mul_cancel: a ≲_{pa} b
    have hmul := pa.asymp_of_mul_cancel h0 hs'
    -- hmul : AsympRel pa a b
    -- Since pa = pa≲ (by hpa_closed), AsympRel pa = pa.rel
    have hrel : pa.rel a b := by rw [hpa_closed]; exact hmul
    exact hpa_not hrel

/-- Key lemma for completeness: from ¬AsympRel p a b, extract n with ¬p.rel (n•a) (n•b + 1).
    This is the contrapositive of asymp_of_bounded_diff. -/
private lemma not_asymp_exists_neg_bound (p : StrassenPreorder S)
    {a b : S} (hnasym : ¬AsympRel p a b) :
    ∃ n : ℕ, n ≥ 1 ∧ ¬p.rel (n • a) (n • b + 1) := by
  -- Contrapositive of asymp_of_bounded_diff (iv):
  -- If ∀n, p.rel (n•a) (n•b + 1), then AsympRel p a b (when b ≠ 0).
  -- Handle b = 0 case:
  by_cases hb : b = 0
  · -- b = 0: We need ∃n, ¬p.rel (n•a) (n•0 + 1) = ¬p.rel (n•a) 1.
    subst hb
    simp only [smul_zero, zero_add]
    -- Case split on a = 0
    by_cases ha : a = 0
    · -- a = 0: AsympRel p 0 0 holds trivially, contradicting hnasym
      subst ha
      exfalso
      apply hnasym
      -- Construct AsympRel p 0 0 with witness x_n = 1
      refine ⟨fun _ => 1, fun n hn => ?_, ?_⟩
      · simp only [zero_pow (Nat.one_le_iff_ne_zero.mp hn), zero_mul]
        exact p.refl 0
      · -- The sInf of {1^(1/n) | n ≥ 1} = 1
        have : sInf ((fun n : ℕ => (1 : ℝ) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n}) = 1 := by
          have himg : (fun n : ℕ => (1 : ℝ) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n} = {1} := by
            ext x
            simp only [Set.mem_image, Set.mem_setOf_eq, Real.one_rpow, Set.mem_singleton_iff]
            constructor
            · rintro ⟨_, _, rfl⟩; rfl
            · intro hx; exact ⟨1, le_refl 1, hx.symm⟩
          simp only [himg, csInf_singleton]
        convert this using 2
        simp only [Nat.cast_one]
    · -- a ≠ 0: If ∀n, p.rel (n•a) 1, derive contradiction via 2 ≤ 1 in ℕ
      by_contra hall
      push_neg at hall
      -- hall : ∀n ≥ 1, p.rel (n•a) 1
      -- By archimedean with s = 1, a' = a: ∃k, p.rel 1 (k•a)
      obtain ⟨k, hk⟩ := p.archimedean 1 a ha
      -- p.rel 1 (k * a) where k * a = k•a
      have hk' : p.rel 1 (k • a) := by
        simp only [nsmul_eq_mul] at hk ⊢
        exact hk
      -- From hall: p.rel (k•a) 1 (for k ≥ 1)
      have hk_ge1 : k ≥ 1 := by
        by_contra hk0
        push_neg at hk0
        interval_cases k
        simp only [zero_smul] at hk'
        -- p.rel 1 0 contradicts nat_compat (1 ≤ 0 in ℕ)
        exact p.not_rel_one_zero hk'
      have hka_1 : p.rel (k • a) 1 := hall k hk_ge1
      -- So k•a ≈ 1: both k•a ≤ 1 and 1 ≤ k•a
      -- From k•a ≤ 1 and 1 ≤ k•a, by add_mono: (k•a) + (k•a) ≤ 1 + (k•a) and 1 + 1 ≤ (k•a) + (k•a)
      -- I.e., (2k)•a ≤ 1 + (k•a) and 2 ≤ (2k)•a
      -- From hall with n = 2k: (2k)•a ≤ 1
      -- Combined: 2 ≤ (2k)•a ≤ 1, so 2 ≤ 1 in the preorder
      have h2k : p.rel ((2 * k) • a) 1 := by
        have h2k_ge1 : 2 * k ≥ 1 := by omega
        exact hall (2 * k) h2k_ge1
      -- (2k)•a = 2•(k•a) by nsmul associativity
      have h2ka_eq : (2 * k) • a = 2 • (k • a) := by rw [mul_smul]
      rw [h2ka_eq] at h2k
      -- From hk': 1 ≤ k•a
      -- By nsmul_mono: 2•1 ≤ 2•(k•a)
      have h2_2ka : p.rel (2 • (1 : S)) (2 • (k • a)) := p.nsmul_mono 2 hk'
      simp only [nsmul_one] at h2_2ka
      -- h2_2ka : 2 ≤ 2•(k•a)
      -- h2k : 2•(k•a) ≤ 1
      have h2_1 : p.rel 2 1 := p.trans 2 (2 • (k • a)) 1 h2_2ka h2k
      -- By nat_compat: 2 ≤ 1 in ℕ
      have : (2 : ℕ) ≤ 1 := (p.nat_compat 2 1).mpr
        (by simp only [Nat.cast_ofNat, Nat.cast_one]; exact h2_1)
      omega
  · -- b ≠ 0: Use contrapositive of asymp_of_bounded_diff.
    by_contra hall
    push_neg at hall
    -- hall : ∀n ≥ 1, p.rel (n•a) (n•b + 1)
    apply hnasym
    -- Apply asymp_of_bounded_diff with s = 1
    have h : ∀ n : ℕ, p.rel (n • a) (n • b + 1) := by
      intro n
      by_cases hn : n ≥ 1
      · exact hall n hn
      · -- n = 0: p.rel 0 (0 + 1) = p.rel 0 1 holds by zero_le and nat_compat
        push_neg at hn
        interval_cases n
        simp only [zero_smul, zero_add]
        exact p.zero_le 1
    exact p.asymp_of_bounded_diff 1 hb h

/-- Stronger version: from ¬AsympRel p a b, extract n with ¬AsympRel p (n•a) (n•b + 1).
    This follows from applying str_props(iv) to the asymptotic preorder pa. -/
private lemma not_asymp_exists_neg_asymp_bound (p : StrassenPreorder S)
    {a b : S} (hnasym : ¬AsympRel p a b) :
    ∃ n : ℕ, n ≥ 1 ∧ ¬AsympRel p (n • a) (n • b + 1) := by
  -- Let pa = asympPreorder p. Then pa is a Strassen preorder.
  let pa := asympPreorder p
  -- By str_props(iv) for pa: ∀n, pa.rel (n•a) (n•b + 1) → AsympRel pa a b
  -- By asymp_asymp_eq_asymp: AsympRel pa = AsympRel p
  -- So: ∀n, AsympRel p (n•a) (n•b + 1) → AsympRel p a b
  -- Contrapositive: ¬AsympRel p a b → ∃n, ¬AsympRel p (n•a) (n•b + 1)
  by_contra hall
  push_neg at hall
  -- hall : ∀n ≥ 1, AsympRel p (n•a) (n•b + 1)
  apply hnasym
  -- Need to show AsympRel p a b
  -- Apply str_props(iv) to pa
  have hb_cases : b = 0 ∨ b ≠ 0 := eq_or_ne b 0
  rcases hb_cases with rfl | hb
  · -- b = 0: Need AsympRel p a 0
    -- From hall: ∀n ≥ 1, AsympRel p (n•a) 1
    -- This means (n•a)^k ≤ 1^k * x_k = x_k for some witness with sInf = 1
    -- Since sInf = 1 and x_k ≥ 1, we have x_k → 1^k = 1 (in the limit sense)
    -- So (n•a)^k is bounded, meaning n•a is "bounded" asymptotically.
    -- For a = 0: AsympRel p 0 0 is trivial.
    -- For a ≠ 0: Similar argument as in not_asymp_exists_neg_bound, derive 2 ≤ 1 contradiction.
    simp only [smul_zero, zero_add] at hall
    by_cases ha : a = 0
    · -- a = 0, b = 0: AsympRel p 0 0 is trivial
      subst ha
      exact AsympRel.refl 0
    · -- a ≠ 0, b = 0: Derive contradiction from hall
      -- hall : ∀n ≥ 1, AsympRel p (n•a) 1
      -- From AsympRel p (n•a) 1, we get (n•a)^k ≤ 1^k * x_k = x_k with sInf = 1
      -- For n = 1: AsympRel p a 1
      -- For n = 2: AsympRel p (2•a) 1
      -- By the asymptotic preorder structure, this means a is "asymptotically ≤ 1/n" in some sense.
      -- The archimedean property of the asymptotic preorder should give AsympRel p a 0.
      -- Actually, let's use that pa = asympPreorder p satisfies str_props(iv).
      -- For pa with b = 0, s = 1: if ∀n, pa.rel (n•a) 1, then AsympRel pa a 0.
      have hpa : ∀ n : ℕ, pa.rel (n • a) (n • (0 : S) + 1) := by
        intro n
        by_cases hn : n ≥ 1
        · simp only [smul_zero, zero_add]; exact hall n hn
        · push_neg at hn
          interval_cases n
          simp only [zero_smul, smul_zero, zero_add]
          exact pa.zero_le 1
      simp only [smul_zero, zero_add] at hpa
      -- hpa : ∀n, AsympRel p (n•a) 1
      --
      -- Following the same pattern as lines 166-207 for the direct preorder case:
      -- 1. By pa.archimedean: ∃k, pa.rel 1 (k•a)
      -- 2. From hpa k: pa.rel (k•a) 1
      -- 3. So k•a ≈ 1 in pa
      -- 4. From hpa (2k): pa.rel ((2k)•a) 1
      -- 5. (2k)•a = 2•(k•a), so pa.rel 2 (2•(k•a)) by nsmul_mono
      -- 6. By transitivity: pa.rel 2 1
      -- 7. By pa.nat_compat.mp: 2 ≤ 1 in ℕ — contradiction!
      --
      -- Get k with pa.rel 1 (k•a)
      obtain ⟨k, hk⟩ := pa.archimedean 1 a ha
      have hk' : pa.rel 1 (k • a) := by simp only [nsmul_eq_mul] at hk ⊢; exact hk
      -- Show k ≥ 1
      have hk_ge1 : k ≥ 1 := by
        by_contra hk0
        push_neg at hk0
        interval_cases k
        simp only [zero_smul] at hk'
        -- pa.rel 1 0 contradicts nat_compat
        exact pa.not_rel_one_zero hk'
      -- Get pa.rel (k•a) 1 from hpa
      have hka_1 : pa.rel (k • a) 1 := hpa k
      -- Get pa.rel ((2k)•a) 1 from hpa
      have h2k : pa.rel ((2 * k) • a) 1 := hpa (2 * k)
      -- (2k)•a = 2•(k•a)
      have h2ka_eq : (2 * k) • a = 2 • (k • a) := mul_smul 2 k a
      rw [h2ka_eq] at h2k
      -- By nsmul_mono: pa.rel 2 (2•(k•a))
      have h2_2ka : pa.rel (2 • (1 : S)) (2 • (k • a)) := pa.nsmul_mono 2 hk'
      simp only [nsmul_one] at h2_2ka
      -- By transitivity: pa.rel 2 1
      have h2_1 : pa.rel 2 1 := pa.trans 2 (2 • (k • a)) 1 h2_2ka h2k
      -- By nat_compat.mp: 2 ≤ 1 in ℕ — contradiction!
      have : (2 : ℕ) ≤ 1 := (pa.nat_compat 2 1).mpr (by
        simp only [Nat.cast_ofNat, Nat.cast_one]; exact h2_1)
      omega
  · -- b ≠ 0: Apply pa.asymp_of_bounded_diff
    have hpa : ∀ n : ℕ, pa.rel (n • a) (n • b + 1) := by
      intro n
      by_cases hn : n ≥ 1
      · exact hall n hn
      · push_neg at hn
        interval_cases n
        simp only [zero_smul, zero_add]
        exact pa.zero_le 1
    have hasym_pa : AsympRel pa a b := pa.asymp_of_bounded_diff 1 hb hpa
    -- AsympRel pa = AsympRel p by asymp_asymp_eq_asymp
    rw [asymp_asymp_eq_asymp p] at hasym_pa
    exact hasym_pa

/-- Backward direction: if a ≤ b for all maximal extensions of p, then a ≲_p b.
    Uses the contrapositive: if a ̸≲ b, find n with n•a ̸≲ n•b + 1, then extend. -/
theorem forall_maximal_implies_asymp (p : StrassenPreorder S)
    {a b : S} (hforall : ∀ q : StrassenPreorder S, p ≤ q → q.IsMaximal → q.rel a b) :
    AsympRel p a b := by
  -- We prove by contradiction: suppose a ̸≲ b
  by_contra hnasym
  -- From ¬AsympRel p a b, extract n ≥ 1 with ¬AsympRel p (n•a) (n•b + 1)
  -- This is the stronger version using str_props(iv) applied to asymptotic preorder
  obtain ⟨n, hn_ge1, hneg⟩ := not_asymp_exists_neg_asymp_bound p hnasym
  -- The asymptotic preorder of p
  let pa := asympPreorder p
  -- pa is asymptotically closed
  have hpa_closed : pa.rel = (asympPreorder pa).rel := by
    ext x y
    constructor
    · exact fun h => AsympRel.of_le h
    · intro h
      change AsympRel pa x y at h
      have heq : AsympRel pa = AsympRel p := asymp_asymp_eq_asymp p
      rw [heq] at h
      exact h
  -- ¬pa.rel (n•a) (n•b + 1) directly from hneg (since pa.rel = AsympRel p)
  have hpa_not : ¬pa.rel (n • a) (n • b + 1) := hneg
  -- By extend_strassen, there exists q ⊇ pa with q.rel (n•b + 1) (n•a)
  obtain ⟨q, hpaq, hq_ext⟩ := extend_strassen pa hpa_closed (n • a) (n • b + 1) hpa_not
  -- Extend q to a maximal preorder q'
  obtain ⟨q', hqq', hq'max⟩ := exists_maximal_strassen q
  -- q' ⊇ q ⊇ pa ⊇ p
  have hpq' : p ≤ q' := by
    intro x y hxy
    have h1 : pa.rel x y := AsympRel.of_le hxy
    have h2 : q.rel x y := hpaq x y h1
    exact hqq' x y h2
  -- By hforall, q'.rel a b
  have hq'ab : q'.rel a b := hforall q' hpq' hq'max
  -- q' is maximal, hence total
  have hq'total := maximal_is_total q' hq'max
  -- Also q'.rel (n•b + 1) (n•a) (from q ≤ q' and hq_ext)
  have hq'_ext : q'.rel (n • b + 1) (n • a) := hqq' _ _ hq_ext
  -- From q'.rel a b, we get q'.rel (n•a) (n•b) by mul_mono
  have hq'_na_nb : q'.rel (n • a) (n • b) := by
    have := q'.nsmul_mono n hq'ab
    exact this
  -- From q'.rel (n•a) (n•b) and q'.rel 1 1, we get q'.rel (n•a + 1) (n•b + 1) by add_mono
  -- It remains to show q'.rel (n•a) (n•b + 1).
  -- We have q'.rel (n•a) (n•b) and need q'.rel (n•b) (n•b + 1).
  -- q'.rel (n•b) (n•b + 1) follows from q'.rel 0 1 (zero_le) and add_mono.
  have hq'_nb_nb1 : q'.rel (n • b) (n • b + 1) := by
    have h01 : q'.rel 0 1 := q'.zero_le 1
    have := q'.add_mono 0 1 (n • b) h01
    simp only [zero_add] at this
    convert this using 1; ring
  have hq'_na_nb1 : q'.rel (n • a) (n • b + 1) := q'.trans _ _ _ hq'_na_nb hq'_nb_nb1
  -- Now we have q'.rel (n•a) (n•b + 1) and q'.rel (n•b + 1) (n•a).
  -- This means (n•a) ≈ (n•b + 1) in q'.
  -- Combined with q'.rel (n•a) (n•b), we get q'.rel (n•b + 1) (n•b) by transitivity.
  have hq'_nb1_nb : q'.rel (n • b + 1) (n • b) := q'.trans _ _ _ hq'_ext hq'_na_nb
  -- Rewrite to form (a + b) ≤ (a' + b) for asymp_of_add_cancel
  -- hq'_nb1_nb : q'.rel (n•b + 1) (n•b)
  -- We need: q'.rel (1 + n•b) (0 + n•b)
  have hq'_rewrite : q'.rel (1 + n • b) (0 + n • b) := by
    convert hq'_nb1_nb using 1 <;> ring
  -- By asymp_of_add_cancel: AsympRel q' 1 0
  have hasym_1_0 : AsympRel q' 1 0 := q'.asymp_of_add_cancel hq'_rewrite
  -- Since q' is maximal, q'.rel = AsympRel q' (asymptotically closed)
  have hq'_closed := maximal_eq_asymp q' hq'max
  -- So q'.rel 1 0
  have hq'_1_0 : q'.rel 1 0 := by rw [hq'_closed]; exact hasym_1_0
  -- By nat_compat: 1 ≤ 0 in ℕ, contradiction
  exact q'.not_rel_one_zero hq'_1_0

/-- Completeness: a ≲_p b iff a ≤ b for all maximal extensions of p.
    (Lemma str_complete) -/
theorem asymp_iff_forall_maximal (p : StrassenPreorder S) (a b : S) :
    AsympRel p a b ↔ ∀ q : StrassenPreorder S, p ≤ q → q.IsMaximal → q.rel a b := by
  constructor
  · -- Forward: if a ≲ b then for all maximal q ⊇ p, a ≤_q b
    intro hasym q hpq hqmax
    -- a ≲_p b and p ≤ q, so we need a ≲_q b? No, we need q.rel a b.
    -- Since q is maximal, q = q≲, so we need a ≲_q b.
    -- From a ≲_p b and p ≤ q, we can show a ≲_q b.
    have hasym_q : AsympRel q a b := by
      -- AsympRel p a b means ∃ x, ∀n≥1, p.rel (a^n) (b^n * x n) ∧ lim x^(1/n) = 1
      -- Since p ≤ q, p.rel implies q.rel, so we get AsympRel q a b
      obtain ⟨x, hx_rel, hx_lim⟩ := hasym
      refine ⟨x, ?_, hx_lim⟩
      intro n hn
      exact hpq _ _ (hx_rel n hn)
    exact asymp_implies_maximal q hqmax hasym_q
  · -- Backward: if ∀ maximal q ⊇ p, a ≤_q b, then a ≲_p b
    exact forall_maximal_implies_asymp p

end AsymptoticSpectrumDuality
