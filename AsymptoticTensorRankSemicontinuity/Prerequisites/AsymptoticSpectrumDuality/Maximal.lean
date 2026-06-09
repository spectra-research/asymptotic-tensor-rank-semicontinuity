/-
Copyright (c) 2024 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.AsymptoticSpectrumDuality.StrassenProps
import Mathlib.Order.Zorn

/-!
# Maximal Strassen Preorders

This file proves the existence of maximal Strassen preorders using Zorn's lemma,
and establishes their key properties: totality and closure under asymptotic.

## Main Results

* `exists_maximal_strassen` : Every Strassen preorder extends to a maximal one
* `maximal_is_total` : Maximal Strassen preorders are total (Lemma str_total)
* `maximal_eq_asymp` : Maximal preorders are closed under asymptotic (Lemma str_maxisclos)
* `extend_strassen` : Extension lemma for non-comparable pairs (Lemma str_extend)

## References

* Strassen (1988), The asymptotic spectrum of tensors
-/

namespace AsymptoticSpectrumDuality

open StrassenPreorder

variable {S : Type*} [CommSemiring S]

/-! ### The Poset of Strassen Preorders -/

/-- The set of Strassen preorders containing p, ordered by inclusion -/
def StrassenPoset (p : StrassenPreorder S) :=
  { q : StrassenPreorder S // p ≤ q }

instance (p : StrassenPreorder S) : LE (StrassenPoset p) where
  le q r := q.val ≤ r.val

instance (p : StrassenPreorder S) : Preorder (StrassenPoset p) where
  le := (· ≤ ·)
  le_refl q := le_refl q.val
  le_trans q r s hqr hrs := le_trans hqr hrs

/-- The union of a chain of Strassen preorders is a Strassen preorder -/
theorem chain_sup_strassen (p : StrassenPreorder S)
    (c : Set (StrassenPoset p)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
    ∃ q : StrassenPreorder S, p ≤ q ∧ ∀ r ∈ c, r.val ≤ q := by
  -- Define the union relation: a ≤_∪ b iff ∃ r ∈ c, a ≤_r b
  let unionRel : S → S → Prop := fun a b => ∃ r ∈ c, r.val.rel a b
  -- Prove this is a Strassen preorder
  have hrefl : ∀ a, unionRel a a := by
    intro a
    obtain ⟨r, hr⟩ := hne
    exact ⟨r, hr, r.val.refl a⟩
  have htrans : ∀ a b d, unionRel a b → unionRel b d → unionRel a d := by
    intro a b d ⟨r1, hr1, hab⟩ ⟨r2, hr2, hbd⟩
    -- r1 and r2 are comparable in the chain
    rcases hc.total hr1 hr2 with hle | hge
    · -- r1 ≤ r2, so use r2
      exact ⟨r2, hr2, r2.val.trans a b d (hle a b hab) hbd⟩
    · -- r2 ≤ r1, so use r1
      exact ⟨r1, hr1, r1.val.trans a b d hab (hge b d hbd)⟩
  have hzero : ∀ a, unionRel 0 a := by
    intro a
    obtain ⟨r, hr⟩ := hne
    exact ⟨r, hr, r.val.zero_le a⟩
  have hnat : ∀ n m : ℕ, n ≤ m ↔ unionRel (n : S) (m : S) := by
    intro n m
    constructor
    · intro hnm
      obtain ⟨r, hr⟩ := hne
      exact ⟨r, hr, (r.val.nat_compat n m).mp hnm⟩
    · intro ⟨r, _, hr⟩
      exact (r.val.nat_compat n m).mpr hr
  have hadd : ∀ a b s, unionRel a b → unionRel (a + s) (b + s) := by
    intro a b s ⟨r, hr, hab⟩
    exact ⟨r, hr, r.val.add_mono a b s hab⟩
  have hmul : ∀ a b s, unionRel a b → unionRel (a * s) (b * s) := by
    intro a b s ⟨r, hr, hab⟩
    exact ⟨r, hr, r.val.mul_mono a b s hab⟩
  have harch : ∀ a b, b ≠ 0 → ∃ r : ℕ, unionRel a (r * b) := by
    intro a b hb
    obtain ⟨s, hs⟩ := hne
    obtain ⟨r, hr⟩ := s.val.archimedean a b hb
    exact ⟨r, s, hs, hr⟩
  -- Package into StrassenPreorder
  let q : StrassenPreorder S := {
    rel := unionRel
    refl := hrefl
    trans := htrans
    zero_le := hzero
    nat_compat := hnat
    add_mono := hadd
    mul_mono := hmul
    archimedean := harch
  }
  refine ⟨q, ?_, ?_⟩
  · -- p ≤ q
    intro a b hab
    obtain ⟨r, hr⟩ := hne
    have hpr : p ≤ r.val := r.property
    exact ⟨r, hr, hpr a b hab⟩
  · -- ∀ r ∈ c, r.val ≤ q
    intro r hr a b hab
    exact ⟨r, hr, hab⟩

/-- Every Strassen preorder extends to a maximal one (Zorn's lemma) -/
theorem exists_maximal_strassen (p : StrassenPreorder S) :
    ∃ q : StrassenPreorder S, p ≤ q ∧ q.IsMaximal := by
  -- Apply Zorn's lemma
  have hzorn : ∃ m : StrassenPoset p, IsMax m := zorn_le ?_
  · obtain ⟨m, hmmax⟩ := hzorn
    refine ⟨m.val, m.property, fun r hr => ?_⟩
    -- r ≥ m.val and we want r ≤ m.val
    -- First show p ≤ r
    have hpr : p ≤ r := StrassenPreorder.le_trans m.property hr
    -- Form r as element of StrassenPoset p
    let r' : StrassenPoset p := ⟨r, hpr⟩
    -- r' ≥ m in StrassenPoset
    have hr' : m ≤ r' := hr
    -- By maximality of m, r' ≤ m
    exact hmmax hr'
  · -- Every chain has an upper bound
    intro c hc
    by_cases hne : c.Nonempty
    · obtain ⟨q, hpq, hq⟩ := chain_sup_strassen p c hc hne
      exact ⟨⟨q, hpq⟩, fun r hr => hq r hr⟩
    · -- Empty chain: use p itself
      simp only [Set.not_nonempty_iff_eq_empty] at hne
      exact ⟨⟨p, StrassenPreorder.le_refl p⟩, fun r hr => (hne ▸ hr : r ∈ (∅ : Set _)).elim⟩

/-! ### Extension Lemma -/

/-- Lemma str_extend: If p = p≲ and a ̸≤_p b, then there exists q ⊇ p with b ≤_q a.
    Construction: x ≤_{a,b} y iff ∃ s, x + sa ≤_p y + sb -/
theorem extend_strassen (p : StrassenPreorder S)
    (hp : p.rel = (asympPreorder p).rel) (a b : S) (hnab : ¬ p.rel a b) :
    ∃ q : StrassenPreorder S, p ≤ q ∧ q.rel b a := by
  -- Define the extended relation
  let extRel : S → S → Prop := fun x y => ∃ s : S, p.rel (x + s * a) (y + s * b)
  -- Prove it's reflexive
  have hrefl : ∀ x, extRel x x := by
    intro x
    exact ⟨0, by simp only [zero_mul, add_zero]; exact p.refl x⟩
  -- Prove it's transitive
  have htrans : ∀ x y z, extRel x y → extRel y z → extRel x z := by
    intro x y z ⟨s, hs⟩ ⟨t, ht⟩
    use s + t
    -- From hs: x + s*a ≤ y + s*b
    -- From ht: y + t*a ≤ z + t*b
    -- Want: x + (s+t)*a ≤ z + (s+t)*b
    -- Strategy: add t*a to hs, add s*b to ht, then chain
    have hs' : p.rel (x + s * a + t * a) (y + s * b + t * a) := p.add_mono _ _ (t * a) hs
    have ht' : p.rel (y + t * a + s * b) (z + t * b + s * b) := p.add_mono _ _ (s * b) ht
    -- Note: y + s*b + t*a = y + t*a + s*b by commutativity
    have eq1 : y + s * b + t * a = y + t * a + s * b := by ring
    rw [eq1] at hs'
    -- Now hs': x + s*a + t*a ≤ y + t*a + s*b
    --     ht': y + t*a + s*b ≤ z + t*b + s*b
    have hchain : p.rel (x + s * a + t * a) (z + t * b + s * b) := p.trans _ _ _ hs' ht'
    -- Simplify: x + s*a + t*a = x + (s+t)*a and z + t*b + s*b = z + (s+t)*b
    have eq2 : x + s * a + t * a = x + (s + t) * a := by ring
    have eq3 : z + t * b + s * b = z + (s + t) * b := by ring
    rw [eq2, eq3] at hchain
    exact hchain
  -- Prove zero_le
  have hzero : ∀ x, extRel 0 x := by
    intro x
    exact ⟨0, by simp only [zero_mul, add_zero]; exact p.zero_le x⟩
  -- Other properties
  have hnat : ∀ n m : ℕ, n ≤ m ↔ extRel (n : S) (m : S) := by
    intro n m
    constructor
    · intro hnm
      exact ⟨0, by simp only [zero_mul, add_zero]; exact (p.nat_compat n m).mp hnm⟩
    · intro ⟨s, hs⟩
      -- Key: if n + sa ≤ m + sb but a ̸≤ b, then we must have n ≤ m
      -- This uses that p = p≲ (asymptotically closed)
      by_cases hs0 : s = 0
      · simp only [hs0, zero_mul, add_zero] at hs
        exact (p.nat_compat n m).mpr hs
      · -- When s ≠ 0, the argument uses asymptotic cancellation:
        -- From (n + sa) ≤_p (m + sb) and a ̸≤_p b, if n > m, then
        -- iterating would give a ≲ b (contradiction with hnab).
        by_contra hgt
        push_neg at hgt
        -- hgt : m < n, so m + 1 ≤ n
        have hmn : m + 1 ≤ n := hgt
        -- Step 1: p.rel (↑(m + 1)) (↑n) from nat_compat
        have hrel_mn : p.rel (↑(m + 1) : S) (↑n : S) := (p.nat_compat (m + 1) n).mp hmn
        -- Step 2: Add (n + s*a) to both sides of hrel_mn
        -- p.rel ((m + 1) + (n + s*a)) (n + (n + s*a))
        have h1 : p.rel ((↑(m + 1) : S) + (↑n + s * a)) ((↑n : S) + (↑n + s * a)) :=
          p.add_mono _ _ (↑n + s * a) hrel_mn
        -- Step 3: Add n to both sides of hs : p.rel (n + s*a) (m + s*b)
        -- p.rel (n + (n + s*a)) (n + (m + s*b))
        have h2 : p.rel ((↑n : S) + (↑n + s * a)) ((↑n : S) + (↑m + s * b)) := by
          have := p.add_mono _ _ (↑n : S) hs
          simp only [add_comm (↑n : S)] at this ⊢
          exact this
        -- Step 4: By transitivity: p.rel ((m + 1) + n + s*a) (n + m + s*b)
        have h3 : p.rel ((↑(m + 1) : S) + (↑n + s * a)) ((↑n : S) + (↑m + s * b)) :=
          p.trans _ _ _ h1 h2
        -- Rewrite to: p.rel ((1 + s*a) + (n + m)) ((s*b) + (n + m))
        have eq1 : (↑(m + 1) : S) + (↑n + s * a) = (1 + s * a) + (↑n + ↑m) := by
          simp only [Nat.cast_add, Nat.cast_one]; ring
        have eq2 : (↑n : S) + (↑m + s * b) = (s * b) + (↑n + ↑m) := by ring
        rw [eq1, eq2] at h3
        -- Step 5: Apply asymp_of_add_cancel: from (1 + s*a) + C ≤ (s*b) + C, get (1 + s*a) ≲ s*b
        have hasym1 : AsympRel p (1 + s * a) (s * b) := p.asymp_of_add_cancel h3
        -- Since p = p≲ (by hp), p.rel = AsympRel p, so hasym1 gives p.rel
        -- hp : p.rel = (asympPreorder p).rel, and (asympPreorder p).rel = AsympRel p
        have hasym1' : p.rel (1 + s * a) (s * b) := by rw [hp]; exact hasym1
        -- Step 6: From 0 ≤ 1 and add_mono, get s*a ≤ 1 + s*a
        have h4 : p.rel (s * a) (1 + s * a) := by
          have h0 := p.zero_le 1
          have h := p.add_mono 0 1 (s * a) h0
          -- h : p.rel (0 + s * a) (1 + s * a)
          simp only [zero_add] at h
          exact h
        -- Step 7: By transitivity: p.rel (s*a) (s*b)
        have h5 : p.rel (s * a) (s * b) := p.trans _ _ _ h4 hasym1'
        -- Rewrite using commutativity for asymp_of_mul_cancel (needs a*s not s*a)
        have h5' : p.rel (a * s) (b * s) := by
          simp only [mul_comm a s, mul_comm b s] at h5 ⊢; exact h5
        -- Step 8: Apply asymp_of_mul_cancel with s ≠ 0: a ≲ b
        have hasym2 : AsympRel p a b := p.asymp_of_mul_cancel hs0 h5'
        -- Since p = p≲, we have p.rel a b
        have hasym2' : p.rel a b := by rw [hp]; exact hasym2
        -- This contradicts hnab
        exact hnab hasym2'
  have hadd : ∀ x y t, extRel x y → extRel (x + t) (y + t) := by
    intro x y t ⟨s, hs⟩
    use s
    have h1 : (x + t + s * a) = (x + s * a + t) := by ring
    have h2 : (y + t + s * b) = (y + s * b + t) := by ring
    rw [h1, h2]
    exact p.add_mono _ _ t hs
  have hmul : ∀ x y t, extRel x y → extRel (x * t) (y * t) := by
    intro x y t ⟨s, hs⟩
    use s * t
    have h1 : (x * t + s * t * a) = (x + s * a) * t := by ring
    have h2 : (y * t + s * t * b) = (y + s * b) * t := by ring
    rw [h1, h2]
    exact p.mul_mono _ _ t hs
  have harch : ∀ x y, y ≠ 0 → ∃ r : ℕ, extRel x (r * y) := by
    intro x y hy
    obtain ⟨r, hr⟩ := p.archimedean x y hy
    exact ⟨r, 0, by simp only [zero_mul, add_zero]; exact hr⟩
  -- Package
  let q : StrassenPreorder S := {
    rel := extRel
    refl := hrefl
    trans := htrans
    zero_le := hzero
    nat_compat := hnat
    add_mono := hadd
    mul_mono := hmul
    archimedean := harch
  }
  refine ⟨q, ?_, ?_⟩
  · -- p ≤ q
    intro x y hxy
    exact ⟨0, by simp only [zero_mul, add_zero]; exact hxy⟩
  · -- q.rel b a
    exact ⟨1, by simp only [one_mul]; rw [add_comm a b]; exact p.refl (b + a)⟩

/-! ### Properties of Maximal Preorders -/

/-- Lemma str_maxisclos: If p is maximal, then p = p≲ (asymptotically closed) -/
theorem maximal_eq_asymp (p : StrassenPreorder S) (hmax : p.IsMaximal) :
    p.rel = (asympPreorder p).rel := by
  ext a b
  constructor
  · -- p.rel a b → (asympPreorder p).rel a b
    exact AsympRel.of_le
  · -- (asympPreorder p).rel a b → p.rel a b
    -- Since ≲ ⊇ ≤ and p is maximal, we have ≲ ⊆ ≤
    intro hasym
    have hle : p ≤ asympPreorder p := fun x y hxy => AsympRel.of_le hxy
    have hge : asympPreorder p ≤ p := hmax (asympPreorder p) hle
    exact hge a b hasym

/-- Lemma str_total: If p is maximal, then p is total -/
theorem maximal_is_total (p : StrassenPreorder S) (hmax : p.IsMaximal) :
    p.IsTotal := by
  intro a b
  by_contra h
  push_neg at h
  obtain ⟨hnab, hnba⟩ := h
  -- Use extend_strassen to get q ⊇ p with b ≤_q a
  have hpeq := maximal_eq_asymp p hmax
  obtain ⟨q, hpq, hqba⟩ := extend_strassen p hpeq a b hnab
  -- But then q > p, contradicting maximality
  have hqp : q ≤ p := hmax q hpq
  -- So p.rel b a, contradiction with hnba
  exact hnba (hqp b a hqba)

end AsymptoticSpectrumDuality
