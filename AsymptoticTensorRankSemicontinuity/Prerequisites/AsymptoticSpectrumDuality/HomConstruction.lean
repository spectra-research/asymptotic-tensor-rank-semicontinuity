/-
Copyright (c) 2024 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.AsymptoticSpectrumDuality.Maximal

/-!
# Homomorphism Construction from Strassen Preorders

This file constructs the semiring homomorphism φ from a total Strassen preorder
to the nonnegative reals, following Lemma str_exis in Strassen (1988).

## Main Definitions

* `phiFromPreorder` : φ(a) = inf { r/s : sa ≤ r }
* `psiFromPreorder` : ψ(a) = sup { u/v : u ≤ va }

## Main Results

* `psi_le_phi` : ψ(a) ≤ φ(a)
* `phi_eq_psi_of_total` : For total preorders, φ = ψ
* `phi_is_hom_of_total` : For total preorders, φ is a semiring homomorphism
* `phi_monotone` : φ is monotone under the preorder
* `phi_reflects_of_maximal` : For maximal preorders, a ≤ b ↔ φ(a) ≤ φ(b)

## References

* Strassen (1988), The asymptotic spectrum of tensors, Lemma str_exis
-/

namespace AsymptoticSpectrumDuality

open StrassenPreorder

variable {S : Type*} [CommSemiring S]

/-! ### The φ and ψ Functions -/

/-- The set of ratios r/s where sa ≤ r -/
def phiSet (p : StrassenPreorder S) (a : S) : Set ℝ :=
  { x : ℝ | ∃ (r s : ℕ) (_ : s ≠ 0), p.rel (s • a) r ∧ x = (r : ℝ) / s }

/-- The set of ratios u/v where u ≤ va -/
def psiSet (p : StrassenPreorder S) (a : S) : Set ℝ :=
  { x : ℝ | ∃ (u v : ℕ) (_ : v ≠ 0), p.rel u (v • a) ∧ x = (u : ℝ) / v }

/-- φ(a) = inf { r/s : sa ≤ r } -/
noncomputable def phiFromPreorder (p : StrassenPreorder S) (a : S) : ℝ :=
  sInf (phiSet p a)

/-- ψ(a) = sup { u/v : u ≤ va } -/
noncomputable def psiFromPreorder (p : StrassenPreorder S) (a : S) : ℝ :=
  sSup (psiSet p a)

/-! ### Basic Properties of φ and ψ -/

/-- The phiSet is nonempty (by Archimedean property) -/
theorem phiSet_nonempty (p : StrassenPreorder S) (a : S) : (phiSet p a).Nonempty := by
  -- By archimedean property: for any a and b ≠ 0, there exists r with a ≤ r*b
  -- We need to find some nonzero b. Use b = 1 + a (which is nonzero by archimedean property
  -- of 1 with respect to b, or use zero_le differently)
  -- Actually simpler: by archimedean on (1•a) with respect to b = 1+1 = 2:
  -- First check if 1 = 0 in S (trivial ring) or not
  by_cases h : (1 : S) = 0
  · -- Trivial ring case: everything is 0, so 1•a = 0 ≤ 0
    use 0
    refine ⟨0, 1, Nat.one_ne_zero, ?_, by simp⟩
    simp only [one_smul, Nat.cast_zero]
    -- In trivial ring, a = a * 1 = a * 0 = 0
    have ha : a = 0 := by rw [← mul_one a, h, mul_zero]
    rw [ha]
    exact p.refl 0
  · -- Nontrivial case: use archimedean with b = 1
    obtain ⟨r, hr⟩ := p.archimedean a 1 h
    simp only [mul_one] at hr
    use (r : ℝ) / 1
    refine ⟨r, 1, Nat.one_ne_zero, ?_, by simp⟩
    simp only [one_smul]
    exact hr

/-- The psiSet contains 0 (since 0 ≤ 1•a) -/
theorem psiSet_has_zero (p : StrassenPreorder S) (a : S) : (0 : ℝ) ∈ psiSet p a := by
  refine ⟨0, 1, Nat.one_ne_zero, ?_, by simp⟩
  simp only [Nat.cast_zero, one_smul]
  exact p.zero_le a

/-- The psiSet is nonempty -/
theorem psiSet_nonempty (p : StrassenPreorder S) (a : S) : (psiSet p a).Nonempty :=
  ⟨0, psiSet_has_zero p a⟩

/-- The psiSet is bounded above by any element of phiSet -/
theorem psiSet_bddAbove_by_phiSet (p : StrassenPreorder S) (a : S) :
    ∀ x ∈ phiSet p a, ∀ y ∈ psiSet p a, y ≤ x := by
  intro x ⟨r, s, hs, hsa_r, hx⟩ y ⟨u, v, hv, hu_va, hy⟩
  subst hx hy
  -- We have s•a ≤ r and u ≤ v•a
  -- Multiply first by s: us ≤ (v•a)*s = (sv)•a
  -- Multiply second by v: (s•a)*v = (sv)•a ≤ rv
  -- Chain: us ≤ (sv)•a ≤ rv, so us ≤ rv
  -- Thus u/v ≤ r/s
  have h1 : p.rel (u * s) ((v • a) * s) := p.mul_mono _ _ s hu_va
  have h2 : p.rel ((s • a) * v) (r * v) := p.mul_mono _ _ v hsa_r
  -- Simplify: (v • a) * s = vs • a and (s • a) * v = sv • a = vs • a
  have eq1 : (v • a) * (s : S) = (v * s) • a := by
    simp only [nsmul_eq_mul, Nat.cast_mul]; ring
  have eq2 : (s • a) * (v : S) = (s * v) • a := by
    simp only [nsmul_eq_mul, Nat.cast_mul]; ring
  have eq3 : v * s = s * v := mul_comm v s
  rw [eq1] at h1
  rw [eq2] at h2
  rw [eq3] at h1
  -- Now h1 : u * s ≤ (s * v) • a and h2 : (s * v) • a ≤ r * v
  have hchain : p.rel ((u * s : ℕ) : S) ((r * v : ℕ) : S) := by
    simp only [Nat.cast_mul]
    exact p.trans _ _ _ h1 h2
  -- Convert to naturals: us ≤ rv in ℕ (by nat_compat)
  have hnat : (u * s : ℕ) ≤ (r * v : ℕ) := (p.nat_compat _ _).mpr hchain
  -- Now u/v ≤ r/s follows from us ≤ rv and s,v > 0
  have hs' : (0 : ℝ) < s := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs)
  have hv' : (0 : ℝ) < v := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hv)
  rw [div_le_div_iff₀ hv' hs']
  calc (u : ℝ) * s = ((u * s : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((r * v : ℕ) : ℝ) := by exact mod_cast hnat
    _ = r * v := by push_cast; ring

/-- The psiSet is bounded above -/
theorem psiSet_bddAbove (p : StrassenPreorder S) (a : S) : BddAbove (psiSet p a) := by
  obtain ⟨x, hx⟩ := phiSet_nonempty p a
  exact ⟨x, fun y hy => psiSet_bddAbove_by_phiSet p a x hx y hy⟩

/-- The phiSet is bounded below by ψ(a) -/
theorem phiSet_bddBelow (p : StrassenPreorder S) (a : S) : BddBelow (phiSet p a) := by
  use 0
  intro x ⟨r, s, hs, _, hx⟩
  subst hx
  exact div_nonneg (Nat.cast_nonneg r) (Nat.cast_nonneg s)

/-- ψ(a) ≤ φ(a) -/
theorem psi_le_phi (p : StrassenPreorder S) (a : S) :
    psiFromPreorder p a ≤ phiFromPreorder p a := by
  apply csSup_le (psiSet_nonempty p a)
  intro y hy
  apply le_csInf (phiSet_nonempty p a)
  intro x hx
  exact psiSet_bddAbove_by_phiSet p a x hx y hy

/-! ### Properties of φ -/

/-- φ(0) = 0 -/
theorem phi_zero (p : StrassenPreorder S) : phiFromPreorder p (0 : S) = 0 := by
  apply le_antisymm
  · -- φ(0) ≤ 0: show 0 ∈ phiSet
    apply csInf_le (phiSet_bddBelow p 0)
    refine ⟨0, 1, one_ne_zero, ?_, by simp⟩
    simp only [one_smul, Nat.cast_zero]
    exact p.refl 0
  · -- 0 ≤ φ(0): phiSet elements are nonnegative
    apply le_csInf (phiSet_nonempty p 0)
    intro x ⟨r, s, hs, _, hx⟩
    subst hx
    exact div_nonneg (Nat.cast_nonneg r) (Nat.cast_nonneg s)

/-- φ(1) = 1 -/
theorem phi_one (p : StrassenPreorder S) : phiFromPreorder p (1 : S) = 1 := by
  apply le_antisymm
  · -- φ(1) ≤ 1: show 1 ∈ phiSet, i.e., 1•1 ≤ 1 (reflexivity)
    apply csInf_le (phiSet_bddBelow p 1)
    refine ⟨1, 1, Nat.one_ne_zero, ?_, by simp⟩
    simp only [one_smul, Nat.cast_one]
    exact p.refl 1
  · -- 1 ≤ φ(1): for any r/s in phiSet with s•1 ≤ r, we have s ≤ r, so 1 ≤ r/s
    apply le_csInf (phiSet_nonempty p 1)
    intro x ⟨r, s, hs, hrel, hx⟩
    subst hx
    have hs1r : p.rel (s • (1 : S)) r := hrel
    simp only [nsmul_eq_mul, mul_one] at hs1r
    -- s ≤ r in the preorder, so s ≤ r as naturals
    have hsr : (s : ℕ) ≤ r := (p.nat_compat _ _).mpr hs1r
    have hs' : (0 : ℝ) < s := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs)
    rw [le_div_iff₀ hs']
    simp only [one_mul]
    exact mod_cast hsr

/-- φ is monotone: if a ≤ b then φ(a) ≤ φ(b) -/
theorem phi_monotone (p : StrassenPreorder S) {a b : S} (hab : p.rel a b) :
    phiFromPreorder p a ≤ phiFromPreorder p b := by
  -- If x ∈ phiSet(b), i.e., s•b ≤ r, then s•a ≤ s•b ≤ r, so x ∈ phiSet(a) conceptually
  -- Actually we show phiSet(b) ⊆ phiSet(a), so inf of larger set ≤ inf of smaller
  apply csInf_le_csInf (phiSet_bddBelow p a) (phiSet_nonempty p b)
  intro x ⟨r, s, hs, hsb_r, hx⟩
  refine ⟨r, s, hs, ?_, hx⟩
  -- Need s•a ≤ r, we have s•b ≤ r
  have hsa_sb : p.rel (s • a) (s • b) := p.nsmul_mono s hab
  exact p.trans _ _ _ hsa_sb hsb_r

/-! ### φ = ψ for Total Preorders -/

/-- For total preorders, φ(a) = ψ(a) -/
theorem phi_eq_psi_of_total (p : StrassenPreorder S) (htotal : p.IsTotal) (a : S) :
    phiFromPreorder p a = psiFromPreorder p a := by
  apply le_antisymm
  · -- φ(a) ≤ ψ(a): Uses totality
    -- Key: For total preorder, every ratio r/s (s ≠ 0) is in phiSet ∪ psiSet
    -- Proof by contradiction: if φ(a) > ψ(a), find r/s between them
    -- Then r/s ∉ phiSet (since r/s < φ(a)) and r/s ∉ psiSet (since r/s > ψ(a))
    -- But totality says r/s ∈ phiSet ∪ psiSet, contradiction
    by_contra h
    push_neg at h
    -- h : ψ(a) < φ(a)
    have hpsi_lt_phi : psiFromPreorder p a < phiFromPreorder p a := h
    -- There exists a rational r/s between ψ(a) and φ(a)
    have hgap : 0 < phiFromPreorder p a - psiFromPreorder p a := sub_pos.mpr hpsi_lt_phi
    -- Use density of rationals: find natural r, s with ψ(a) < r/s < φ(a)
    -- Since psi contains 0, ψ(a) ≥ 0
    have hpsi_nn : 0 ≤ psiFromPreorder p a := le_csSup
        (psiSet_bddAbove p a) (psiSet_has_zero p a)
    -- The midpoint is positive
    set mid := (psiFromPreorder p a + phiFromPreorder p a) / 2 with hmid_def
    have hmid_pos : 0 < mid := by linarith
    have hmid_lt_phi : mid < phiFromPreorder p a := by linarith
    have hmid_gt_psi : psiFromPreorder p a < mid := by linarith
    -- Find a rational between ψ(a) and φ(a)
    obtain ⟨q, hq_gt, hq_lt⟩ := exists_rat_btwn hpsi_lt_phi
    have hq_pos : (0 : ℝ) < q := lt_of_le_of_lt hpsi_nn hq_gt
    have hq_pos' : (0 : ℚ) < q := by exact_mod_cast hq_pos
    -- Convert q to r/s with r, s ∈ ℕ
    have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq_pos'
    set r := q.num.natAbs with hr_def
    set s := q.den with hs_def
    have hs_ne : s ≠ 0 := q.den_ne_zero
    have hq_eq : (q : ℝ) = (r : ℝ) / s := by
      simp only [Rat.cast_def, hr_def, hs_def]
      congr 1
      simp only [Nat.cast_natAbs, abs_of_pos hnum_pos]
    -- By totality: either s•a ≤ r or r ≤ s•a
    rcases htotal (s • a) r with hphi_mem | hpsi_mem
    · -- Case: s•a ≤ r, so r/s ∈ phiSet
      have hmem : (r : ℝ) / s ∈ phiSet p a := ⟨r, s, hs_ne, hphi_mem, rfl⟩
      -- But inf of phiSet ≤ r/s < φ(a), contradicting φ(a) = inf phiSet
      have hle : phiFromPreorder p a ≤ (r : ℝ) / s :=
        csInf_le (phiSet_bddBelow p a) hmem
      rw [hq_eq] at hq_lt
      linarith
    · -- Case: r ≤ s•a, so r/s ∈ psiSet
      have hmem : (r : ℝ) / s ∈ psiSet p a := ⟨r, s, hs_ne, hpsi_mem, rfl⟩
      -- But r/s ≤ sup of psiSet = ψ(a) < r/s, contradiction
      have hle : (r : ℝ) / s ≤ psiFromPreorder p a :=
        le_csSup (psiSet_bddAbove p a) hmem
      rw [hq_eq] at hq_gt
      linarith
  · -- ψ(a) ≤ φ(a): Already proved
    exact psi_le_phi p a

/-! ### φ is a Semiring Homomorphism for Total Preorders -/

/-- φ(a + b) = φ(a) + φ(b) for total preorders -/
theorem phi_add (p : StrassenPreorder S) (htotal : p.IsTotal) (a b : S) :
    phiFromPreorder p (a + b) = phiFromPreorder p a + phiFromPreorder p b := by
  apply le_antisymm
  · -- φ(a + b) ≤ φ(a) + φ(b)
    -- For any x ∈ phiSet(a) and y ∈ phiSet(b), show x + y is achievable
    apply le_of_forall_pos_lt_add
    intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    -- Get x ∈ phiSet(a) close to φ(a)
    have hxa := (Real.lt_sInf_add_pos (phiSet_nonempty p a) hε2)
    obtain ⟨x, hx_mem, hx_lt⟩ := hxa
    obtain ⟨r₁, s₁, hs₁, hrel₁, hx_eq⟩ := hx_mem
    -- Get y ∈ phiSet(b) close to φ(b)
    have hyb := (Real.lt_sInf_add_pos (phiSet_nonempty p b) hε2)
    obtain ⟨y, hy_mem, hy_lt⟩ := hyb
    obtain ⟨r₂, s₂, hs₂, hrel₂, hy_eq⟩ := hy_mem
    -- Construct witness for a + b
    -- s₁•a ≤ r₁ and s₂•b ≤ r₂
    -- Then (s₁*s₂)•(a+b) ≤ s₂*r₁ + s₁*r₂
    have hs₁s₂_ne : s₁ * s₂ ≠ 0 := Nat.mul_ne_zero hs₁ hs₂
    have hsum_mem : ((s₂ * r₁ + s₁ * r₂ : ℕ) : ℝ) / (s₁ * s₂ : ℕ) ∈ phiSet p (a + b) := by
      refine ⟨s₂ * r₁ + s₁ * r₂, s₁ * s₂, hs₁s₂_ne, ?_, rfl⟩
      -- Need: (s₁*s₂)•(a+b) ≤ s₂*r₁ + s₁*r₂
      have h1 : p.rel (s₂ • (s₁ • a)) (s₂ • (r₁ : S)) := p.nsmul_mono s₂ hrel₁
      have h2 : p.rel (s₁ • (s₂ • b)) (s₁ • (r₂ : S)) := p.nsmul_mono s₁ hrel₂
      have h12 := p.add_mono_both h1 h2
      simp only [← mul_smul, mul_comm s₁ s₂] at h12
      convert h12 using 1 <;> simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_add]
      ring
    have hsum_eq : ((s₂ * r₁ + s₁ * r₂ : ℕ) : ℝ) / (s₁ * s₂ : ℕ) = x + y := by
      subst hx_eq hy_eq
      push_cast
      have hs₁' : (s₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs₁
      have hs₂' : (s₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs₂
      field_simp
    calc phiFromPreorder p (a + b) ≤ ((s₂ * r₁ + s₁ * r₂ : ℕ) : ℝ) / (s₁ * s₂ : ℕ) :=
            csInf_le (phiSet_bddBelow p (a + b)) hsum_mem
      _ = x + y := hsum_eq
      _ < (phiFromPreorder p a + ε / 2) + (phiFromPreorder p b + ε / 2) := add_lt_add hx_lt hy_lt
      _ = phiFromPreorder p a + phiFromPreorder p b + ε := by ring
  · -- φ(a + b) ≥ φ(a) + φ(b) using ψ and totality
    -- For total preorders, φ = ψ, and ψ(a) + ψ(b) ≤ ψ(a + b)
    rw [phi_eq_psi_of_total p htotal a, phi_eq_psi_of_total p htotal b,
        phi_eq_psi_of_total p htotal (a + b)]
    -- Show ψ(a) + ψ(b) ≤ ψ(a + b): for any u₁/v₁ ∈ psiSet(a) and u₂/v₂ ∈ psiSet(b),
    -- we have u₁/v₁ + u₂/v₂ ∈ psiSet(a + b), so x + y ≤ ψ(a+b)
    -- Taking supremum: ψ(a) + ψ(b) ≤ ψ(a+b)
    have h : ∀ x ∈ psiSet p a, ∀ y ∈ psiSet p b, x + y ≤ psiFromPreorder p (a + b) := by
      intro x hx_mem y hy_mem
      obtain ⟨u₁, v₁, hv₁, hrel₁, hx_eq⟩ := hx_mem
      obtain ⟨u₂, v₂, hv₂, hrel₂, hy_eq⟩ := hy_mem
      subst hx_eq hy_eq
      have hv₁v₂_ne : v₁ * v₂ ≠ 0 := Nat.mul_ne_zero hv₁ hv₂
      have hsum_mem : ((v₂ * u₁ + v₁ * u₂ : ℕ) : ℝ) / (v₁ * v₂ : ℕ) ∈ psiSet p (a + b) := by
        refine ⟨v₂ * u₁ + v₁ * u₂, v₁ * v₂, hv₁v₂_ne, ?_, rfl⟩
        -- Need: v₂*u₁ + v₁*u₂ ≤ (v₁*v₂)•(a+b)
        have h1 : p.rel (v₂ • (u₁ : S)) (v₂ • (v₁ • a)) := p.nsmul_mono v₂ hrel₁
        have h2 : p.rel (v₁ • (u₂ : S)) (v₁ • (v₂ • b)) := p.nsmul_mono v₁ hrel₂
        simp only [← mul_smul, mul_comm v₁ v₂] at h1 h2
        have h12 := p.add_mono_both h1 h2
        convert h12 using 1 <;> simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_add]
        ring
      have hsum_eq : ((v₂ * u₁ + v₁ * u₂ : ℕ) : ℝ) / (v₁ * v₂ : ℕ) =
          (u₁ : ℝ) / v₁ + (u₂ : ℝ) / v₂ := by
        push_cast
        have hv₁' : (v₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hv₁
        have hv₂' : (v₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hv₂
        field_simp
      calc (u₁ : ℝ) / v₁ + (u₂ : ℝ) / v₂ = ((v₂ * u₁ + v₁ * u₂ : ℕ) : ℝ) / (v₁ * v₂ : ℕ) :=
              hsum_eq.symm
        _ ≤ psiFromPreorder p (a + b) := le_csSup (psiSet_bddAbove p (a + b)) hsum_mem
    -- Now use: if ∀ x ∈ A, ∀ y ∈ B, x + y ≤ c, then sSup A + sSup B ≤ c
    -- Strategy: for any y ∈ B, ∀ x ∈ A, x ≤ c - y, so sSup A ≤ c - y, hence y ≤ c - sSup A
    have hstep : ∀ y ∈ psiSet p b, y ≤ psiFromPreorder p (a + b) - sSup (psiSet p a) := by
      intro y hy_mem
      have h1 : ∀ x ∈ psiSet p a, x ≤ psiFromPreorder p (a + b) - y := by
        intro x hx_mem
        linarith [h x hx_mem y hy_mem]
      have h2 : sSup (psiSet p a) ≤ psiFromPreorder p (a + b) - y :=
        csSup_le (psiSet_nonempty p a) h1
      linarith
    have hfinal : sSup (psiSet p b) ≤ psiFromPreorder p (a + b) - sSup (psiSet p a) :=
      csSup_le (psiSet_nonempty p b) hstep
    simp only [psiFromPreorder] at hfinal ⊢
    linarith

/-- φ(a * b) = φ(a) * φ(b) for total preorders -/
theorem phi_mul (p : StrassenPreorder S) (htotal : p.IsTotal) (a b : S) :
    phiFromPreorder p (a * b) = phiFromPreorder p a * phiFromPreorder p b := by
  apply le_antisymm
  · -- φ(a * b) ≤ φ(a) * φ(b)
    -- For any ε > 0, find x ∈ phiSet(a) and y ∈ phiSet(b) close to the infima
    apply le_of_forall_pos_lt_add
    intro ε hε
    -- We need to handle the case when φ(a) or φ(b) is close to 0 carefully
    -- Use: (φ(a) + δ)(φ(b) + δ) = φ(a)φ(b) + δ(φ(a) + φ(b)) + δ²
    -- Choose δ small enough that δ(φ(a) + φ(b) + δ) < ε
    have hphi_a_nn : 0 ≤ phiFromPreorder p a := by
      apply le_csInf (phiSet_nonempty p a)
      intro x ⟨r, s, hs, _, hx⟩; subst hx
      exact div_nonneg (Nat.cast_nonneg r) (Nat.cast_nonneg s)
    have hphi_b_nn : 0 ≤ phiFromPreorder p b := by
      apply le_csInf (phiSet_nonempty p b)
      intro x ⟨r, s, hs, _, hx⟩; subst hx
      exact div_nonneg (Nat.cast_nonneg r) (Nat.cast_nonneg s)
    set M := phiFromPreorder p a + phiFromPreorder p b + 1 with hM_def
    have hM_pos : 0 < M := by linarith
    set δ := min (ε / (2 * M)) 1 with hδ_def
    have hδ_pos : 0 < δ := by
      simp only [hδ_def, lt_min_iff]
      constructor
      · exact div_pos hε (by linarith)
      · linarith
    have hδ_le : δ ≤ 1 := min_le_right _ _
    have hδ_bound : δ * M ≤ ε / 2 := by
      calc δ * M ≤ (ε / (2 * M)) * M := by
            apply mul_le_mul_of_nonneg_right (min_le_left _ _) (le_of_lt hM_pos)
        _ = ε / 2 := by field_simp
    -- Get x ∈ phiSet(a) close to φ(a)
    have hxa := (Real.lt_sInf_add_pos (phiSet_nonempty p a) hδ_pos)
    obtain ⟨x, hx_mem, hx_lt⟩ := hxa
    obtain ⟨r₁, s₁, hs₁, hrel₁, hx_eq⟩ := hx_mem
    -- Get y ∈ phiSet(b) close to φ(b)
    have hyb := (Real.lt_sInf_add_pos (phiSet_nonempty p b) hδ_pos)
    obtain ⟨y, hy_mem, hy_lt⟩ := hyb
    obtain ⟨r₂, s₂, hs₂, hrel₂, hy_eq⟩ := hy_mem
    -- Show (r₁ * r₂) / (s₁ * s₂) ∈ phiSet(a * b)
    have hs₁s₂_ne : s₁ * s₂ ≠ 0 := Nat.mul_ne_zero hs₁ hs₂
    have hprod_mem : ((r₁ * r₂ : ℕ) : ℝ) / (s₁ * s₂ : ℕ) ∈ phiSet p (a * b) := by
      refine ⟨r₁ * r₂, s₁ * s₂, hs₁s₂_ne, ?_, rfl⟩
      -- Need: (s₁*s₂)•(a*b) ≤ r₁*r₂
      -- (s₁*s₂)•(a*b) = (s₁•a)*(s₂•b) and (s₁•a)*(s₂•b) ≤ r₁*r₂
      have h1 := p.mul_mono_both hrel₁ hrel₂
      simp only [nsmul_eq_mul, Nat.cast_mul] at h1 ⊢
      convert h1 using 1
      ring
    have hprod_eq : ((r₁ * r₂ : ℕ) : ℝ) / (s₁ * s₂ : ℕ) = x * y := by
      subst hx_eq hy_eq
      push_cast
      have hs₁' : (s₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs₁
      have hs₂' : (s₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs₂
      field_simp
    have hx_nn : 0 ≤ x := by subst hx_eq; exact div_nonneg (Nat.cast_nonneg r₁) (Nat.cast_nonneg s₁)
    have hy_nn : 0 ≤ y := by subst hy_eq; exact div_nonneg (Nat.cast_nonneg r₂) (Nat.cast_nonneg s₂)
    have hx_bound : x < phiFromPreorder p a + δ := hx_lt
    have hy_bound : y < phiFromPreorder p b + δ := hy_lt
    calc phiFromPreorder p (a * b) ≤ ((r₁ * r₂ : ℕ) : ℝ) / (s₁ * s₂ : ℕ) :=
            csInf_le (phiSet_bddBelow p (a * b)) hprod_mem
      _ = x * y := hprod_eq
      _ ≤ (phiFromPreorder p a + δ) * (phiFromPreorder p b + δ) := by
          apply mul_le_mul (le_of_lt hx_bound) (le_of_lt hy_bound) hy_nn (by linarith)
      _ = phiFromPreorder p a * phiFromPreorder p b +
          δ * (phiFromPreorder p a + phiFromPreorder p b + δ) := by ring
      _ ≤ phiFromPreorder p a * phiFromPreorder p b + δ * M := by
          have h1 : phiFromPreorder p a + phiFromPreorder p b + δ ≤ M := by linarith
          have h2 : δ * (phiFromPreorder p a + phiFromPreorder p b + δ) ≤ δ * M :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt hδ_pos)
          linarith
      _ ≤ phiFromPreorder p a * phiFromPreorder p b + ε / 2 := by linarith [hδ_bound]
      _ < phiFromPreorder p a * phiFromPreorder p b + ε := by linarith
  · -- φ(a * b) ≥ φ(a) * φ(b) using ψ and totality
    rw [phi_eq_psi_of_total p htotal a, phi_eq_psi_of_total p htotal b,
        phi_eq_psi_of_total p htotal (a * b)]
    -- For any x ∈ psiSet(a) and y ∈ psiSet(b), x * y ∈ psiSet(a * b)
    have h : ∀ x ∈ psiSet p a, ∀ y ∈ psiSet p b, x * y ≤ psiFromPreorder p (a * b) := by
      intro x hx_mem y hy_mem
      obtain ⟨u₁, v₁, hv₁, hrel₁, hx_eq⟩ := hx_mem
      obtain ⟨u₂, v₂, hv₂, hrel₂, hy_eq⟩ := hy_mem
      subst hx_eq hy_eq
      have hv₁v₂_ne : v₁ * v₂ ≠ 0 := Nat.mul_ne_zero hv₁ hv₂
      have hprod_mem : ((u₁ * u₂ : ℕ) : ℝ) / (v₁ * v₂ : ℕ) ∈ psiSet p (a * b) := by
        refine ⟨u₁ * u₂, v₁ * v₂, hv₁v₂_ne, ?_, rfl⟩
        -- Need: u₁*u₂ ≤ (v₁*v₂)•(a*b)
        have h12 := p.mul_mono_both hrel₁ hrel₂
        simp only [nsmul_eq_mul, Nat.cast_mul] at h12 ⊢
        convert h12 using 1
        ring
      have hprod_eq : ((u₁ * u₂ : ℕ) : ℝ) / (v₁ * v₂ : ℕ) =
          (u₁ : ℝ) / v₁ * ((u₂ : ℝ) / v₂) := by
        push_cast
        have hv₁' : (v₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hv₁
        have hv₂' : (v₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hv₂
        field_simp
      calc (u₁ : ℝ) / v₁ * ((u₂ : ℝ) / v₂) = ((u₁ * u₂ : ℕ) : ℝ) / (v₁ * v₂ : ℕ) := hprod_eq.symm
        _ ≤ psiFromPreorder p (a * b) := le_csSup (psiSet_bddAbove p (a * b)) hprod_mem
    -- Now: ψ(a) * ψ(b) ≤ ψ(a * b) using x * y ≤ ψ(ab) for all x, y
    have hpsi_a_nn : 0 ≤ psiFromPreorder p a := le_csSup (psiSet_bddAbove p a) (psiSet_has_zero p a)
    have hpsi_b_nn : 0 ≤ psiFromPreorder p b := le_csSup (psiSet_bddAbove p b) (psiSet_has_zero p b)
    -- Case split on whether ψ(a) = 0 or ψ(b) = 0
    by_cases ha0 : psiFromPreorder p a = 0
    · simp only [ha0, zero_mul]
      exact le_csSup (psiSet_bddAbove p (a * b)) (psiSet_has_zero p (a * b))
    by_cases hb0 : psiFromPreorder p b = 0
    · simp only [hb0, mul_zero]
      exact le_csSup (psiSet_bddAbove p (a * b)) (psiSet_has_zero p (a * b))
    -- Both ψ(a) > 0 and ψ(b) > 0
    have ha_pos : 0 < psiFromPreorder p a := hpsi_a_nn.lt_of_ne' ha0
    have hb_pos : 0 < psiFromPreorder p b := hpsi_b_nn.lt_of_ne' hb0
    -- Use: for all y ∈ psiSet(b), ψ(a) * y ≤ ψ(ab)
    have hstep1 : ∀ y ∈ psiSet p b, sSup (psiSet p a) * y ≤ psiFromPreorder p (a * b) := by
      intro y hy_mem
      have hy_nn : 0 ≤ y := by
        obtain ⟨u, v, _, _, hy_eq⟩ := hy_mem
        subst hy_eq
        exact div_nonneg (Nat.cast_nonneg u) (Nat.cast_nonneg v)
      by_cases hy0 : y = 0
      · simp only [hy0, mul_zero]
        exact le_csSup (psiSet_bddAbove p (a * b)) (psiSet_has_zero p (a * b))
      have hy_pos : 0 < y := hy_nn.lt_of_ne' hy0
      have h1 : ∀ x ∈ psiSet p a, x ≤ psiFromPreorder p (a * b) / y := by
        intro x hx_mem
        have hxy := h x hx_mem y hy_mem
        rwa [le_div_iff₀ hy_pos]
      have h2 : sSup (psiSet p a) ≤ psiFromPreorder p (a * b) / y :=
        csSup_le (psiSet_nonempty p a) h1
      rwa [← le_div_iff₀ hy_pos]
    have hstep2 : sSup (psiSet p a) * sSup (psiSet p b) ≤ psiFromPreorder p (a * b) := by
      have h3 : ∀ y ∈ psiSet p b, y ≤ psiFromPreorder p (a * b) / sSup (psiSet p a) := by
        intro y hy_mem
        have := hstep1 y hy_mem
        simp only [psiFromPreorder] at ha_pos
        rw [mul_comm] at this
        rwa [le_div_iff₀ ha_pos]
      have h4 : sSup (psiSet p b) ≤ psiFromPreorder p (a * b) / sSup (psiSet p a) :=
        csSup_le (psiSet_nonempty p b) h3
      simp only [psiFromPreorder] at ha_pos ⊢
      rw [mul_comm]
      rwa [← le_div_iff₀ ha_pos]
    simp only [psiFromPreorder]
    exact hstep2

/-- φ(n) = n for natural numbers -/
theorem phi_nat (p : StrassenPreorder S) (n : ℕ) :
    phiFromPreorder p (n : S) = n := by
  apply le_antisymm
  · -- φ(n) ≤ n: show n ∈ phiSet
    apply csInf_le (phiSet_bddBelow p (n : S))
    refine ⟨n, 1, Nat.one_ne_zero, ?_, by simp⟩
    simp only [one_smul]
    exact p.refl n
  · -- n ≤ φ(n): for any r/s in phiSet with s•n ≤ r, we have s*n ≤ r, so n ≤ r/s
    apply le_csInf (phiSet_nonempty p (n : S))
    intro x ⟨r, s, hs, hrel, hx⟩
    subst hx
    have hsn_r : p.rel (s • (n : S)) r := hrel
    simp only [nsmul_eq_mul] at hsn_r
    -- s * n ≤ r in the preorder, so s * n ≤ r as naturals
    have hnat : (s * n : ℕ) ≤ r := by
      have h : (s : S) * (n : S) = ((s * n : ℕ) : S) := by simp [Nat.cast_mul]
      rw [h] at hsn_r
      exact (p.nat_compat (s * n) r).mpr hsn_r
    have hs' : (0 : ℝ) < s := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs)
    rw [le_div_iff₀ hs']
    calc (n : ℝ) * s = (n * s : ℕ) := by push_cast; ring
      _ = (s * n : ℕ) := by ring_nf
      _ ≤ r := mod_cast hnat

/-! ### Reflection of Order for Maximal Preorders -/

/-- For maximal preorders, a ≤ b iff φ(a) ≤ φ(b) -/
theorem phi_reflects_of_maximal (p : StrassenPreorder S) (hmax : p.IsMaximal)
    (a b : S) : p.rel a b ↔ phiFromPreorder p a ≤ phiFromPreorder p b := by
  constructor
  · -- Forward: monotonicity
    exact fun h => phi_monotone p h
  · -- Backward: uses maximality (total + asymptotically closed)
    intro hphi
    have htotal := maximal_is_total p hmax
    -- By totality, either a ≤ b or b ≤ a
    rcases htotal a b with hab | hba
    · exact hab
    · -- If b ≤ a, then φ(b) ≤ φ(a), combined with φ(a) ≤ φ(b) gives equality
      have hphi_ba : phiFromPreorder p b ≤ phiFromPreorder p a := phi_monotone p hba
      have heq : phiFromPreorder p a = phiFromPreorder p b := le_antisymm hphi hphi_ba
      -- The source argument (survey tex:776): "Let a ̸≤ b. From str_props(iv)
      -- follows ∃n, na ̸≤ nb + 1. By totality na ≥ nb + 1. Apply φ to get
      -- φ(a) ≥ φ(b) + 1/n." Below: by contradiction, extract the witness n,
      -- iterate the gap, and contradict φ(a) = φ(b).
      -- By contradiction: assume ¬p.rel a b
      by_contra hnab
      -- Since p is maximal, p.rel = (asympPreorder p).rel by maximal_eq_asymp
      have hpeq := maximal_eq_asymp p hmax
      -- So ¬p.rel a b implies ¬(asympPreorder p).rel a b = ¬AsympRel p a b
      have hnasym : ¬AsympRel p a b := by
        intro hasym
        rw [hpeq] at hnab
        exact hnab hasym
      -- By contrapositive of asymp_of_bounded_diff (str_props iv):
      -- ¬AsympRel p a b → ∃n ≥ 1, ¬p.rel (n•a) (n•b + 1)
      -- Case split on b = 0
      have hex : ∃ n : ℕ, n ≥ 1 ∧ ¬p.rel (n • a) (n • b + 1) := by
        by_cases hb : b = 0
        · -- b = 0 case
          subst hb
          simp only [smul_zero, zero_add]
          by_cases ha : a = 0
          · -- a = 0: AsympRel p 0 0 holds, contradicting hnasym
            exfalso
            apply hnasym
            subst ha
            -- Construct AsympRel p 0 0 with witness x_n = 1
            refine ⟨fun _ => 1, fun n hn => ?_, ?_⟩
            · simp only [zero_pow (Nat.one_le_iff_ne_zero.mp hn), zero_mul]
              exact p.refl 0
            · simp only [Nat.cast_one, Real.one_rpow]
              have : (fun _ : ℕ => (1:ℝ)) '' {m : ℕ | 1 ≤ m} = {1} := by
                ext x; simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
                constructor
                · rintro ⟨_, _, rfl⟩; rfl
                · intro hx; exact ⟨1, by omega, hx.symm⟩
              rw [this]; exact csInf_singleton 1
          · -- a ≠ 0: If ∀n, p.rel (n•a) 1, derive contradiction via 2 ≤ 1
            by_contra hall
            push_neg at hall
            -- hall : ∀n ≥ 1, p.rel (n•a) 1
            obtain ⟨k, hk⟩ := p.archimedean 1 a ha
            have hk' : p.rel 1 (k • a) := by simp only [nsmul_eq_mul] at hk ⊢; exact hk
            have hk_ge1 : k ≥ 1 := by
              by_contra hk0; push_neg at hk0; interval_cases k
              simp only [zero_smul] at hk'
              -- p.rel 1 0 means 1 ≤ 0 in ℕ via nat_compat
              exact p.not_rel_one_zero hk'
            have hka_1 : p.rel (k • a) 1 := hall k hk_ge1
            have h2k : p.rel ((2 * k) • a) 1 := hall (2 * k) (by omega)
            have h2ka_eq : (2 * k) • a = 2 • (k • a) := mul_smul 2 k a
            rw [h2ka_eq] at h2k
            have h2_2ka : p.rel (2 • (1 : S)) (2 • (k • a)) := p.nsmul_mono 2 hk'
            -- 2 • 1 = (2:ℕ):S in a semiring
            have h21 : (2 : ℕ) • (1 : S) = ((2 : ℕ) : S) := by norm_num [two_nsmul]
            rw [h21] at h2_2ka
            have h2_1 : p.rel ((2:ℕ):S) 1 := p.trans ((2:ℕ):S) (2 • (k • a)) 1 h2_2ka h2k
            -- Convert 1 : S to (1:ℕ):S for nat_compat
            have h1eq : (1 : S) = ((1 : ℕ) : S) := by simp
            rw [h1eq] at h2_1
            have : (2 : ℕ) ≤ 1 := (p.nat_compat 2 1).mpr h2_1; omega
        · -- b ≠ 0: Use contrapositive of asymp_of_bounded_diff
          by_contra hall
          push_neg at hall
          apply hnasym
          have h : ∀ n : ℕ, p.rel (n • a) (n • b + 1) := by
            intro n
            by_cases hn : n ≥ 1
            · exact hall n hn
            · push_neg at hn; interval_cases n
              simp only [zero_smul, zero_add]; exact p.zero_le 1
          exact p.asymp_of_bounded_diff 1 hb h
      obtain ⟨n, hn_ge1, hneg⟩ := hex
      -- By maximal_is_total: p is total
      have htotal := maximal_is_total p hmax
      -- From totality and ¬p.rel (n•a) (n•b + 1): p.rel (n•b + 1) (n•a)
      have hrev : p.rel (n • b + 1) (n • a) := by
        rcases htotal (n • a) (n • b + 1) with h | h
        · exact (hneg h).elim
        · exact h
      -- Apply phi_monotone: φ(n•b + 1) ≤ φ(n•a)
      have hphi_ineq : phiFromPreorder p (n • b + 1) ≤ phiFromPreorder p (n • a) :=
        phi_monotone p hrev
      -- φ(n•b + 1) = φ(n•b) + φ(1) by phi_add, and φ(1) = 1 by phi_nat
      have hphi_add : phiFromPreorder p (n • b + 1) = phiFromPreorder p (n • b) + 1 := by
        have h1 : (1 : S) = ((1 : ℕ) : S) := by simp
        conv_lhs => rw [h1]
        rw [phi_add p htotal (n • b) ((1 : ℕ) : S), phi_nat p 1]
        simp only [Nat.cast_one]
      -- φ(n•a) = φ(n * a) = φ(n) * φ(a) = n * φ(a) by phi_mul and phi_nat
      -- Note: n•a = n * a in a CommSemiring
      have hphi_nsmul_a : phiFromPreorder p (n • a) = n * phiFromPreorder p a := by
        simp only [nsmul_eq_mul]
        rw [phi_mul p htotal n a, phi_nat p n]
      have hphi_nsmul_b : phiFromPreorder p (n • b) = n * phiFromPreorder p b := by
        simp only [nsmul_eq_mul]
        rw [phi_mul p htotal n b, phi_nat p n]
      -- Substitute into inequality: n*φ(b) + 1 ≤ n*φ(a)
      rw [hphi_add, hphi_nsmul_b, hphi_nsmul_a] at hphi_ineq
      -- hphi_ineq : n * phiFromPreorder p b + 1 ≤ n * phiFromPreorder p a
      -- So φ(a) ≥ φ(b) + 1/n
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega : n ≠ 0))
      -- From heq: φ(a) = φ(b), substitute into hphi_ineq
      rw [heq] at hphi_ineq
      -- hphi_ineq : n * phiFromPreorder p b + 1 ≤ n * phiFromPreorder p b
      -- This gives 1 ≤ 0, contradiction
      nlinarith [sq_nonneg (phiFromPreorder p b)]

end AsymptoticSpectrumDuality
