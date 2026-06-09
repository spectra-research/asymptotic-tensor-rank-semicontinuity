/-
Copyright (c) 2024 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.AsymptoticSpectrumDuality.Completeness
import AsymptoticTensorRankSemicontinuity.Prerequisites.AsymptoticSpectrumDuality.HomConstruction

/-!
# Strassen's Spectral Duality Theorem

This file proves Strassen's duality theorem: the asymptotic preorder is characterized
by monotonicity under all spectral points (maximal Strassen preorder homomorphisms).

## Main Results

* `spectral_duality` : a ≲ b ↔ ∀ φ : SpectralPoint, φ(a) ≤ φ(b) (Theorem 2.4)

## Proof Strategy

The proof follows Strassen (1988):

1. **Forward direction (easy)**: If a ≲ b, then for any spectral point φ (which
   corresponds to a maximal preorder p via φ = phiFromPreorder p), we have
   a ≤_p b (by completeness), hence φ(a) ≤ φ(b) (by monotonicity of φ).

2. **Backward direction (completeness)**: If ∀ spectral points φ, φ(a) ≤ φ(b),
   then for all maximal preorders p, we have phiFromPreorder p a ≤ phiFromPreorder p b.
   By phi_reflects_of_maximal, this means a ≤_p b for all maximal p.
   By completeness, a ≲ b.

## References

* Strassen (1988), The asymptotic spectrum of tensors, Theorem 2.4
-/

namespace AsymptoticSpectrumDuality

open StrassenPreorder

variable {S : Type*} [CommSemiring S]

/-! ### Spectral Points -/

/-- A spectral point is a nonnegative real-valued semiring homomorphism that is
    monotone with respect to the base Strassen preorder.

    In our formalization, spectral points correspond bijectively to maximal
    Strassen preorders via the φ construction. -/
structure SpectralPoint (p : StrassenPreorder S) where
  /-- The underlying function -/
  toFun : S → ℝ
  /-- φ is a semiring homomorphism (zero) -/
  map_zero : toFun 0 = 0
  /-- φ is a semiring homomorphism (one) -/
  map_one : toFun 1 = 1
  /-- φ is a semiring homomorphism (add) -/
  map_add : ∀ a b, toFun (a + b) = toFun a + toFun b
  /-- φ is a semiring homomorphism (mul) -/
  map_mul : ∀ a b, toFun (a * b) = toFun a * toFun b
  /-- φ is monotone under p -/
  monotone : ∀ a b, p.rel a b → toFun a ≤ toFun b
  /-- φ takes nonnegative values -/
  nonneg : ∀ a, 0 ≤ toFun a

instance (p : StrassenPreorder S) : CoeFun (SpectralPoint p) (fun _ => S → ℝ) where
  coe := SpectralPoint.toFun

/-! ### From Maximal Preorders to Spectral Points -/

/-- Construct a spectral point from a maximal Strassen preorder.
    Uses the φ function from HomConstruction. -/
noncomputable def spectralPointOfMaximal (p : StrassenPreorder S) (hmax : p.IsMaximal) :
    SpectralPoint p where
  toFun := phiFromPreorder p
  map_zero := phi_zero p
  map_one := phi_one p
  map_add := by
    intro a b
    have htotal := maximal_is_total p hmax
    exact phi_add p htotal a b
  map_mul := by
    intro a b
    have htotal := maximal_is_total p hmax
    exact phi_mul p htotal a b
  monotone := fun a b hab => phi_monotone p hab
  nonneg := by
    intro a
    -- φ(a) = inf { r/s : sa ≤ r }, all ratios are nonnegative
    apply le_csInf (phiSet_nonempty p a)
    intro x ⟨r, s, _, _, hx⟩
    subst hx
    exact div_nonneg (Nat.cast_nonneg r) (Nat.cast_nonneg s)

/-! ### Main Duality Theorem -/

/-- Helper: spectral points preserve natural number powers -/
private theorem spectral_map_pow (φ : SpectralPoint p) (a : S) (n : ℕ) :
    φ (a ^ n) = (φ a) ^ n := by
  induction n with
  | zero => simp only [pow_zero, φ.map_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, φ.map_mul, ih]

/-- Helper: spectral points preserve natural number casts -/
private theorem spectral_map_nat (φ : SpectralPoint p) (n : ℕ) :
    φ (n : S) = (n : ℝ) := by
  induction n with
  | zero => simp only [Nat.cast_zero, φ.map_zero]
  | succ n ih =>
    simp only [Nat.cast_succ, φ.map_add, φ.map_one, ih]

/-- Forward direction: if a ≲_p b then φ(a) ≤ φ(b) for all spectral points φ -/
theorem asymp_implies_spectral (p : StrassenPreorder S) {a b : S}
    (hasym : AsympRel p a b) (φ : SpectralPoint p) : φ a ≤ φ b := by
  -- The key argument: if φ(a) > φ(b), then φ(a)^n grows faster than φ(b)^n * x(n)
  -- which contradicts a^n ≤ b^n * x(n) with x(n)^{1/n} → 1
  -- Convert to Tendsto form using AsympRel_iff_tendsto
  obtain ⟨x, hx_rel, hx_lim⟩ := (AsympRel_iff_tendsto p a b).mp hasym
  -- For each n ≥ 1, p.rel (a^n) (b^n * x(n)), so φ(a^n) ≤ φ(b^n * x(n))
  have hphi_bound : ∀ n, n ≥ 1 → φ a ^ n ≤ φ b ^ n * (x n : ℝ) := by
    intro n hn
    have hrel := hx_rel n hn
    have hmono := φ.monotone _ _ hrel
    rw [spectral_map_pow, φ.map_mul, spectral_map_pow, spectral_map_nat] at hmono
    exact hmono
  -- Now use the limit condition to get φ(a) ≤ φ(b)
  by_contra hgt
  push_neg at hgt
  -- hgt : φ b < φ a
  -- If φ(b) = 0, then φ(a) > 0, so φ(a)^n > 0 but φ(b)^n * x(n) = 0
  -- contradicting hphi_bound for n ≥ 1
  by_cases hb0 : φ b = 0
  · -- φ(b) = 0, so φ(a) > 0
    have ha_pos : 0 < φ a := by
      have := φ.nonneg a
      linarith
    -- For n = 1: φ(a) ≤ 0 * x(1) = 0, contradiction
    have h1 := hphi_bound 1 (Nat.le_refl 1)
    simp only [pow_one, hb0, zero_mul] at h1
    linarith
  · -- φ(b) > 0 (since φ(b) ≥ 0 by nonneg and φ(b) ≠ 0)
    have hb_pos : 0 < φ b := (φ.nonneg b).lt_of_ne' hb0
    -- For large n, (φ(a)/φ(b))^n > x(n), contradicting hphi_bound
    -- Since φ(a)/φ(b) > 1 and x(n)^{1/n} → 1
    have hratio : 1 < φ a / φ b := by
      rw [one_lt_div₀ hb_pos]
      exact hgt
    -- From hphi_bound: (φ(a)/φ(b))^n ≤ x(n)
    -- Since φ(a)/φ(b) > 1 and x(n)^{1/n} → 1, this is impossible for large n
    set r := φ a / φ b with hr_def
    have hr_pos : 0 < r := by positivity
    have heps : 0 < r - 1 := by linarith
    -- Since x(n)^{1/n} → 1 and r > 1, eventually x(n)^{1/n} < r
    have hlim_near : ∀ᶠ n in Filter.atTop, (x n : ℝ) ^ (1 / (n : ℝ)) < r := by
      have := Metric.tendsto_atTop.mp hx_lim (r - 1) heps
      simp only [Real.dist_eq] at this
      obtain ⟨N, hN⟩ := this
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      specialize hN n hn
      have hlt : (x n : ℝ) ^ (1 / (n : ℝ)) - 1 < r - 1 := (abs_lt.mp hN).2
      linarith
    -- Eventually x(n)^{1/n} < r, so x(n) < r^n
    have hxn_lt : ∀ᶠ n in Filter.atTop, (x n : ℝ) < r ^ n := by
      filter_upwards [hlim_near, Filter.eventually_ge_atTop 1] with n hlim hn
      have hn_ne : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn_ne)
      have h1 : (x n : ℝ) ^ (1 / (n : ℝ)) < r := hlim
      have h2 : ((x n : ℝ) ^ (1 / (n : ℝ))) ^ (n : ℝ) < r ^ (n : ℝ) := by
        apply Real.rpow_lt_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) h1
        exact hn_pos
      rw [← Real.rpow_mul (Nat.cast_nonneg _), one_div, inv_mul_cancel₀ (ne_of_gt hn_pos),
          Real.rpow_one, Real.rpow_natCast] at h2
      exact h2
    -- But hphi_bound gives r^n ≤ x(n) for n ≥ 1
    have hphi_ratio : ∀ n, n ≥ 1 → r ^ n ≤ (x n : ℝ) := by
      intro n hn
      have hb := hphi_bound n hn
      have hb_pow_pos : 0 < φ b ^ n := by positivity
      rw [mul_comm] at hb
      calc r ^ n = (φ a / φ b) ^ n := by rfl
        _ = φ a ^ n / φ b ^ n := by rw [div_pow]
        _ ≤ (x n : ℝ) := by rwa [div_le_iff₀ hb_pow_pos]
    -- Contradiction: eventually r^n > x(n) but r^n ≤ x(n)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hxn_lt
    have hcontra := hN (max N 1) (le_max_left _ _)
    have hbound := hphi_ratio (max N 1) (le_max_right _ _)
    linarith

/-- Backward direction: if φ(a) ≤ φ(b) for all maximal extensions' spectral points,
    then a ≲_p b -/
theorem spectral_implies_asymp (p : StrassenPreorder S) {a b : S}
    (hspec : ∀ q : StrassenPreorder S, ∀ _hpq : p ≤ q, ∀ hqmax : q.IsMaximal,
             (spectralPointOfMaximal q hqmax) a ≤
             (spectralPointOfMaximal q hqmax) b) :
    AsympRel p a b := by
  -- By completeness, a ≲ b iff a ≤_q b for all maximal q ⊇ p
  rw [asymp_iff_forall_maximal]
  intro q hpq hqmax
  -- We have spectralPointOfMaximal q a ≤ spectralPointOfMaximal q b
  have hspec_q := hspec q hpq hqmax
  -- spectralPointOfMaximal q = phiFromPreorder q
  -- By phi_reflects_of_maximal, phiFromPreorder q a ≤ phiFromPreorder q b iff q.rel a b
  rw [phi_reflects_of_maximal q hqmax]
  exact hspec_q

/-- Strassen's spectral duality theorem (abstract version):
    a ≲_p b iff φ(a) ≤ φ(b) for all spectral points of maximal extensions of p.

    This is the abstract algebraic statement. For the graph-theoretic version,
    we would instantiate S = GraphSemiring and p = cohomomorphism preorder. -/
theorem spectral_duality_abstract (p : StrassenPreorder S) (a b : S) :
    AsympRel p a b ↔
    ∀ q : StrassenPreorder S, ∀ _hpq : p ≤ q, ∀ hqmax : q.IsMaximal,
      (spectralPointOfMaximal q hqmax) a ≤
      (spectralPointOfMaximal q hqmax) b := by
  constructor
  · -- Forward
    intro hasym q hpq hqmax
    -- a ≲_p b and p ≤ q, so a ≲_q b
    have hasym_q : AsympRel q a b := by
      obtain ⟨x, hx_rel, hx_lim⟩ := hasym
      refine ⟨x, ?_, hx_lim⟩
      intro n hn
      exact hpq _ _ (hx_rel n hn)
    -- By completeness, a ≤_q b
    have hqab : q.rel a b := asymp_implies_maximal q hqmax hasym_q
    -- By phi_monotone, spectralPointOfMaximal q a ≤ spectralPointOfMaximal q b
    exact phi_monotone q hqab
  · -- Backward
    exact spectral_implies_asymp p

end AsymptoticSpectrumDuality
