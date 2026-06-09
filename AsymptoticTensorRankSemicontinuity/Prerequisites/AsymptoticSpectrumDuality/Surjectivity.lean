/-
Copyright (c) 2024 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.AsymptoticSpectrumDuality.SpectrumDuality
import Mathlib.Order.BourbakiWitt
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Surjectivity of Restriction Maps on Asymptotic Spectra (Theorem A.2)

This file proves that restriction maps between asymptotic spectra are surjective.

Given two commutative semirings S₁ and S₂ with Strassen preorders p₁ and p₂,
and a ring homomorphism i : S₁ →+* S₂ that is an order embedding (preserving
the preorder in both directions), every spectral point φ on S₁ extends to a
spectral point ψ on S₂ such that ψ(i(a)) = φ(a) for all a ∈ S₁.

## Proof approach (survey.tex topological proof, lines 2988–3017)

The proof uses the topological structure of the asymptotic spectrum:
1. Define pullback map f* : X₂ → X₁ by f*(ψ) = ψ ∘ i
2. Show f*(X₂) is closed in X₁ (continuous image of compact in Hausdorff)
3. Show same-halfspace condition: ∀φ∈X₁, φ(a)≤φ(b) ↔ ∀ψ∈X₂, ψ(ia)≤ψ(ib)
4. Use density (Stone–Weierstrass) + Urysohn to show f*(X₂) = X₁

## Main Results

* `restriction_surjective` - Theorem A.2

## References

* de Boer, Buys, Zuiddam, *Distance in the asymptotic spectrum of graphs*, Theorem A.2
-/

-- Suppress stylistic warnings
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.style.emptyLine false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.style.cdot false
set_option linter.style.show false
set_option linter.unreachableTactic false

namespace AsymptoticSpectrumDuality

open StrassenPreorder

variable {S₁ : Type*} [CommSemiring S₁] {S₂ : Type*} [CommSemiring S₂]

/-- An order embedding of Strassen preorders preserves the asymptotic relation. -/
theorem order_embedding_preserves_asympRel
    (p₁ : StrassenPreorder S₁) (p₂ : StrassenPreorder S₂)
    (i : S₁ →+* S₂)
    (hord : ∀ a b : S₁, p₁.rel a b ↔ p₂.rel (i a) (i b))
    (a b : S₁) :
    AsympRel p₁ a b ↔ AsympRel p₂ (i a) (i b) := by
  constructor
  · -- Forward: AsympRel p₁ a b → AsympRel p₂ (i a) (i b)
    intro ⟨x, hx_rel, hx_lim⟩
    refine ⟨x, ?_, hx_lim⟩
    intro n hn
    have h := (hord _ _).mp (hx_rel n hn)
    rw [map_pow, map_mul, map_pow, map_natCast] at h
    exact h
  · -- Backward: AsympRel p₂ (i a) (i b) → AsympRel p₁ a b
    intro ⟨x, hx_rel, hx_lim⟩
    refine ⟨x, ?_, hx_lim⟩
    intro n hn
    apply (hord _ _).mpr
    show p₂.rel (i (a ^ n)) (i (b ^ n * (x n)))
    rw [map_pow, map_mul, map_pow, map_natCast]
    exact hx_rel n hn

/-- The same-halfspace condition: an inequality holds for all spectral points of p₂
    on the image of i iff it holds for all spectral points of p₁.
    This combines the order embedding with spectral duality. -/
theorem same_halfspace
    (p₁ : StrassenPreorder S₁) (p₂ : StrassenPreorder S₂)
    (i : S₁ →+* S₂)
    (hord : ∀ a b : S₁, p₁.rel a b ↔ p₂.rel (i a) (i b))
    (a b : S₁) :
    (∀ ψ : AsymptoticSpectrum p₂, AsymptoticSpectrum.eval p₂ (i a) ψ ≤
                                    AsymptoticSpectrum.eval p₂ (i b) ψ) ↔
    (∀ φ : AsymptoticSpectrum p₁, AsymptoticSpectrum.eval p₁ a φ ≤
                                    AsymptoticSpectrum.eval p₁ b φ) := by
  rw [← StrassenPreorder.asympRel_iff_forall_spectrum p₂,
      ← StrassenPreorder.asympRel_iff_forall_spectrum p₁]
  exact (order_embedding_preserves_asympRel p₁ p₂ i hord a b).symm

/-- Pullback of a spectral point through the ring homomorphism. -/
def pullbackSpectralPoint
    (p₁ : StrassenPreorder S₁) (p₂ : StrassenPreorder S₂)
    (i : S₁ →+* S₂)
    (hord : ∀ a b : S₁, p₁.rel a b ↔ p₂.rel (i a) (i b))
    (ψ : SpectralPoint p₂) : SpectralPoint p₁ where
  toFun := ψ.toFun ∘ i
  map_zero := by simp [Function.comp, i.map_zero, ψ.map_zero]
  map_one := by simp [Function.comp, i.map_one, ψ.map_one]
  map_add := by intro a b; simp [Function.comp, i.map_add, ψ.map_add]
  map_mul := by intro a b; simp [Function.comp, i.map_mul, ψ.map_mul]
  monotone := by
    intro a b hab
    exact ψ.monotone _ _ ((hord a b).mp hab)
  nonneg := by intro a; exact ψ.nonneg (i a)

/-- The hypotheses of the topological proof are contradictory: if q ∈ A is negative
    at φ₀ and positive on the image of the pullback map, then the Finsupp decomposition
    of q (using adjoin = span, since range evalCM is a submonoid) combined with rational
    approximation and same_halfspace yields a contradiction.

    Specifically: decompose q = Σ c(a) · eval(a) for finitely many a ∈ S₁ with
    real coefficients c(a). Approximate c(a) ≈ z(a)/N for integers z(a), construct
    cp = Σ max(z(a),0) · a and cm = Σ max(-z(a),0) · a in S₁. For small enough
    approximation error:
    - q(fψ) > 0 implies ψ(icp) > ψ(icm) for all ψ, so same_halfspace gives φ₀(cm) ≤ φ₀(cp)
    - q(φ₀) < 0 implies φ₀(cp) < φ₀(cm), contradiction. -/
private theorem spectral_algebraic_contradiction
    (p₁ : StrassenPreorder S₁)
    (p₂ : StrassenPreorder S₂)
    (i : S₁ →+* S₂)
    (hord : ∀ a b : S₁, p₁.rel a b ↔ p₂.rel (i a) (i b))
    (φ₀ : SpectralPoint p₁)
    (f : AsymptoticSpectrum p₂ → AsymptoticSpectrum p₁)
    (hf : ∀ ψ a, (f ψ).toFun a = ψ.toFun (i a))
    (hf_cont : Continuous f)
    (q : C(AsymptoticSpectrum p₁, ℝ))
    [CompactSpace (AsymptoticSpectrum p₁)]
    [CompactSpace (AsymptoticSpectrum p₂)]
    [T2Space (AsymptoticSpectrum p₁)]
    (hq_mem : q ∈ Algebra.adjoin ℝ (Set.range (fun a : S₁ =>
      (⟨AsymptoticSpectrum.eval p₁ a, AsymptoticSpectrum.continuous_eval p₁ a⟩ :
        C(AsymptoticSpectrum p₁, ℝ)))))
    (hq_neg : q φ₀ < 0)
    (hq_pos : ∀ ψ : AsymptoticSpectrum p₂, 0 < q (f ψ)) :
    False := by
  -- Notation for evaluation continuous maps
  set evalCM : S₁ → C(AsymptoticSpectrum p₁, ℝ) :=
    fun a => ⟨AsymptoticSpectrum.eval p₁ a, AsymptoticSpectrum.continuous_eval p₁ a⟩
    with evalCM_def
  -- Step 1: adjoin ℝ (range evalCM) = span ℝ (range evalCM)
  -- Because range evalCM is closed under * and contains 1 (a submonoid).
  have heval_mul : ∀ a b : S₁, evalCM a * evalCM b = evalCM (a * b) :=
    fun a b => ContinuousMap.ext fun φ => (φ.map_mul a b).symm
  have heval_one : evalCM 1 = 1 :=
    ContinuousMap.ext fun φ => φ.map_one
  -- range evalCM is a submonoid (closed under *, contains 1)
  let SM : Submonoid C(AsymptoticSpectrum p₁, ℝ) :=
    { carrier := Set.range evalCM
      one_mem' := ⟨1, heval_one⟩
      mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * b, (heval_mul a b).symm⟩ }
  -- Step 2: q is in the span of range evalCM
  -- adjoin = span(closure(S)), and closure(S) = S since S is already a submonoid
  have hclosure_eq : (Submonoid.closure (Set.range evalCM) :
      Set C(AsymptoticSpectrum p₁, ℝ)) = Set.range evalCM := by
    have h := Submonoid.closure_eq SM
    rw [show (Submonoid.closure (Set.range evalCM) :
        Set C(AsymptoticSpectrum p₁, ℝ)) = SM.carrier from by rw [← h]; rfl]
  have hq_span : q ∈ Submodule.span ℝ (Set.range evalCM) := by
    have h1 : q ∈ Subalgebra.toSubmodule (Algebra.adjoin ℝ (Set.range evalCM)) := hq_mem
    rw [Algebra.adjoin_eq_span, hclosure_eq] at h1; exact h1
  -- Step 3: Finsupp decomposition of q
  obtain ⟨c, hc_eq⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hq_span
  -- hc_eq : c.sum (fun a r => r • evalCM a) = q
  -- i.e., ∀ φ, q(φ) = Σ_{a ∈ c.support} c(a) * eval(a)(φ)
  -- Step 3: Uniform approximation by (1/N)(eval(cp) - eval(cm))
  -- For any ε > 0, choose N large and round c(a) to z(a)/N.
  -- cp = Σ max(z(a),0) • a, cm = Σ max(-z(a),0) • a in S₁.
  -- Error bounded by B/(2N) where B depends on support and eval bounds.
  -- Then same_halfspace + approximation gives contradiction.
  have hdecomp : ∀ ε > 0, ∃ cp cm : S₁, ∃ N : ℕ, 0 < N ∧
      ∀ φ : AsymptoticSpectrum p₁,
        |q φ - (1 / (N : ℝ)) * (AsymptoticSpectrum.eval p₁ cp φ -
          AsymptoticSpectrum.eval p₁ cm φ)| < ε := by
    intro ε hε
    -- Uniform bound on evaluation norms
    set B := 1 + c.support.sum (fun a => ‖evalCM a‖) with hB_def
    have hB_pos : 0 < B := by
      have : 0 ≤ c.support.sum (fun a => ‖evalCM a‖) :=
        Finset.sum_nonneg (fun a _ => norm_nonneg (evalCM a))
      linarith
    -- Choose N large enough that B / N < ε
    obtain ⟨N, hN⟩ := exists_nat_gt (B / ε)
    have hN_pos : 0 < N := by
      by_contra h
      push_neg at h
      interval_cases N
      simp at hN
      linarith [div_pos hB_pos hε]
    have hN_cast_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN_pos
    -- Round coefficients: z(a) = ⌊N * c(a)⌋
    set z : S₁ → ℤ := fun a => ⌊(N : ℝ) * c a⌋ with hz_def
    -- Define cp and cm in S₁
    refine ⟨c.support.sum (fun a => (z a).toNat • a),
            c.support.sum (fun a => (-z a).toNat • a),
            N, hN_pos, ?_⟩
    intro φ
    -- Build an AddMonoidHom from φ for sum/nsmul reasoning
    let φ_hom : S₁ →+ ℝ := ⟨⟨φ.toFun, φ.map_zero⟩, φ.map_add⟩
    -- Evaluate q at φ using hc_eq
    have hq_φ : q φ = c.support.sum (fun a => c a * φ.toFun a) := by
      have := congr_fun (congr_arg DFunLike.coe hc_eq.symm) φ
      simp only [Finsupp.sum, ContinuousMap.coe_sum, ContinuousMap.coe_smul,
                 Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      exact this
    -- Helper: φ_hom(n • a) = n * φ.toFun a
    have hφ_nsmul : ∀ (n : ℕ) (a : S₁), φ_hom (n • a) = (n : ℝ) * φ.toFun a := by
      intro n a
      change φ.toFun (n • a) = _
      induction n with
      | zero => simp [φ.map_zero]
      | succ n ih =>
        rw [succ_nsmul, φ.map_add, ih]
        push_cast; ring
    -- φ(cp) = Σ (z a).toNat * φ(a)
    have hφ_cp : φ.toFun (c.support.sum (fun a => (z a).toNat • a)) =
        c.support.sum (fun a => ((z a).toNat : ℝ) * φ.toFun a) := by
      show φ_hom (c.support.sum (fun a => (z a).toNat • a)) = _
      rw [map_sum]; congr 1; ext a; exact hφ_nsmul _ _
    -- φ(cm) = Σ (-z a).toNat * φ(a)
    have hφ_cm : φ.toFun (c.support.sum (fun a => (-z a).toNat • a)) =
        c.support.sum (fun a => ((-z a).toNat : ℝ) * φ.toFun a) := by
      show φ_hom (c.support.sum (fun a => (-z a).toNat • a)) = _
      rw [map_sum]; congr 1; ext a; exact hφ_nsmul _ _
    -- cp(φ) - cm(φ) = Σ z(a) * φ(a)
    have hφ_diff : φ.toFun (c.support.sum (fun a => (z a).toNat • a)) -
        φ.toFun (c.support.sum (fun a => (-z a).toNat • a)) =
        c.support.sum (fun a => (z a : ℝ) * φ.toFun a) := by
      rw [hφ_cp, hφ_cm, ← Finset.sum_sub_distrib]
      congr 1; ext a
      have hkey : ((z a).toNat : ℝ) - ((-z a).toNat : ℝ) = (z a : ℝ) := by
        have : ((z a).toNat : ℤ) - ((-z a).toNat : ℤ) = z a := by omega
        exact_mod_cast this
      linear_combination hkey * φ.toFun a
    -- Now bound the error
    -- error = |q(φ) - (1/N)(cp(φ) - cm(φ))| = |Σ (c(a) - z(a)/N) * φ(a)|
    rw [hq_φ]
    simp only [AsymptoticSpectrum.eval]
    rw [hφ_diff]
    rw [show (1 / (N : ℝ)) * c.support.sum (fun a => (z a : ℝ) * φ.toFun a) =
        c.support.sum (fun a => (z a : ℝ) / N * φ.toFun a) by
      rw [Finset.mul_sum]; congr 1; ext a; ring]
    rw [show c.support.sum (fun a => c a * φ.toFun a) -
        c.support.sum (fun a => (z a : ℝ) / N * φ.toFun a) =
        c.support.sum (fun a => (c a - (z a : ℝ) / N) * φ.toFun a) by
      rw [← Finset.sum_sub_distrib]; congr 1; ext a; ring]
    -- Bound: |Σ (c(a) - z(a)/N) * φ(a)| ≤ Σ |c(a) - z(a)/N| * |φ(a)|
    calc |c.support.sum (fun a => (c a - (z a : ℝ) / N) * φ.toFun a)|
        ≤ c.support.sum (fun a => |(c a - (z a : ℝ) / N) * φ.toFun a|) :=
          Finset.abs_sum_le_sum_abs _ _
      _ = c.support.sum (fun a => |c a - (z a : ℝ) / N| * |φ.toFun a|) := by
          congr 1; ext a; exact abs_mul _ _
      _ ≤ c.support.sum (fun a => (1 / N) * ‖evalCM a‖) := by
          apply Finset.sum_le_sum; intro a _
          apply mul_le_mul
          · -- |c(a) - z(a)/N| < 1/N
            rw [hz_def]
            rw [show c a - (⌊(N : ℝ) * c a⌋ : ℝ) / N = ((N : ℝ) * c a - ⌊(N : ℝ) * c a⌋) / N by
              field_simp]
            rw [abs_div, abs_of_pos hN_cast_pos]
            apply div_le_div_of_nonneg_right _ hN_cast_pos.le
            rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le _))]
            linarith [Int.lt_floor_add_one ((N : ℝ) * c a)]
          · -- |φ(a)| ≤ ‖evalCM a‖
            rw [abs_of_nonneg (φ.nonneg a)]
            have : ‖(evalCM a) φ‖ ≤ ‖evalCM a‖ := ContinuousMap.norm_coe_le_norm (evalCM a) φ
            rw [Real.norm_eq_abs] at this
            calc φ.toFun a ≤ |φ.toFun a| := le_abs_self _
              _ = |(evalCM a) φ| := rfl
              _ ≤ ‖evalCM a‖ := this
          · exact abs_nonneg _
          · exact div_nonneg one_pos.le hN_cast_pos.le
      _ = (1 / N) * c.support.sum (fun a => ‖evalCM a‖) := by
          rw [← Finset.mul_sum]
      _ ≤ B / N := by
          rw [div_mul_eq_mul_div, one_mul]
          apply div_le_div_of_nonneg_right _ hN_cast_pos.le
          linarith
      _ < ε := by
          rw [div_lt_iff₀ hN_cast_pos, mul_comm]
          calc B = B / ε * ε := by field_simp
            _ < N * ε := mul_lt_mul_of_pos_right hN hε
  -- Step 4: Choose ε small enough for contradiction
  -- Need ε < min(δ, -q(φ₀)) where δ = inf_ψ q(f ψ) > 0 (positive on compact image)
  suffices hkey : 0 ≤ q φ₀ from absurd hkey (not_le.mpr hq_neg)
  -- Get uniform positive lower bound δ on q ∘ f (continuous on compact X₂)
  by_cases hne : Nonempty (AsymptoticSpectrum p₂)
  · -- Nonempty case: use compactness to get minimum
    have hqf_cont : Continuous (fun ψ => q (f ψ)) := q.continuous.comp hf_cont
    have hqf_pos : ∀ ψ, (0 : ℝ) < q (f ψ) := hq_pos
    -- On compact nonempty space, continuous function attains minimum
    haveI := hne
    obtain ⟨ψ_min, _, hψ_min⟩ := IsCompact.exists_isMinOn isCompact_univ
      Set.univ_nonempty hqf_cont.continuousOn
    set δ := q (f ψ_min) with hδ_def
    have hδ_pos : 0 < δ := hqf_pos ψ_min
    have hδ_le : ∀ ψ, δ ≤ q (f ψ) := by
      intro ψ; exact hψ_min (Set.mem_univ ψ)
    -- Choose ε = min(δ, -q(φ₀)) / 2
    set ε := min δ (-q φ₀) / 2 with hε_def
    have hε_pos : 0 < ε := by
      apply div_pos (lt_min hδ_pos (by linarith)) two_pos
    obtain ⟨cp, cm, N, hN, happrox⟩ := hdecomp ε hε_pos
    -- At each f ψ: approximation is positive, so eval(cm)(ψ) ≤ eval(cp)(ψ)
    have hall : ∀ ψ : AsymptoticSpectrum p₂,
        AsymptoticSpectrum.eval p₂ (i cm) ψ ≤ AsymptoticSpectrum.eval p₂ (i cp) ψ := by
      intro ψ
      have happrox_ψ := happrox (f ψ)
      rw [abs_lt] at happrox_ψ
      -- (1/N)(eval cp (f ψ) - eval cm (f ψ)) > q(f ψ) - ε ≥ δ - ε ≥ δ/2 > 0
      -- eval cp (f ψ) = (f ψ)(cp) = ψ(i cp), similarly for cm
      have hfψ_cp : AsymptoticSpectrum.eval p₁ cp (f ψ) = AsymptoticSpectrum.eval p₂ (i cp) ψ :=
        hf ψ cp
      have hfψ_cm : AsymptoticSpectrum.eval p₁ cm (f ψ) = AsymptoticSpectrum.eval p₂ (i cm) ψ :=
        hf ψ cm
      rw [hfψ_cp, hfψ_cm] at happrox_ψ
      have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
      have h1N_pos : (0 : ℝ) < 1 / N := div_pos one_pos hN_pos
      -- From happrox_ψ.1: q(f ψ) - ε < (1/N)(ψ(icp) - ψ(icm))
      -- q(f ψ) ≥ δ and ε ≤ δ/2, so q(f ψ) - ε ≥ δ - δ/2 = δ/2 > 0
      have hge : 0 < 1 / (N : ℝ) * (AsymptoticSpectrum.eval p₂ (i cp) ψ -
          AsymptoticSpectrum.eval p₂ (i cm) ψ) := by
        have : δ - ε ≤ q (f ψ) - ε := by linarith [hδ_le ψ]
        have : 0 < δ - ε := by
          simp only [hε_def]; linarith [min_le_left δ (-q φ₀)]
        linarith [happrox_ψ.1]
      -- (1/N) * (eval cp - eval cm) > 0 and 1/N > 0, so eval cp > eval cm
      rcases mul_pos_iff.mp hge with ⟨_, h⟩ | ⟨h, _⟩ <;> linarith
    -- By same_halfspace: ∀ φ, φ(cm) ≤ φ(cp)
    have hsame := (same_halfspace p₁ p₂ i hord cm cp).mp hall
    -- At φ₀: from approximation, (1/N)(φ₀(cp) - φ₀(cm)) is close to q(φ₀)
    -- and φ₀(cp) - φ₀(cm) ≥ 0, so q(φ₀) > -ε > q(φ₀) (contradiction)
    have happrox_φ₀ := happrox φ₀
    rw [abs_lt] at happrox_φ₀
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hsame_φ₀ := hsame φ₀
    -- φ₀(cm) ≤ φ₀(cp) means eval cm φ₀ ≤ eval cp φ₀
    -- so eval cp φ₀ - eval cm φ₀ ≥ 0
    -- so (1/N)(eval cp φ₀ - eval cm φ₀) ≥ 0
    have h_approx_nonneg : 0 ≤ 1 / (N : ℝ) * (AsymptoticSpectrum.eval p₁ cp φ₀ -
        AsymptoticSpectrum.eval p₁ cm φ₀) := by
      apply mul_nonneg (by positivity)
      linarith
    -- q(φ₀) > (1/N)(...) - ε ≥ 0 - ε = -ε > -(-q(φ₀)) = q(φ₀)... wait
    -- From happrox_φ₀.1: q(φ₀) - ε < (1/N)(...)
    -- From h_approx_nonneg: 0 ≤ (1/N)(...)
    -- Want: 0 ≤ q(φ₀). From happrox_φ₀.2: (1/N)(...) < q(φ₀) + ε
    -- And ε ≤ -q(φ₀)/2. So q(φ₀) + ε ≤ q(φ₀) + (-q(φ₀))/2 = q(φ₀)/2
    -- So (1/N)(...) < q(φ₀)/2. But also 0 ≤ (1/N)(...). So 0 < q(φ₀)/2... no
    -- Actually: q(φ₀) > (1/N)(...) - ε ≥ -ε. So q(φ₀) > -ε ≥ -(-q(φ₀))/2 = q(φ₀)/2.
    -- That gives q(φ₀) > q(φ₀)/2, i.e., q(φ₀)/2 > 0... no, q(φ₀) < 0.
    -- Let me redo: from happrox_φ₀: |q(φ₀) - X| < ε where X = (1/N)(eval cp - eval cm)(φ₀)
    -- So X > q(φ₀) - ε and X < q(φ₀) + ε
    -- Also X ≥ 0 (from same_halfspace)
    -- So 0 ≤ X < q(φ₀) + ε ≤ q(φ₀) + (-q(φ₀))/2 = q(φ₀)/2 < 0 (since q(φ₀) < 0)
    -- Contradiction! 0 ≤ X < 0.
    -- Actually need ε ≤ -q(φ₀)/2, i.e., q(φ₀) + ε ≤ q(φ₀)/2 < 0.
    linarith [min_le_right δ (-q φ₀)]
  · -- Empty X₂ case: same_halfspace gives everything, derive 1 ≤ 0
    rw [not_nonempty_iff] at hne
    have : ∀ a b : S₁, ∀ φ : AsymptoticSpectrum p₁,
        AsymptoticSpectrum.eval p₁ a φ ≤ AsymptoticSpectrum.eval p₁ b φ := by
      intro a b
      exact (same_halfspace p₁ p₂ i hord a b).mp (fun ψ => (hne.false ψ).elim)
    -- In particular φ₀(1) ≤ φ₀(0), i.e., 1 ≤ 0
    have h01 := this 1 0 φ₀
    simp only [AsymptoticSpectrum.eval, φ₀.map_one, φ₀.map_zero] at h01
    linarith

theorem topological_contradiction
    (p₁ : StrassenPreorder S₁) (p₂ : StrassenPreorder S₂)
    (i : S₁ →+* S₂)
    (hord : ∀ a b : S₁, p₁.rel a b ↔ p₂.rel (i a) (i b))
    (φ₀ : SpectralPoint p₁)
    (hφ₀ : ∀ ψ : SpectralPoint p₂, ∃ a : S₁, ψ (i a) ≠ φ₀ a) :
    False := by
  -- Topological instances for the compact spectra.
  haveI : CompactSpace (AsymptoticSpectrum p₁) :=
    isCompact_univ_iff.mp (AsymptoticSpectrum.isCompact p₁)
  haveI : T2Space (AsymptoticSpectrum p₁) := AsymptoticSpectrum.t2Space p₁
  haveI : NormalSpace (AsymptoticSpectrum p₁) := inferInstance
  haveI : CompactSpace (AsymptoticSpectrum p₂) :=
    isCompact_univ_iff.mp (AsymptoticSpectrum.isCompact p₂)
  haveI : T2Space (AsymptoticSpectrum p₂) := AsymptoticSpectrum.t2Space p₂
  -- Pullback map and closed image.
  let f : AsymptoticSpectrum p₂ → AsymptoticSpectrum p₁ :=
    fun ψ => pullbackSpectralPoint p₁ p₂ i hord ψ
  have hf_cont : Continuous f := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro a
    exact AsymptoticSpectrum.continuous_eval p₂ (i a)
  have himg_compact : IsCompact (Set.range f) := isCompact_range hf_cont
  have himg_closed : IsClosed (Set.range f) := himg_compact.isClosed
  -- `φ₀` is not in the pullback image.
  have hφ₀_notin : φ₀ ∉ Set.range f := by
    intro ⟨ψ, hψ⟩
    obtain ⟨a, ha⟩ := hφ₀ ψ
    exact ha (show (f ψ).toFun a = φ₀.toFun a by rw [hψ])
  -- Urysohn separation.
  have hφ₀_closed : IsClosed ({φ₀} : Set (AsymptoticSpectrum p₁)) := isClosed_singleton
  have hdisjoint : Disjoint ({φ₀} : Set (AsymptoticSpectrum p₁)) (Set.range f) := by
    rw [Set.disjoint_left]
    intro x hx hxf
    rw [Set.mem_singleton_iff] at hx; rw [hx] at hxf; exact hφ₀_notin hxf
  obtain ⟨g, hg0, hg1, _⟩ :=
    exists_continuous_zero_one_of_isClosed hφ₀_closed himg_closed hdisjoint
  -- Stone-Weierstrass approximation algebra.
  let evalCM : S₁ → C(AsymptoticSpectrum p₁, ℝ) :=
    fun a => ⟨AsymptoticSpectrum.eval p₁ a, AsymptoticSpectrum.continuous_eval p₁ a⟩
  let A : Subalgebra ℝ C(AsymptoticSpectrum p₁, ℝ) := Algebra.adjoin ℝ (Set.range evalCM)
  have hA_sep : A.SeparatesPoints := by
    intro φ₁ φ₂ hne
    have hne' : φ₁.toFun ≠ φ₂.toFun := by
      intro heq; apply hne; cases φ₁; cases φ₂; simp only at heq; congr
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hne'
    exact ⟨evalCM a, ⟨evalCM a, Algebra.subset_adjoin (Set.mem_range_self a), rfl⟩, ha⟩
  -- Approximate `2g - 1` by an element of `A`.
  let h : C(AsymptoticSpectrum p₁, ℝ) :=
    (2 : ℝ) • g + ((-1 : ℝ) • (1 : C(AsymptoticSpectrum p₁, ℝ)))
  have hh_φ₀ : h φ₀ = -1 := by
    simp only [h, ContinuousMap.coe_add, ContinuousMap.coe_smul, Pi.add_apply, Pi.smul_apply,
               ContinuousMap.one_apply, smul_eq_mul]
    simp [hg0 (Set.mem_singleton φ₀)]
  have hh_img : ∀ ψ : AsymptoticSpectrum p₂, h (f ψ) = 1 := by
    intro ψ
    simp only [h, ContinuousMap.coe_add, ContinuousMap.coe_smul, Pi.add_apply, Pi.smul_apply,
               ContinuousMap.one_apply, smul_eq_mul]
    rw [hg1 ⟨ψ, rfl⟩]; norm_num
  obtain ⟨⟨p_approx, hp_mem⟩, hp_close⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
      A hA_sep h (1/2) (by norm_num)
  have hp_at_φ₀ : p_approx φ₀ < 0 := by
    have hpw : |p_approx φ₀ - h φ₀| < 1/2 :=
      (ContinuousMap.norm_coe_le_norm (p_approx - h) φ₀).trans_lt hp_close
    rw [hh_φ₀] at hpw; rw [abs_lt] at hpw; linarith [hpw.1]
  have hp_at_img : ∀ ψ : AsymptoticSpectrum p₂, 0 < p_approx (f ψ) := by
    intro ψ
    have hpw : |p_approx (f ψ) - h (f ψ)| < 1/2 :=
      (ContinuousMap.norm_coe_le_norm (p_approx - h) (f ψ)).trans_lt hp_close
    rw [hh_img ψ] at hpw; rw [abs_lt] at hpw; linarith [hpw.2]
  -- Algebraic contradiction.
  exact spectral_algebraic_contradiction p₁ p₂ i hord φ₀ f
    (fun ψ a => rfl) hf_cont p_approx hp_mem hp_at_φ₀ hp_at_img

/-- Theorem A.2: The restriction map on spectral points is surjective.

    Given an order-embedding ring homomorphism i : S₁ →+* S₂ between
    Strassen preorders, every spectral point on S₁ extends to one on S₂.

    Proof: by contradiction. If no extension exists, the pullback image
    f*(X₂) ⊊ X₁ is a proper closed subset. Urysohn's lemma + Stone–Weierstrass
    give an element of the evaluation subalgebra that's negative at φ and positive
    on f*(X₂). The Finsupp decomposition + rational approximation + same_halfspace
    then yield a contradiction. -/
theorem restriction_surjective
    {S₁ : Type*} [CommSemiring S₁] {S₂ : Type*} [CommSemiring S₂]
    (p₁ : StrassenPreorder S₁) (p₂ : StrassenPreorder S₂)
    (i : S₁ →+* S₂)
    (hord : ∀ a b : S₁, p₁.rel a b ↔ p₂.rel (i a) (i b))
    (φ : SpectralPoint p₁) :
    ∃ ψ : SpectralPoint p₂, ∀ a : S₁, ψ (i a) = φ a := by
  by_contra hno
  push_neg at hno
  exact topological_contradiction p₁ p₂ i hord φ hno

end AsymptoticSpectrumDuality
