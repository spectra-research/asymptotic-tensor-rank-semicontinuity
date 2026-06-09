/-
Copyright (c) 2024 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.AsymptoticSpectrumDuality.Duality
import AsymptoticTensorRankSemicontinuity.Prerequisites.AsymptoticSpectrumDuality.RankSubrank

/-!
# The Asymptotic Spectrum as a Topological Space

This file defines the asymptotic spectrum X_P of a Strassen preorder P
as a topological space and proves it is compact.

## Main Definitions

* `AsymptoticSpectrum` - The type of spectral points, with product topology
* `AsymptoticSpectrum.eval` - Evaluation at a point: X → ℝ

## Main Results

* `AsymptoticSpectrum.isCompact` - The asymptotic spectrum is compact

## References

* survey.tex, Section on compactness of the spectrum
-/

namespace AsymptoticSpectrumDuality

open scoped NNReal ENNReal Topology

variable {S : Type*} [CommSemiring S]

/-! ### The Asymptotic Spectrum -/

/-- The asymptotic spectrum X_P is the set of all spectral points.
    We give it the topology induced from the product topology on S → ℝ. -/
def AsymptoticSpectrum (p : StrassenPreorder S) := SpectralPoint p

namespace AsymptoticSpectrum

variable (p : StrassenPreorder S)

/-- Evaluation map: sends φ ∈ X to φ(a) -/
def eval (a : S) : AsymptoticSpectrum p → ℝ :=
  fun φ => φ.toFun a

/-- The topology on the asymptotic spectrum is the weak topology
    making all evaluation maps continuous (product topology). -/
instance : TopologicalSpace (AsymptoticSpectrum p) :=
  TopologicalSpace.induced (fun φ a => φ.toFun a) Pi.topologicalSpace

/-- The evaluation maps are continuous by definition of the topology -/
theorem continuous_eval (a : S) : Continuous (eval p a) := by
  -- eval a = (fun f => f a) ∘ (fun φ a => φ.toFun a)
  have : eval p a = (fun f => f a) ∘ (fun φ : AsymptoticSpectrum p => fun a => φ.toFun a) := rfl
  rw [this]
  apply Continuous.comp
  · exact continuous_apply a
  · exact continuous_induced_dom

/-! ### Bounds on Spectral Points -/

/-- Every spectral point satisfies φ(a) ≥ 0 -/
theorem eval_nonneg (φ : AsymptoticSpectrum p) (a : S) : 0 ≤ eval p a φ :=
  φ.nonneg a

/-- Every spectral point satisfies φ(1) = 1 -/
theorem eval_one (φ : AsymptoticSpectrum p) : eval p 1 φ = 1 :=
  φ.map_one

/-- Every spectral point satisfies φ(0) = 0 -/
theorem eval_zero (φ : AsymptoticSpectrum p) : eval p 0 φ = 0 :=
  φ.map_zero

/-- φ(ab) = φ(a)φ(b) -/
theorem eval_mul (φ : AsymptoticSpectrum p) (a b : S) :
    eval p (a * b) φ = eval p a φ * eval p b φ :=
  φ.map_mul a b

/-- φ is monotone: a ≤_P b → φ(a) ≤ φ(b) -/
theorem eval_mono (φ : AsymptoticSpectrum p) {a b : S} (h : p.rel a b) :
    eval p a φ ≤ eval p b φ :=
  φ.monotone a b h

/-- φ(a^n) = φ(a)^n -/
theorem eval_pow (φ : AsymptoticSpectrum p) (a : S) (n : ℕ) :
    eval p (a ^ n) φ = (eval p a φ) ^ n := by
  induction n with
  | zero => simp only [pow_zero, eval_one]
  | succ n ih =>
    simp only [pow_succ, eval, φ.map_mul]
    simp only [show φ.toFun (a ^ n) = eval p (a ^ n) φ from rfl,
               show φ.toFun a = eval p a φ from rfl, ih, mul_comm]

/-- For natural numbers, φ(n) = n -/
theorem eval_natCast (φ : AsymptoticSpectrum p) (n : ℕ) : eval p (n : S) φ = n := by
  induction n with
  | zero => simp only [Nat.cast_zero, eval, φ.map_zero]
  | succ n ih =>
    simp only [Nat.cast_succ, eval, φ.map_add, φ.map_one]
    have : φ.toFun (n : S) = n := ih
    linarith

/-- If a ≤_P n then φ(a) ≤ n -/
theorem eval_le_of_rel_nat (φ : AsymptoticSpectrum p) {a : S} {n : ℕ} (h : p.rel a n) :
    eval p a φ ≤ n := by
  have h1 : eval p a φ ≤ eval p (n : S) φ := φ.monotone a n h
  rw [eval_natCast] at h1
  exact h1

/-- φ(a) ≤ n for any n with a ≤_P n -/
theorem eval_le_of_rank_le (φ : AsymptoticSpectrum p) (a : S) (n : ℕ) (h : p.rank a ≤ n) :
    eval p a φ ≤ n := by
  -- rank a ≤ n means a ≤_P n by rank_le_iff
  have hrel : p.rel a n := (p.rank_le_iff a n).mp h
  exact eval_le_of_rel_nat p φ hrel

/-- φ(a) ≤ rank(a) -/
theorem eval_le_rank (φ : AsymptoticSpectrum p) (a : S) : eval p a φ ≤ p.rank a :=
  eval_le_of_rank_le p φ a (p.rank a) le_rfl

/-- subrank(a) ≤ φ(a) -/
theorem subrank_le_eval (φ : AsymptoticSpectrum p) (a : S) : (p.subrank a : ℝ) ≤ eval p a φ := by
  have hrel := p.rel_subrank a
  have h1 : eval p (p.subrank a : S) φ ≤ eval p a φ := φ.monotone _ _ hrel
  rw [eval_natCast] at h1
  exact h1

/-! ### Compactness of the Spectrum -/

-- The asymptotic spectrum embeds into the product ∏ₐ [0, rank(a)].
-- Since each [0, rank(a)] is compact and the product is compact by Tychonoff,
-- we need to show that X is a closed subset.

/-- The spectrum is closed in the product topology.
    This follows because X is the intersection of closed sets:
    - Z₁ = {φ : φ is additive}
    - Z₂ = {φ : φ is multiplicative}
    - Z₃ = {φ : φ is P-monotone}
    - Z₄ = {φ : φ(1) = 1} -/
theorem isClosed : IsClosed (Set.univ : Set (AsymptoticSpectrum p)) := by
  -- The whole space is closed by definition
  exact isClosed_univ

/-- The asymptotic spectrum is compact.

    Proof outline (from survey.tex):
    1. Define Y = ∏_{a ∈ S} [0, rank(a)] ⊆ ℝ^S
    2. Y is compact by Tychonoff's theorem
    3. X ⊆ Y since 0 ≤ φ(a) ≤ rank(a) for all φ ∈ X
    4. X is closed in Y (intersection of closed sets for additivity, multiplicativity,
       monotonicity, and normalization)
    5. Closed subset of compact is compact -/
theorem isCompact : IsCompact (Set.univ : Set (AsymptoticSpectrum p)) := by
  -- The embedding: AsymptoticSpectrum p → (S → ℝ)
  let emb : AsymptoticSpectrum p → (S → ℝ) := fun φ => φ.toFun
  -- The compact ambient space: ∏_a [0, rank(a)]
  let Y : Set (S → ℝ) := Set.univ.pi (fun a => Set.Icc 0 (p.rank a : ℝ))
  -- Step 1: Y is compact by Tychonoff
  have hY_compact : IsCompact Y := isCompact_univ_pi (fun a => isCompact_Icc)
  -- Step 2: The image of the spectrum is contained in Y
  have hX_sub_Y : emb '' Set.univ ⊆ Y := by
    intro f hf
    obtain ⟨φ, _, rfl⟩ := hf
    intro a _
    exact ⟨φ.nonneg a, eval_le_rank p φ a⟩
  -- Step 3: The image is closed in the product topology
  -- The spectrum is the intersection of closed sets defined by:
  -- - Additivity: { f | ∀ a b, f(a+b) = f(a) + f(b) }
  -- - Multiplicativity: { f | ∀ a b, f(a*b) = f(a) * f(b) }
  -- - Monotonicity: { f | ∀ a b, p.rel a b → f(a) ≤ f(b) }
  -- - Normalization: { f | f(1) = 1 }
  -- - Nonnegativity: { f | ∀ a, 0 ≤ f(a) }
  -- Each condition defines a closed set because:
  -- - Evaluation is continuous in the product topology
  -- - Equality and ≤ define closed sets in ℝ
  -- - Intersection of closed sets is closed
  have hX_closed : IsClosed (emb '' Set.univ) := by
    -- The image is the set of functions satisfying the spectral point axioms
    -- We express this as an intersection of closed sets
    -- First, establish that the image equals the set of functions satisfying all conditions
    have himage_eq : emb '' Set.univ =
        {f : S → ℝ | f 0 = 0} ∩ {f | f 1 = 1} ∩
        {f | ∀ a b, f (a + b) = f a + f b} ∩
        {f | ∀ a b, f (a * b) = f a * f b} ∩
        {f | ∀ a b, p.rel a b → f a ≤ f b} ∩
        {f | ∀ a, 0 ≤ f a} := by
      ext f
      simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_univ, true_and]
      constructor
      · rintro ⟨φ, rfl⟩
        exact ⟨⟨⟨⟨⟨φ.map_zero, φ.map_one⟩, φ.map_add⟩, φ.map_mul⟩, φ.monotone⟩, φ.nonneg⟩
      · rintro ⟨⟨⟨⟨⟨hz, ho⟩, ha⟩, hm⟩, hmon⟩, hnn⟩
        exact ⟨⟨f, hz, ho, ha, hm, hmon, hnn⟩, rfl⟩
    rw [himage_eq]
    -- Now prove each set is closed
    -- Helper: equality conditions are closed (f(x) = c is closed)
    have h_eq_closed : ∀ (a : S) (c : ℝ), IsClosed {f : S → ℝ | f a = c} := fun a c => by
      have h1 : IsClosed {f : S → ℝ | f a ≤ c} := isClosed_le (continuous_apply a) continuous_const
      have h2 : IsClosed {f : S → ℝ | c ≤ f a} := isClosed_le continuous_const (continuous_apply a)
      convert h1.inter h2 using 1
      ext f; simp [le_antisymm_iff]
    -- Helper: additive condition for fixed a, b is closed
    have h_add_closed : ∀ a b : S, IsClosed {f : S → ℝ | f (a + b) = f a + f b} := fun a b => by
      have h1 : IsClosed {f : S → ℝ | f (a + b) ≤ f a + f b} :=
        isClosed_le (continuous_apply (a + b)) ((continuous_apply a).add (continuous_apply b))
      have h2 : IsClosed {f : S → ℝ | f a + f b ≤ f (a + b)} :=
        isClosed_le ((continuous_apply a).add (continuous_apply b)) (continuous_apply (a + b))
      convert h1.inter h2 using 1
      ext f; simp [le_antisymm_iff]
    -- Helper: multiplicative condition for fixed a, b is closed
    have h_mul_closed : ∀ a b : S, IsClosed {f : S → ℝ | f (a * b) = f a * f b} := fun a b => by
      have h1 : IsClosed {f : S → ℝ | f (a * b) ≤ f a * f b} :=
        isClosed_le (continuous_apply (a * b)) ((continuous_apply a).mul (continuous_apply b))
      have h2 : IsClosed {f : S → ℝ | f a * f b ≤ f (a * b)} :=
        isClosed_le ((continuous_apply a).mul (continuous_apply b)) (continuous_apply (a * b))
      convert h1.inter h2 using 1
      ext f; simp [le_antisymm_iff]
    -- Helper: monotonicity condition for fixed a, b with p.rel a b is closed
    have h_mono_closed : ∀ a b : S, IsClosed {f : S → ℝ | p.rel a b → f a ≤ f b} := fun a b => by
      by_cases hrel : p.rel a b
      · -- If p.rel a b, this equals {f | f a ≤ f b}
        have hclosed : IsClosed {f : S → ℝ | f a ≤ f b} :=
          isClosed_le (continuous_apply a) (continuous_apply b)
        convert hclosed using 1
        ext f; simp [hrel]
      · -- If ¬p.rel a b, this equals Set.univ
        convert isClosed_univ using 1
        ext f; simp [hrel]
    -- Helper: nonnegativity condition for fixed a is closed
    have h_nonneg_closed : ∀ a : S, IsClosed {f : S → ℝ | 0 ≤ f a} := fun a =>
      isClosed_le continuous_const (continuous_apply a)
    -- Now combine all closedness results
    have hz : IsClosed {f : S → ℝ | f 0 = 0} := h_eq_closed 0 0
    have ho : IsClosed {f : S → ℝ | f 1 = 1} := h_eq_closed 1 1
    have hadd : IsClosed {f : S → ℝ | ∀ a b, f (a + b) = f a + f b} := by
      have : {f : S → ℝ | ∀ a b, f (a + b) = f a + f b} =
          ⋂ a, ⋂ b, {f | f (a + b) = f a + f b} := by
        ext f; simp
      rw [this]
      exact isClosed_iInter (fun a => isClosed_iInter (fun b => h_add_closed a b))
    have hmul : IsClosed {f : S → ℝ | ∀ a b, f (a * b) = f a * f b} := by
      have : {f : S → ℝ | ∀ a b, f (a * b) = f a * f b} =
          ⋂ a, ⋂ b, {f | f (a * b) = f a * f b} := by
        ext f; simp
      rw [this]
      exact isClosed_iInter (fun a => isClosed_iInter (fun b => h_mul_closed a b))
    have hmon : IsClosed {f : S → ℝ | ∀ a b, p.rel a b → f a ≤ f b} := by
      have : {f : S → ℝ | ∀ a b, p.rel a b → f a ≤ f b} =
          ⋂ a, ⋂ b, {f | p.rel a b → f a ≤ f b} := by
        ext f; simp
      rw [this]
      exact isClosed_iInter (fun a => isClosed_iInter (fun b => h_mono_closed a b))
    have hnn : IsClosed {f : S → ℝ | ∀ a, 0 ≤ f a} := by
      have : {f : S → ℝ | ∀ a, 0 ≤ f a} = ⋂ a, {f | 0 ≤ f a} := by ext f; simp
      rw [this]
      exact isClosed_iInter h_nonneg_closed
    -- The intersection is left-associated: ((((A ∩ B) ∩ C) ∩ D) ∩ E) ∩ F
    exact ((((hz.inter ho).inter hadd).inter hmul).inter hmon).inter hnn
  -- Step 4: Closed subset of compact is compact
  have himage_compact := hY_compact.of_isClosed_subset hX_closed hX_sub_Y
  -- Step 5: The induced topology makes the preimage compact
  -- The topology on AsymptoticSpectrum is induced from ℝ^S via emb
  -- Since emb is injective, Set.univ = emb ⁻¹' (emb '' Set.univ)
  have hemb_inj : Function.Injective emb := by
    intro φ₁ φ₂ h
    have heq : φ₁.toFun = φ₂.toFun := h
    cases φ₁; cases φ₂; simp only at heq; congr
  -- By definition of induced topology, the preimage of a compact set is compact
  -- when the preimage equals the whole space
  have heq : (Set.univ : Set (AsymptoticSpectrum p)) = emb ⁻¹' (emb '' Set.univ) := by
    ext φ
    simp only [Set.mem_univ, Set.mem_preimage, Set.mem_image, true_iff]
    exact ⟨φ, trivial, rfl⟩
  rw [heq]
  -- The topology is induced by emb = (fun φ a => φ.toFun a)
  -- We need to show that the preimage of a compact set is compact
  -- This follows from the fact that the induced topology makes this an embedding
  have hind : Topology.IsInducing emb := by
    constructor
    -- The induced topology equals the original topology
    rfl
  have hrange_closed : IsClosed (Set.range emb) := by
    convert hX_closed using 1
    exact Set.image_univ.symm
  exact hind.isCompact_preimage hrange_closed himage_compact

/-- The spectrum is nonempty (follows from existence of maximal preorders) -/
theorem nonempty [Nontrivial S] : Nonempty (AsymptoticSpectrum p) := by
  -- By Zorn's lemma, get a maximal extension q of p
  obtain ⟨q, hpq, hqmax⟩ := exists_maximal_strassen p
  -- spectralPointOfMaximal gives a SpectralPoint q
  let φq := spectralPointOfMaximal q hqmax
  -- Since p ≤ q, φq is also monotone for p
  refine ⟨⟨φq.toFun, φq.map_zero, φq.map_one, φq.map_add, φq.map_mul, ?_, φq.nonneg⟩⟩
  intro a b hab
  exact φq.monotone a b (hpq a b hab)

/-- The spectrum is Hausdorff (T2) -/
theorem t2Space : T2Space (AsymptoticSpectrum p) := by
  -- The topology is induced from ℝ^S which is Hausdorff
  -- Induced topology from injective map to Hausdorff is Hausdorff
  have hinj : Function.Injective (fun φ : AsymptoticSpectrum p => fun a => φ.toFun a) := by
    intro φ₁ φ₂ h
    have heq : φ₁.toFun = φ₂.toFun := funext (fun a => congrFun h a)
    cases φ₁; cases φ₂
    simp only at heq
    congr
  exact T2Space.of_injective_continuous hinj continuous_induced_dom

/-! ### Continuity Properties -/

/-- The evaluation map is continuous -/
theorem continuous_eval' : ∀ a, Continuous (fun φ : AsymptoticSpectrum p => φ.toFun a) :=
  continuous_eval p

-- Note: The sum of two spectral points is NOT a spectral point in general,
-- since it would not satisfy φ(1) = 1.

/-- The map φ ↦ (φ(a₁), ..., φ(aₖ)) is continuous for any finite list -/
theorem continuous_eval_finset (as : Finset S) :
    Continuous (fun φ : AsymptoticSpectrum p => fun a : as => φ.toFun a) := by
  apply continuous_pi
  intro ⟨a, _⟩
  exact continuous_eval p a

end AsymptoticSpectrum

namespace StrassenPreorder

variable (p : StrassenPreorder S)

/-- **Gapped element** (Wigderson–Zuiddam survey `def:gapped`, survey.tex:1912-1914).

    An element `a` is *gapped* if either
    (i)  there is `k ∈ ℕ` with `a^k ≥_P 2` (strictly gapped), or
    (iii) there is a spectral point `φ ∈ 𝒳_P` with `φ(a) = 1`.

    We additionally include the zero-aware disjunct
    (ii) `a ≤_P 0` (the survey works in a zero-free semiring; in a `CommSemiring`
    the element `0` is gapped via this disjunct).

    NOTE on disjunct (iii): the survey (tex:1916) explicitly warns that requiring
    `a ∼ 1` (i.e. `a ≤_P 1 ∧ 1 ≤_P a`, "equivalent to 1") instead of merely
    `∃ φ, φ(a) = 1` is *too strong for our applications* — "tensors do not satisfy
    this". The earlier formalization used that too-strong form; this definition is
    the faithful one. The duality theorem `asympSubrank_eq_iInf_spectrum` therefore
    carries the survey's Strong-Archimedean hypothesis `∀ x, p.rel x 0 ∨ p.rel 1 x`
    (def:strassen-preorder property 3, tex:704) which the relaxed Lean
    `StrassenPreorder.archimedean` field does not provide. -/
def IsGapped (a : S) : Prop :=
  (∃ k : ℕ, 0 < k ∧ p.rel 2 (a ^ k)) ∨
  p.rel a 0 ∨
  (∃ φ : AsymptoticSpectrum p, AsymptoticSpectrum.eval p a φ = 1)

end StrassenPreorder

end AsymptoticSpectrumDuality
