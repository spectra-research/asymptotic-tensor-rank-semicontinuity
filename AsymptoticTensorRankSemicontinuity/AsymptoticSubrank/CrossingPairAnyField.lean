/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.MaxRankBound
import AsymptoticTensorRankSemicontinuity.Prerequisites.Matrix.SubmatrixDet
import AsymptoticTensorRankSemicontinuity.Prerequisites.Matrix.PencilCommonFactor
import Mathlib.Algebra.Order.Ring.Star

/-!
# Field-general crossing-pair extraction

This file is the field-general replacement for
`exists_crossing_pair_of_flatRank_cut_ge_two`: the desired statement removes the
`[Infinite F]` hypothesis.
-/

namespace Semicontinuity

universe u

variable {F : Type u} [Field F]

open Matrix

/-!
## Rank-≤1 pencils

The following is the field-general rank-≤1 pencil lemma in the two-column
matrix form needed by the crossing-pair argument.  It is a direct consequence
of the rectangular rank-one classification in `StabDim`.
-/

/-- A subspace of `m × 2` matrices all of whose elements have rank at most one
has either a nonzero common right-kernel vector or a common image line. -/
theorem exists_common_kernel_or_common_image_line_of_rank_le_one_matrix
    {m : ℕ} (V : Submodule F (Matrix (Fin m) (Fin 2) F))
    (hV : ∀ M ∈ V, M.rank ≤ 1) :
    (∃ x : Fin 2 → F, x ≠ 0 ∧ ∀ M ∈ V, M.mulVec x = 0) ∨
      (∃ L : Submodule F (Fin m → F), Module.finrank F L ≤ 1 ∧
        ∀ M ∈ V, LinearMap.range M.mulVecLin ≤ L) := by
  classical
  rcases Matrix.common_factor_strong_of_rank_le_one_rect V hV with
    h_zero | ⟨uA, _huA, h_align_u⟩ | ⟨vA, hvA, h_align_v⟩
  · right
    refine ⟨⊥, by simp, fun M hM => ?_⟩
    rw [h_zero M hM]
    simp
  · right
    refine ⟨F ∙ uA, ?_, fun M hM => ?_⟩
    · refine le_trans (finrank_span_le_card (R := F) ({uA} : Set (Fin m → F))) ?_
      simp
    · obtain ⟨u, v, hM_eq, hu_mem⟩ := h_align_u M hM
      rintro y ⟨x, rfl⟩
      rw [hM_eq]
      have hmul :
          Matrix.mulVecLin (Matrix.vecMulVec u v) x =
            ((v 0 * x 0 + v 1 * x 1) : F) • u := by
        ext i
        simp [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Fin.sum_univ_two]
        ring
      rw [hmul]
      exact Submodule.smul_mem _ _ hu_mem
  · left
    obtain ⟨x, hx_ne, hx_dot⟩ :=
      Matrix.exists_dotProduct_eq_zero (K := F) (n := 2) hvA (by norm_num)
    refine ⟨x, hx_ne, fun M hM => ?_⟩
    obtain ⟨u, v, hM_eq, hv_mem⟩ := h_align_v M hM
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv_mem
    have hvAx : vA ⬝ᵥ x = 0 := by
      rw [dotProduct_comm]
      exact hx_dot
    have hvx : v ⬝ᵥ x = 0 := by
      rw [← hc, smul_dotProduct, smul_eq_mul, hvAx, mul_zero]
    rw [hM_eq, Matrix.vecMulVec_mulVec, hvx]
    simp

/-!
## Product-covector localization

The next definitions package the coordinate form of product-covector
contraction for the `KTensor` model from `MaxRankBound`.  A family
`ψ a ha : Fin (d a) → F` is one covector on every leg `a ≠ i`; the contraction
keeps the `i`-leg and sums over all tensor coordinates with the product of the
other covector evaluations.
-/

/-- The scalar weight used by `productCovectorContraction`: it is the product
of the selected covectors over all legs except `i`, with an indicator forcing
the surviving `i`-coordinate to be `q`. -/
noncomputable def productCovectorWeight {k : ℕ} {d : Fin k → ℕ+}
    (i : Fin k) (ψ : ∀ a : Fin k, a ≠ i → Fin (d a) → F)
    (q : Fin (d i)) (idx : ∀ a : Fin k, Fin (d a)) : F :=
  if idx i = q then
    (∏ a : Fin k, if h : a = i then (1 : F) else ψ a h (idx a))
  else 0

/-- Product-covector contraction to the surviving leg `i`, in the concrete
coordinate tensor model `KTensor F d`. -/
noncomputable def productCovectorContraction {k : ℕ} {d : Fin k → ℕ+}
    (i : Fin k) (ψ : ∀ a : Fin k, a ≠ i → Fin (d a) → F) :
    KTensor F d →ₗ[F] (Fin (d i) → F) where
  toFun T := fun q =>
    ∑ idx : (∀ a : Fin k, Fin (d a)),
      productCovectorWeight (F := F) i ψ q idx * T idx
  map_add' T U := by
    ext q
    simp [productCovectorWeight, mul_add, Finset.sum_add_distrib]
  map_smul' c T := by
    ext q
    simp [productCovectorWeight, smul_eq_mul, Finset.mul_sum, mul_assoc, mul_comm]

@[simp]
lemma productCovectorContraction_apply {k : ℕ} {d : Fin k → ℕ+}
    (i : Fin k) (ψ : ∀ a : Fin k, a ≠ i → Fin (d a) → F)
    (T : KTensor F d) (q : Fin (d i)) :
    productCovectorContraction (F := F) i ψ T q =
      ∑ idx : (∀ a : Fin k, Fin (d a)),
        productCovectorWeight (F := F) i ψ q idx * T idx := rfl

private lemma sum_mul_productCovectorWeight {k : ℕ} {d : Fin k → ℕ+}
    (i : Fin k) (ψ : ∀ a : Fin k, a ≠ i → Fin (d a) → F)
    (B : Fin (d i) → F) (idx : ∀ a : Fin k, Fin (d a)) :
    (∑ q : Fin (d i), B q * productCovectorWeight (F := F) i ψ q idx) =
      B (idx i) *
        (∏ a : Fin k, if h : a = i then (1 : F) else ψ a h (idx a)) := by
  classical
  rw [Finset.sum_eq_single (idx i)]
  · rw [productCovectorWeight, if_pos rfl]
  · intro q _ hq
    rw [productCovectorWeight, if_neg hq.symm]
    simp
  · intro hq
    exact False.elim (hq (Finset.mem_univ _))

private lemma sum_productCovectorWeight_mul {k : ℕ} {d : Fin k → ℕ+}
    (i : Fin k) (ψ : ∀ a : Fin k, a ≠ i → Fin (d a) → F)
    (B : Fin (d i) → F) (idx : ∀ a : Fin k, Fin (d a)) :
    (∑ q : Fin (d i), productCovectorWeight (F := F) i ψ q idx * B q) =
      (∏ a : Fin k, if h : a = i then (1 : F) else ψ a h (idx a)) *
        B (idx i) := by
  classical
  rw [Finset.sum_eq_single (idx i)]
  · rw [productCovectorWeight, if_pos rfl]
  · intro q _ hq
    rw [productCovectorWeight, if_neg hq.symm]
    simp
  · intro hq
    exact False.elim (hq (Finset.mem_univ _))

private lemma prod_dite_special_eq_mul {α : Type*} [Fintype α] [DecidableEq α]
    (i : α) (x : F) (f : ∀ a : α, a ≠ i → F) :
    (∏ a : α, if h : a = i then x else f a h) =
      x * ∏ a : α, if h : a = i then (1 : F) else f a h := by
  classical
  have hleft :
      (∏ a : α, if h : a = i then x else f a h) =
        (if h : i = i then x else f i h) *
          (∏ a ∈ ((Finset.univ : Finset α) \ {i}),
            if h : a = i then x else f a h) :=
    Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ i) _
  have hright :
      (∏ a : α, if h : a = i then (1 : F) else f a h) =
        (if h : i = i then (1 : F) else f i h) *
          (∏ a ∈ ((Finset.univ : Finset α) \ {i}),
            if h : a = i then (1 : F) else f a h) :=
    Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ i) _
  have hout :
      (∏ a ∈ ((Finset.univ : Finset α) \ {i}),
          if h : a = i then x else f a h) =
        (∏ a ∈ ((Finset.univ : Finset α) \ {i}),
          if h : a = i then (1 : F) else f a h) := by
    refine Finset.prod_congr rfl ?_
    intro a ha
    have hne : a ≠ i := by
      intro h
      subst h
      simp at ha
    rw [dif_neg hne, dif_neg hne]
  rw [hleft, hright]
  rw [hout]
  simp

private lemma double_productCovectorWeight_sum
    {k₁ k₂ : ℕ} {d₁ : Fin k₁ → ℕ+} {d₂ : Fin k₂ → ℕ+}
    (i₁ : Fin k₁) (ψ₁ : ∀ a : Fin k₁, a ≠ i₁ → Fin (d₁ a) → F)
    (i₂ : Fin k₂) (ψ₂ : ∀ a : Fin k₂, a ≠ i₂ → Fin (d₂ a) → F)
    (B₁ : Fin (d₁ i₁) → F) (B₂ : Fin (d₂ i₂) → F)
    (idx₁ : ∀ a : Fin k₁, Fin (d₁ a)) (idx₂ : ∀ a : Fin k₂, Fin (d₂ a))
    (c : F) :
    (∑ q₁ : Fin (d₁ i₁), ∑ q₂ : Fin (d₂ i₂),
        B₁ q₁ *
            (productCovectorWeight (F := F) i₂ ψ₂ q₂ idx₂ *
              (productCovectorWeight (F := F) i₁ ψ₁ q₁ idx₁ * c)) *
          B₂ q₂) =
      ((∏ a : Fin k₂, if h : a = i₂ then (1 : F) else ψ₂ a h (idx₂ a)) *
          B₂ (idx₂ i₂)) *
        ((B₁ (idx₁ i₁) *
            (∏ a : Fin k₁, if h : a = i₁ then (1 : F) else ψ₁ a h (idx₁ a))) *
          c) := by
  classical
  let P₁ : F :=
    ∏ a : Fin k₁, if h : a = i₁ then (1 : F) else ψ₁ a h (idx₁ a)
  let P₂ : F :=
    ∏ a : Fin k₂, if h : a = i₂ then (1 : F) else ψ₂ a h (idx₂ a)
  calc
    (∑ q₁ : Fin (d₁ i₁), ∑ q₂ : Fin (d₂ i₂),
        B₁ q₁ *
            (productCovectorWeight (F := F) i₂ ψ₂ q₂ idx₂ *
              (productCovectorWeight (F := F) i₁ ψ₁ q₁ idx₁ * c)) *
          B₂ q₂)
        = ∑ q₁ : Fin (d₁ i₁),
            (∑ q₂ : Fin (d₂ i₂),
              productCovectorWeight (F := F) i₂ ψ₂ q₂ idx₂ * B₂ q₂) *
              (B₁ q₁ * productCovectorWeight (F := F) i₁ ψ₁ q₁ idx₁ * c) := by
          refine Finset.sum_congr rfl ?_
          intro q₁ _
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro q₂ _
          ring
    _ = ∑ q₁ : Fin (d₁ i₁),
            (P₂ * B₂ (idx₂ i₂)) *
              (B₁ q₁ * productCovectorWeight (F := F) i₁ ψ₁ q₁ idx₁ * c) := by
          rw [sum_productCovectorWeight_mul]
    _ = (P₂ * B₂ (idx₂ i₂)) *
          (∑ q₁ : Fin (d₁ i₁),
            (B₁ q₁ * productCovectorWeight (F := F) i₁ ψ₁ q₁ idx₁) * c) := by
          rw [Finset.mul_sum]
    _ = (P₂ * B₂ (idx₂ i₂)) *
          ((∑ q₁ : Fin (d₁ i₁),
            B₁ q₁ * productCovectorWeight (F := F) i₁ ψ₁ q₁ idx₁) * c) := by
          rw [Finset.sum_mul]
    _ = (P₂ * B₂ (idx₂ i₂)) * ((B₁ (idx₁ i₁) * P₁) * c) := by
          rw [sum_mul_productCovectorWeight]
    _ = ((∏ a : Fin k₂, if h : a = i₂ then (1 : F) else ψ₂ a h (idx₂ a)) *
          B₂ (idx₂ i₂)) *
        ((B₁ (idx₁ i₁) *
            (∏ a : Fin k₁, if h : a = i₁ then (1 : F) else ψ₁ a h (idx₁ a))) *
          c) := by
          rfl

/-- The format obtained by deleting leg `0` from a nonempty `Fin`-indexed
format. -/
def productCovectorTailFormat0 {k : ℕ} (d : Fin (k + 1) → ℕ+) : Fin k → ℕ+ :=
  fun a => d a.succ

/-- Contraction of the split-off leg `0` by a covector.  This is the concrete
map used in the clean leg-removal induction for product-covector localization. -/
noncomputable def splitLeg0Contraction {k : ℕ} {d : Fin (k + 1) → ℕ+}
    (β : Fin (d 0) → F) :
    KTensor F d →ₗ[F] KTensor F (productCovectorTailFormat0 d) where
  toFun T := fun rest => ∑ x0 : Fin (d 0), β x0 * T (Fin.cons x0 rest)
  map_add' T U := by
    ext rest
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c T := by
    ext rest
    change (∑ x0 : Fin (d 0), β x0 * (c * T (Fin.cons x0 rest))) =
      c * (∑ x0 : Fin (d 0), β x0 * T (Fin.cons x0 rest))
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x0 _ => by ring

@[simp]
lemma splitLeg0Contraction_apply {k : ℕ} {d : Fin (k + 1) → ℕ+}
    (β : Fin (d 0) → F) (T : KTensor F d)
    (rest : ∀ a : Fin k, Fin (productCovectorTailFormat0 d a)) :
    splitLeg0Contraction (F := F) β T rest =
      ∑ x0 : Fin (d 0), β x0 * T (Fin.cons x0 rest) := rfl

lemma splitLeg0Contraction_single_apply {k : ℕ} {d : Fin (k + 1) → ℕ+}
    (x0 : Fin (d 0)) (T : KTensor F d)
    (rest : ∀ a : Fin k, Fin (productCovectorTailFormat0 d a)) :
    splitLeg0Contraction (F := F) (Pi.single x0 (1 : F)) T rest =
      T (Fin.cons x0 rest) := by
  classical
  rw [splitLeg0Contraction_apply]
  rw [Finset.sum_eq_single x0]
  · simp
  · intro y _ hy
    rw [Pi.single_eq_of_ne hy, zero_mul]
  · intro hx0
    exact False.elim (hx0 (Finset.mem_univ x0))

lemma eq_zero_of_forall_splitLeg0Contraction_eq_zero
    {k : ℕ} {d : Fin (k + 1) → ℕ+} (T : KTensor F d)
    (hT : ∀ β : Fin (d 0) → F,
      splitLeg0Contraction (F := F) β T = 0) :
    T = 0 := by
  classical
  funext idx
  have hδ := congrFun (hT (Pi.single (idx 0) (1 : F))) (Fin.tail idx)
  rw [splitLeg0Contraction_single_apply] at hδ
  simpa [Fin.cons_self_tail] using hδ

/-- Tail-coordinate delta product covectors for localization to leg `0`. -/
noncomputable def productCovectorTailDelta0 {k : ℕ} {d : Fin (k + 1) → ℕ+}
    (rest0 : ∀ a : Fin k, Fin (productCovectorTailFormat0 d a)) :
    ∀ a : Fin (k + 1), a ≠ 0 → Fin (d a) → F :=
  fun a ha =>
    Fin.cases
      (motive := fun a : Fin (k + 1) => a ≠ 0 → Fin (d a) → F)
      (fun h => False.elim (h rfl))
      (fun a _ => Pi.single (rest0 a) (1 : F))
      a ha

@[simp]
lemma productCovectorTailDelta0_succ {k : ℕ} {d : Fin (k + 1) → ℕ+}
    (rest0 : ∀ a : Fin k, Fin (productCovectorTailFormat0 d a))
    (a : Fin k) (h : a.succ ≠ (0 : Fin (k + 1))) :
    productCovectorTailDelta0 (F := F) (d := d) rest0 a.succ h =
      Pi.single (rest0 a) (1 : F) := rfl

lemma productCovectorTailDelta0_prod_eq_zero {k : ℕ}
    {d : Fin (k + 1) → ℕ+}
    (rest0 rest : ∀ a : Fin k, Fin (productCovectorTailFormat0 d a))
    (hrest : rest ≠ rest0) :
    (∏ a : Fin k,
      (Pi.single (rest0 a) (1 : F) :
        Fin (productCovectorTailFormat0 d a) → F) (rest a)) = 0 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : Fin k, rest a ≠ rest0 a := by
    by_contra h
    apply hrest
    funext a
    by_contra ha
    exact h ⟨a, ha⟩
  rw [Finset.prod_eq_zero_iff]
  refine ⟨a, Finset.mem_univ a, ?_⟩
  change
    (Pi.single (rest0 a) (1 : F) :
      Fin (productCovectorTailFormat0 d a) → F) (rest a) = 0
  rw [Pi.single_eq_of_ne ha]

lemma productCovectorWeight_tailDelta0_cons {k : ℕ}
    {d : Fin (k + 1) → ℕ+}
    (rest0 : ∀ a : Fin k, Fin (productCovectorTailFormat0 d a))
    (q x0 : Fin (d 0))
    (rest : ∀ a : Fin k, Fin (productCovectorTailFormat0 d a)) :
    productCovectorWeight (F := F) (d := d) 0
        (productCovectorTailDelta0 (F := F) (d := d) rest0) q
        (Fin.cons x0 rest) =
      if x0 = q then if rest = rest0 then 1 else 0 else 0 := by
  classical
  by_cases hxq : x0 = q
  · subst x0
    by_cases hrest : rest = rest0
    · subst hrest
      rw [productCovectorWeight]
      simp [Fin.prod_univ_succ, productCovectorTailFormat0]
    · rw [productCovectorWeight]
      simp only [Fin.cons_zero, ↓reduceIte]
      have hprod :
          (∏ a : Fin (k + 1),
              if h : a = 0 then (1 : F)
              else productCovectorTailDelta0 (F := F) (d := d) rest0 a h
                ((Fin.cons q rest : ∀ a : Fin (k + 1), Fin (d a)) a)) = 0 := by
        rw [Fin.prod_univ_succ]
        simp [productCovectorTailFormat0,
          productCovectorTailDelta0_prod_eq_zero (F := F) (d := d) rest0 rest hrest]
      rw [hprod]
      simp [hrest]
  · rw [productCovectorWeight]
    simp [hxq]

lemma productCovectorContraction_tailDelta0_apply {k : ℕ}
    {d : Fin (k + 1) → ℕ+}
    (rest0 : ∀ a : Fin k, Fin (productCovectorTailFormat0 d a))
    (T : KTensor F d) (q : Fin (d 0)) :
    productCovectorContraction (F := F) (d := d) 0
        (productCovectorTailDelta0 (F := F) (d := d) rest0) T q =
      T (Fin.cons q rest0) := by
  classical
  rw [productCovectorContraction_apply]
  rw [← (Fin.consEquiv (fun a : Fin (k + 1) => Fin (d a))).sum_comp
      (fun idx =>
        productCovectorWeight (F := F) (d := d) 0
          (productCovectorTailDelta0 (F := F) (d := d) rest0) q idx * T idx)]
  rw [Fintype.sum_prod_type]
  change
    (∑ x0 : Fin (d 0),
      ∑ rest : (∀ a : Fin k, Fin (productCovectorTailFormat0 d a)),
        productCovectorWeight (F := F) (d := d) 0
          (productCovectorTailDelta0 (F := F) (d := d) rest0) q
          (Fin.cons x0 rest) * T (Fin.cons x0 rest)) =
      T (Fin.cons q rest0)
  rw [Finset.sum_eq_single q]
  · rw [Finset.sum_eq_single rest0]
    · rw [productCovectorWeight_tailDelta0_cons]
      simp
    · intro rest _ hrest
      rw [productCovectorWeight_tailDelta0_cons]
      simp [hrest]
    · intro hrest0
      exact False.elim (hrest0 (Finset.mem_univ rest0))
  · intro x0 _ hx0
    apply Finset.sum_eq_zero
    intro rest _
    rw [productCovectorWeight_tailDelta0_cons]
    simp [hx0]
  · intro hq
    exact False.elim (hq (Finset.mem_univ q))

/-- The split-leg contraction pencil as a linear family of maps on `E`. -/
noncomputable def splitLeg0ContractionFamilyHom {k : ℕ}
    {d : Fin (k + 1) → ℕ+}
    (E : Submodule F (KTensor F d)) :
    (Fin (d 0) → F) →ₗ[F]
      (E →ₗ[F] KTensor F (productCovectorTailFormat0 d)) where
  toFun β := (splitLeg0Contraction (F := F) β).domRestrict E
  map_add' β γ := by
    ext e rest
    change
      (∑ x0 : Fin (d 0), (β x0 + γ x0) *
          (e : KTensor F d) (Fin.cons x0 rest)) =
        (∑ x0 : Fin (d 0), β x0 *
          (e : KTensor F d) (Fin.cons x0 rest)) +
        (∑ x0 : Fin (d 0), γ x0 *
          (e : KTensor F d) (Fin.cons x0 rest))
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x0 _ => by ring
  map_smul' c β := by
    ext e rest
    change
      (∑ x0 : Fin (d 0), (c * β x0) *
          (e : KTensor F d) (Fin.cons x0 rest)) =
        c * (∑ x0 : Fin (d 0), β x0 *
          (e : KTensor F d) (Fin.cons x0 rest))
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x0 _ => by ring

/-- Hom-form rank-`≤ 1` pencil dichotomy derived from
`exists_common_kernel_or_common_image_line_of_rank_le_one_matrix`.

This is the finite-dimensional linear-map form needed by the split-leg pencil:
all maps in a subspace `M ≤ Hom(X,Y)` have image dimension at most one, and
`dim X = 2`.  The proof is the standard basis/matrix translation into the
two-column matrix lemma. -/
theorem exists_common_kernel_or_common_image_line_of_rank_le_one_linearMap
    {X Y : Type u} [AddCommGroup X] [Module F X] [FiniteDimensional F X]
    [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y]
    (hX : Module.finrank F X = 2) (M : Submodule F (X →ₗ[F] Y))
    (hrk : ∀ A ∈ M, Module.finrank F (LinearMap.range A) ≤ 1) :
    (∃ x : X, x ≠ 0 ∧ ∀ A ∈ M, A x = 0) ∨
      (∃ L : Submodule F Y, Module.finrank F L ≤ 1 ∧
        ∀ A ∈ M, LinearMap.range A ≤ L) := by
  classical
  let m : ℕ := Module.finrank F Y
  let bX : Module.Basis (Fin 2) F X := Module.finBasisOfFinrankEq F X hX
  let bY : Module.Basis (Fin m) F Y := Module.finBasis F Y
  let Φ : (X →ₗ[F] Y) ≃ₗ[F] Matrix (Fin m) (Fin 2) F :=
    LinearMap.toMatrix bX bY
  let V : Submodule F (Matrix (Fin m) (Fin 2) F) :=
    M.map (Φ : (X →ₗ[F] Y) →ₗ[F] Matrix (Fin m) (Fin 2) F)
  have hV : ∀ N ∈ V, N.rank ≤ 1 := by
    intro N hN
    rw [Submodule.mem_map] at hN
    rcases hN with ⟨A, hA, rfl⟩
    have hrankN :
        (Φ A).rank = Module.finrank F (LinearMap.range A) := by
      calc
        (Φ A).rank =
            Module.finrank F (LinearMap.range (Matrix.toLin bX bY (Φ A))) := by
          simpa [Φ] using
            (Matrix.rank_eq_finrank_range_toLin (R := F)
              (A := Φ A) bY bX)
        _ = Module.finrank F (LinearMap.range A) := by
          rw [show Matrix.toLin bX bY (Φ A) = A by
            simp [Φ]]
    change (Φ A).rank ≤ 1
    rw [hrankN]
    exact hrk A hA
  rcases exists_common_kernel_or_common_image_line_of_rank_le_one_matrix
      (F := F) V hV with hker | him
  · left
    rcases hker with ⟨x₀, hx₀_ne, hx₀⟩
    refine ⟨bX.equivFun.symm x₀, ?_, ?_⟩
    · intro hx
      apply hx₀_ne
      have hx_repr := congrArg bX.equivFun hx
      simpa only [LinearEquiv.apply_symm_apply, map_zero] using hx_repr
    · intro A hA
      have hAmem : Φ A ∈ V := by
        change Φ A ∈
          M.map (Φ : (X →ₗ[F] Y) →ₗ[F] Matrix (Fin m) (Fin 2) F)
        exact Submodule.mem_map_of_mem
          (f := (Φ : (X →ₗ[F] Y) →ₗ[F] Matrix (Fin m) (Fin 2) F)) hA
      have hmat : (Φ A).mulVec x₀ = 0 := hx₀ (Φ A) hAmem
      have hrepr :
          (Φ A).mulVec (bX.equivFun (bX.equivFun.symm x₀)) =
            bY.equivFun (A (bX.equivFun.symm x₀)) := by
        simpa [Φ, Module.Basis.equivFun_apply] using
          (LinearMap.toMatrix_mulVec_repr bX bY A (bX.equivFun.symm x₀))
      apply bY.equivFun.injective
      rw [← hrepr]
      simpa only [LinearEquiv.apply_symm_apply, map_zero] using hmat
  · right
    rcases him with ⟨L₀, hL₀_dim, hL₀⟩
    let L : Submodule F Y :=
      L₀.map (bY.equivFun.symm : (Fin m → F) →ₗ[F] Y)
    refine ⟨L, ?_, ?_⟩
    · calc
        Module.finrank F L = Module.finrank F L₀ := by
          simpa [L] using
            (LinearEquiv.finrank_map_eq
              (bY.equivFun.symm : (Fin m → F) ≃ₗ[F] Y) L₀)
        _ ≤ 1 := hL₀_dim
    · intro A hA
      rintro y ⟨x, rfl⟩
      have hAmem : Φ A ∈ V := by
        change Φ A ∈
          M.map (Φ : (X →ₗ[F] Y) →ₗ[F] Matrix (Fin m) (Fin 2) F)
        exact Submodule.mem_map_of_mem
          (f := (Φ : (X →ₗ[F] Y) →ₗ[F] Matrix (Fin m) (Fin 2) F)) hA
      have hcoord_mem : bY.equivFun (A x) ∈ L₀ := by
        apply hL₀ (Φ A) hAmem
        refine ⟨bX.equivFun x, ?_⟩
        simpa [Φ, Module.Basis.equivFun_apply, Matrix.mulVecLin_apply] using
          (LinearMap.toMatrix_mulVec_repr bX bY A x)
      change A x ∈ L₀.map (bY.equivFun.symm : (Fin m → F) →ₗ[F] Y)
      rw [Submodule.mem_map]
      exact ⟨bY.equivFun (A x), hcoord_mem, by simp⟩

/-- Assemble a covector on leg `0` with product covectors on the tail, producing
the covectors needed to localize at the successor leg `i.succ`. -/
def productCovectorCons0 {k : ℕ} {d : Fin (k + 1) → ℕ+}
    (β : Fin (d 0) → F) (i : Fin k)
    (ψ : ∀ a : Fin k, a ≠ i → Fin (productCovectorTailFormat0 d a) → F) :
    ∀ a : Fin (k + 1), a ≠ i.succ → Fin (d a) → F :=
  fun a ha =>
    Fin.cases
      (motive := fun a : Fin (k + 1) => a ≠ i.succ → Fin (d a) → F)
      (fun _ => β)
      (fun a ha' => ψ a (fun h => ha' (by simp [h])))
      a ha

omit [Field F] in
@[simp]
lemma productCovectorCons0_zero {k : ℕ} {d : Fin (k + 1) → ℕ+}
    (β : Fin (d 0) → F) (i : Fin k)
    (ψ : ∀ a : Fin k, a ≠ i → Fin (productCovectorTailFormat0 d a) → F)
    (h : (0 : Fin (k + 1)) ≠ i.succ) :
    productCovectorCons0 (F := F) β i ψ 0 h = β := rfl

omit [Field F] in
@[simp]
lemma productCovectorCons0_succ {k : ℕ} {d : Fin (k + 1) → ℕ+}
    (β : Fin (d 0) → F) (i a : Fin k)
    (ψ : ∀ a : Fin k, a ≠ i → Fin (productCovectorTailFormat0 d a) → F)
    (h : a.succ ≠ i.succ) :
    productCovectorCons0 (F := F) β i ψ a.succ h =
      ψ a (fun ha => h (by simp [ha])) := rfl

lemma productCovectorWeight_succ_cons {k : ℕ} {d : Fin (k + 1) → ℕ+}
    (β : Fin (d 0) → F) (i : Fin k)
    (ψ : ∀ a : Fin k, a ≠ i → Fin (productCovectorTailFormat0 d a) → F)
    (q : Fin (d i.succ)) (x0 : Fin (d 0))
    (rest : ∀ a : Fin k, Fin (d a.succ)) :
    productCovectorWeight (F := F) i.succ
        (productCovectorCons0 (F := F) β i ψ) q (Fin.cons x0 rest) =
      β x0 * productCovectorWeight (F := F) i ψ q rest := by
  classical
  by_cases hq : rest i = q
  · rw [productCovectorWeight, productCovectorWeight]
    have hfull :
        ((Fin.cons x0 rest : ∀ a : Fin (k + 1), Fin (d a)) i.succ) = q := by
      simpa using hq
    have h0 : ¬ (0 : Fin (k + 1)) = i.succ := by
      intro h
      exact Fin.succ_ne_zero i h.symm
    rw [if_pos hfull, if_pos hq]
    simp [h0, Fin.prod_univ_succ]
  · rw [productCovectorWeight, productCovectorWeight]
    have hfull :
        ((Fin.cons x0 rest : ∀ a : Fin (k + 1), Fin (d a)) i.succ) ≠ q := by
      simpa using hq
    rw [if_neg hfull, if_neg hq]
    simp

lemma productCovectorContraction_succ_splitLeg0Contraction
    {k : ℕ} {d : Fin (k + 1) → ℕ+}
    (β : Fin (d 0) → F) (i : Fin k)
    (ψ : ∀ a : Fin k, a ≠ i → Fin (productCovectorTailFormat0 d a) → F)
    (T : KTensor F d) :
    productCovectorContraction (F := F) i ψ
        (splitLeg0Contraction (F := F) β T) =
      productCovectorContraction (F := F) i.succ
        (productCovectorCons0 (F := F) β i ψ) T := by
  classical
  ext q
  rw [productCovectorContraction_apply, productCovectorContraction_apply]
  simp_rw [splitLeg0Contraction_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← (Fin.consEquiv (fun a : Fin (k + 1) => Fin (d a))).sum_comp
      (fun idx =>
        productCovectorWeight (F := F) i.succ
          (productCovectorCons0 (F := F) β i ψ) q idx * T idx)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro x0 _
  refine Finset.sum_congr rfl ?_
  intro rest _
  have hcons :
      ((Fin.consEquiv (fun a : Fin (k + 1) => Fin (d a))) (x0, rest) :
          ∀ a : Fin (k + 1), Fin (d a)) = Fin.cons x0 rest := rfl
  rw [hcons]
  rw [productCovectorWeight_succ_cons (F := F) β i ψ q x0 rest]
  ring

/-- The active legs for product-covector localization: exactly the legs whose
coordinate space has dimension strictly larger than one. -/
def productCovectorActiveLegs {k : ℕ} (d : Fin k → ℕ+) : Finset (Fin k) :=
  Finset.univ.filter fun a => 1 < (d a : ℕ)

/-- The constant-one product covector on every leg except `i`. -/
def productCovectorOnes {k : ℕ} {d : Fin k → ℕ+} (i : Fin k) :
    ∀ a : Fin k, a ≠ i → Fin (d a) → F :=
  fun _ _ _ => 1

private lemma subsingleton_fin_of_not_one_lt_pnat (n : ℕ+) (hn : ¬ 1 < (n : ℕ)) :
    Subsingleton (Fin (n : ℕ)) := by
  have hnle : (n : ℕ) ≤ 1 := le_of_not_gt hn
  have hnpos : 0 < (n : ℕ) := n.2
  have hn_eq : (n : ℕ) = 1 := by omega
  have hn_pnat : n = (1 : ℕ+) := Subtype.ext hn_eq
  subst hn_pnat
  constructor
  intro x y
  apply Fin.ext
  omega

/-- If at most one leg is active, some leg has a one-dimensional complement. -/
lemma exists_subsingleton_complement_of_activeLegs_card_le_one
    {k : ℕ} (hk : 0 < k) {d : Fin k → ℕ+}
    (hcard : (productCovectorActiveLegs d).card ≤ 1) :
    ∃ i : Fin k, ∀ a : Fin k, a ≠ i → Subsingleton (Fin (d a)) := by
  classical
  let A : Finset (Fin k) := productCovectorActiveLegs d
  have hAcard : A.card ≤ 1 := hcard
  by_cases hAne : A.Nonempty
  · obtain ⟨i, hi⟩ := hAne
    refine ⟨i, ?_⟩
    intro a hai
    apply subsingleton_fin_of_not_one_lt_pnat (d a)
    intro ha_active
    apply hai
    exact (Finset.card_le_one_iff.mp hAcard)
      (by simp [A, productCovectorActiveLegs, ha_active]) hi
  · refine ⟨⟨0, hk⟩, ?_⟩
    intro a _ha
    apply subsingleton_fin_of_not_one_lt_pnat (d a)
    intro ha_active
    apply hAne
    exact ⟨a, by simp [A, productCovectorActiveLegs, ha_active]⟩

lemma productCovectorContraction_ones_apply_of_subsingleton_complement
    {k : ℕ} {d : Fin k → ℕ+} (i : Fin k)
    (hcomp : ∀ a : Fin k, a ≠ i → Subsingleton (Fin (d a)))
    (T : KTensor F d) (idx : ∀ a : Fin k, Fin (d a)) :
    productCovectorContraction (F := F) i (productCovectorOnes (F := F) i) T (idx i) =
      T idx := by
  classical
  rw [productCovectorContraction_apply]
  rw [Finset.sum_eq_single idx]
  · have hprod1 :
        (∏ a : Fin k,
            if h : a = i then (1 : F)
            else productCovectorOnes (F := F) (d := d) i a h (idx a)) = 1 := by
      apply Finset.prod_eq_one
      intro a _
      by_cases ha : a = i
      · rw [dif_pos ha]
      · rw [dif_neg ha]
        rfl
    rw [productCovectorWeight, if_pos rfl, hprod1, one_mul]
  · intro idx' _ hidx'
    have hi_ne : idx' i ≠ idx i := by
      intro hi
      apply hidx'
      funext a
      by_cases ha : a = i
      · subst ha
        exact hi
      · haveI : Subsingleton (Fin (d a)) := hcomp a ha
        exact Subsingleton.elim _ _
    rw [productCovectorWeight, if_neg hi_ne, zero_mul]
  · intro hidx
    exact absurd (Finset.mem_univ idx) hidx

lemma productCovectorContraction_ones_injective_of_subsingleton_complement
    {k : ℕ} {d : Fin k → ℕ+} (i : Fin k)
    (hcomp : ∀ a : Fin k, a ≠ i → Subsingleton (Fin (d a))) :
    Function.Injective
      (productCovectorContraction (F := F) (d := d) i
        (productCovectorOnes (F := F) (d := d) i)) := by
  intro T U hTU
  funext idx
  have hq := congrFun hTU (idx i)
  rw [productCovectorContraction_ones_apply_of_subsingleton_complement
        (F := F) i hcomp T idx,
      productCovectorContraction_ones_apply_of_subsingleton_complement
        (F := F) i hcomp U idx] at hq
  exact hq

/-- Base of the active-leg induction: if at most one leg has dimension larger
than one, the tensor product is already detected by keeping that leg and
contracting the one-dimensional complement by the constant-one product
covector. -/
theorem product_covector_localization_of_activeLegs_card_le_one
    {k : ℕ} (hk : 0 < k) {d : Fin k → ℕ+}
    (E : Submodule F (KTensor F d))
    (hcard : (productCovectorActiveLegs d).card ≤ 1) :
    ∃ i : Fin k, ∃ ψ : ∀ a : Fin k, a ≠ i → Fin (d a) → F,
      Function.Injective
        ((productCovectorContraction (F := F) i ψ).domRestrict E) := by
  classical
  obtain ⟨i, hcomp⟩ := exists_subsingleton_complement_of_activeLegs_card_le_one
    hk (d := d) hcard
  refine ⟨i, productCovectorOnes (F := F) (d := d) i, ?_⟩
  have hamb :
      Function.Injective
        (productCovectorContraction (F := F) i (productCovectorOnes (F := F) (d := d) i)) :=
    productCovectorContraction_ones_injective_of_subsingleton_complement
      (F := F) i hcomp
  intro x y hxy
  apply Subtype.ext
  exact hamb hxy

/-- Noninjective split-leg pencil case in the leg-`0` localization step.

If every split-leg contraction `m_β : E → KTensor tail` is noninjective, the
rank-one-pencil dichotomy should force localization to leg `0`.  This is the
independent algebraic branch: prove the Hom-form corollary,
rule out the common-kernel alternative by coordinate deltas, and use the
common image line to build a tail delta product covector. -/
theorem product_covector_localization_leg0_noninjective_family_case
    {k : ℕ} (hk : 0 < k)
    {d : Fin (k + 1) → ℕ+}
    (E : Submodule F (KTensor F d)) (hE : Module.finrank F E = 2)
    (hno : ∀ β : Fin (d 0) → F,
      ¬ Function.Injective
        ((splitLeg0Contraction (F := F) β).domRestrict E)) :
    ∃ i : Fin (k + 1), ∃ ψ : ∀ a : Fin (k + 1), a ≠ i → Fin (d a) → F,
      Function.Injective
        ((productCovectorContraction (F := F) i ψ).domRestrict E) := by
  classical
  let _ := hk
  haveI : FiniteDimensional F E := FiniteDimensional.of_finrank_eq_succ hE
  let Φ := splitLeg0ContractionFamilyHom (F := F) (d := d) E
  let M : Submodule F (E →ₗ[F] KTensor F (productCovectorTailFormat0 d)) :=
    LinearMap.range Φ
  have hrk : ∀ A ∈ M, Module.finrank F (LinearMap.range A) ≤ 1 := by
    intro A hA
    rcases hA with ⟨β, rfl⟩
    have hnot : ¬ Function.Injective (Φ β) := by
      simpa [Φ, splitLeg0ContractionFamilyHom] using hno β
    have hker_ne : LinearMap.ker (Φ β) ≠ ⊥ := by
      intro hker
      exact hnot (LinearMap.ker_eq_bot.mp hker)
    have hker_pos : 1 ≤ Module.finrank F (LinearMap.ker (Φ β)) :=
      Submodule.one_le_finrank_iff.mpr hker_ne
    have hrn := LinearMap.finrank_range_add_finrank_ker (Φ β)
    rw [hE] at hrn
    omega
  rcases exists_common_kernel_or_common_image_line_of_rank_le_one_linearMap
      (F := F) (X := E) (Y := KTensor F (productCovectorTailFormat0 d))
      hE M hrk with
    h_common_ker | h_common_image
  · rcases h_common_ker with ⟨e, he_ne, he_all⟩
    exfalso
    apply he_ne
    apply Subtype.ext
    apply eq_zero_of_forall_splitLeg0Contraction_eq_zero (F := F) (d := d)
    intro β
    have hmem : Φ β ∈ M := LinearMap.mem_range_self Φ β
    have hzero := he_all (Φ β) hmem
    simpa [Φ, splitLeg0ContractionFamilyHom] using hzero
  · rcases h_common_image with ⟨L, hL_dim, hL_range⟩
    have hL_ne_bot : L ≠ ⊥ := by
      intro hL_bot
      have hE_bot : E = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro T hT
        have hT_zero : T = 0 := by
          apply eq_zero_of_forall_splitLeg0Contraction_eq_zero (F := F) (d := d)
          intro β
          let eT : E := ⟨T, hT⟩
          have hmem : Φ β ∈ M := LinearMap.mem_range_self Φ β
          have himage_mem : Φ β eT ∈ L :=
            hL_range (Φ β) hmem (LinearMap.mem_range_self (Φ β) eT)
          have himage_bot : Φ β eT ∈
              (⊥ : Submodule F (KTensor F (productCovectorTailFormat0 d))) := by
            simpa [hL_bot] using himage_mem
          have himage_zero : Φ β eT = 0 := by
            simpa using himage_bot
          simpa [Φ, splitLeg0ContractionFamilyHom, eT] using himage_zero
        simpa using hT_zero
      have hE_zero : Module.finrank F E = 0 := by
        rw [hE_bot, finrank_bot]
      omega
    obtain ⟨u, huL, hu_ne⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot hL_ne_bot
    have hL_le_span : L ≤ F ∙ u := by
      have hspan_le : F ∙ u ≤ L := by
        rw [Submodule.span_singleton_le_iff_mem]
        exact huL
      have hspan_fin : Module.finrank F (F ∙ u) = 1 := by
        rw [show (F ∙ u) = Submodule.span F ({u} :
            Set (KTensor F (productCovectorTailFormat0 d))) from rfl]
        exact finrank_span_singleton hu_ne
      have h_eq : F ∙ u = L :=
        Submodule.eq_of_le_of_finrank_le hspan_le (by
          rw [hspan_fin]
          exact hL_dim)
      rw [← h_eq]
    obtain ⟨rest0, hrest0⟩ :
        ∃ rest0 : ∀ a : Fin k, Fin (productCovectorTailFormat0 d a),
          u rest0 ≠ 0 := by
      by_contra h
      apply hu_ne
      funext rest
      by_contra hrest
      exact h ⟨rest, hrest⟩
    let ψ := productCovectorTailDelta0 (F := F) (d := d) rest0
    refine ⟨0, ψ, ?_⟩
    have h_local_kernel :
        ∀ e : E,
          ((productCovectorContraction (F := F) (d := d) 0 ψ).domRestrict E) e = 0 →
            e = 0 := by
      intro e he
      apply Subtype.ext
      funext idx
      let x0 : Fin (d 0) := idx 0
      let rest : ∀ a : Fin k, Fin (productCovectorTailFormat0 d a) := Fin.tail idx
      let δ : Fin (d 0) → F := Pi.single x0 (1 : F)
      have hmem : Φ δ ∈ M := LinearMap.mem_range_self Φ δ
      have hslice_mem_L : Φ δ e ∈ L :=
        hL_range (Φ δ) hmem (LinearMap.mem_range_self (Φ δ) e)
      have hslice_mem_span : Φ δ e ∈ F ∙ u := hL_le_span hslice_mem_L
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hslice_mem_span
      have hslice_rest0_zero : (Φ δ e) rest0 = 0 := by
        have hq := congrFun he x0
        change productCovectorContraction (F := F) (d := d) 0 ψ
            (e : KTensor F d) x0 = 0 at hq
        rw [productCovectorContraction_tailDelta0_apply] at hq
        have hδ_eval :
            (Φ δ e) rest0 = (e : KTensor F d) (Fin.cons x0 rest0) := by
          change splitLeg0Contraction (F := F) δ (e : KTensor F d) rest0 =
            (e : KTensor F d) (Fin.cons x0 rest0)
          simpa [δ] using
            splitLeg0Contraction_single_apply (F := F) (d := d) x0
              (e : KTensor F d) rest0
        rw [hδ_eval]
        exact hq
      have hc_zero : c = 0 := by
        have hc_eval := congrFun hc rest0
        rw [hslice_rest0_zero] at hc_eval
        have hmul : c * u rest0 = 0 := by
          simpa [Pi.smul_apply, smul_eq_mul] using hc_eval.symm
        exact (mul_eq_zero.mp hmul).resolve_right hrest0
      have hslice_zero : Φ δ e = 0 := by
        rw [← hc, hc_zero, zero_smul]
      have hcoord := congrFun hslice_zero rest
      have hcoord' :
          (e : KTensor F d) (Fin.cons x0 rest) = 0 := by
        have hδ_eval :
            (Φ δ e) rest = (e : KTensor F d) (Fin.cons x0 rest) := by
          change splitLeg0Contraction (F := F) δ (e : KTensor F d) rest =
            (e : KTensor F d) (Fin.cons x0 rest)
          simpa [δ] using
            splitLeg0Contraction_single_apply (F := F) (d := d) x0
              (e : KTensor F d) rest
        rw [hδ_eval] at hcoord
        exact hcoord
      simpa [x0, rest, Fin.cons_self_tail] using hcoord'
    intro x y hxy
    have hsub :
        x - y = (0 : E) := by
      apply h_local_kernel
      rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp hsub

/-- Clean leg-removal step for PL.

This splits a
`(k + 1)`-leg tensor along leg `0`, considers the maps
`(splitLeg0Contraction β).domRestrict E : E → KTensor F (productCovectorTailFormat0 d)`,
and proves the usual dichotomy:

* if one such map is injective, apply the induction hypothesis on its image and
  compose the resulting tail product covectors with `β`;
* otherwise the matrices of all split-leg contractions form a rank-`≤ 1`
  pencil, so `exists_common_kernel_or_common_image_line_of_rank_le_one_matrix`
  gives either an impossible common kernel or a common image line, from which a
  delta product covector on the tail localizes injectively to leg `0`.
-/
theorem product_covector_localization_leg0_induction_step
    {k : ℕ} (hk : 0 < k)
    (IH : ∀ {d' : Fin k → ℕ+} (E' : Submodule F (KTensor F d')),
      Module.finrank F E' = 2 →
        ∃ i : Fin k, ∃ ψ : ∀ a : Fin k, a ≠ i → Fin (d' a) → F,
          Function.Injective
            ((productCovectorContraction (F := F) i ψ).domRestrict E'))
    {d : Fin (k + 1) → ℕ+}
    (E : Submodule F (KTensor F d)) (hE : Module.finrank F E = 2) :
    ∃ i : Fin (k + 1), ∃ ψ : ∀ a : Fin (k + 1), a ≠ i → Fin (d a) → F,
      Function.Injective
        ((productCovectorContraction (F := F) i ψ).domRestrict E) := by
  classical
  by_cases hinj : ∃ β : Fin (d 0) → F,
      Function.Injective ((splitLeg0Contraction (F := F) β).domRestrict E)
  · obtain ⟨β, hβ⟩ := hinj
    let m : E →ₗ[F] KTensor F (productCovectorTailFormat0 d) :=
      (splitLeg0Contraction (F := F) β).domRestrict E
    let E' : Submodule F (KTensor F (productCovectorTailFormat0 d)) :=
      LinearMap.range m
    have hβm : Function.Injective m := by
      simpa [m] using hβ
    have hE' : Module.finrank F E' = 2 := by
      have hker : LinearMap.ker m = ⊥ := LinearMap.ker_eq_bot_of_injective hβm
      have hrn := LinearMap.finrank_range_add_finrank_ker m
      rw [hker, finrank_bot, add_zero, hE] at hrn
      simpa [E'] using hrn
    obtain ⟨i, ψ', hψ'⟩ :=
      IH (d' := productCovectorTailFormat0 d) E' hE'
    refine ⟨i.succ, productCovectorCons0 (F := F) β i ψ', ?_⟩
    intro x y hxy
    apply hβm
    let mx : E' := ⟨m x, LinearMap.mem_range_self m x⟩
    let my : E' := ⟨m y, LinearMap.mem_range_self m y⟩
    have htail :
        ((productCovectorContraction (F := F) i ψ').domRestrict E') mx =
          ((productCovectorContraction (F := F) i ψ').domRestrict E') my := by
      ext q
      have hx :=
        congrFun
          (productCovectorContraction_succ_splitLeg0Contraction
            (F := F) (d := d) β i ψ' (x : KTensor F d)) q
      have hy :=
        congrFun
          (productCovectorContraction_succ_splitLeg0Contraction
            (F := F) (d := d) β i ψ' (y : KTensor F d)) q
      change
        productCovectorContraction (F := F) i ψ'
            (((splitLeg0Contraction (F := F) β).domRestrict E) x) q =
          productCovectorContraction (F := F) i ψ'
            (((splitLeg0Contraction (F := F) β).domRestrict E) y) q
      rw [LinearMap.domRestrict_apply, LinearMap.domRestrict_apply]
      rw [hx, hy]
      simpa [LinearMap.domRestrict_apply] using congrFun hxy q
    have hmxmy : mx = my := hψ' htail
    exact congrArg Subtype.val hmxmy
  · exact product_covector_localization_leg0_noninjective_family_case
      (F := F) hk E hE (by simpa using hinj)

/--
Induction core for PL, reduced to the clean leg-removal step.
-/
theorem product_covector_localization_induction_core
    {k : ℕ} (hk : 0 < k) {d : Fin k → ℕ+}
    (E : Submodule F (KTensor F d)) (hE : Module.finrank F E = 2) :
    ∃ i : Fin k, ∃ ψ : ∀ a : Fin k, a ≠ i → Fin (d a) → F,
      Function.Injective
        ((productCovectorContraction (F := F) i ψ).domRestrict E) := by
  classical
  induction k with
  | zero =>
      omega
  | succ k IH =>
      cases k with
      | zero =>
          exact product_covector_localization_of_activeLegs_card_le_one
            (F := F) hk E (by
              calc
                (productCovectorActiveLegs d).card ≤ Fintype.card (Fin 1) :=
                  Finset.card_le_univ _
                _ = 1 := by simp)
      | succ k =>
          exact product_covector_localization_leg0_induction_step
            (F := F) (k := k + 1) (Nat.succ_pos k)
            (fun {d'} E' hE' => IH (Nat.succ_pos k) E' hE')
            (d := d) E hE

/-- **PL: product-covector localization.**

For any two-dimensional subspace `E` of a nonempty concrete tensor product
`KTensor F d`, some leg `i` admits product covectors on all other legs whose
contraction is injective on `E`.  This is the load-bearing localization lemma
of the crossing-pair assembly. -/
theorem exists_product_covector_localization_anyField
    {k : ℕ} (hk : 0 < k) {d : Fin k → ℕ+}
    (E : Submodule F (KTensor F d)) (hE : Module.finrank F E = 2) :
    ∃ i : Fin k, ∃ ψ : ∀ a : Fin k, a ≠ i → Fin (d a) → F,
      Function.Injective
        ((productCovectorContraction (F := F) i ψ).domRestrict E) :=
  product_covector_localization_induction_core (F := F) hk E hE

/-! ## Pair-subrank membership from a concrete pair-unit restriction -/

private lemma pairUnit_restricts_le_flatRank_local {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (i j : Fin k) (hij : i ≠ j) {r : ℕ} (hr : 0 < r)
    (hres : Restricts (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) T) :
    r ≤ flatRank T {i} := by
  classical
  have hmono := hres.flatRank_le {i}
  have hrank_eq : flatRank (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) {i} = r := by
    have memi : i ∈ ({i} : Finset (Fin k)) := Finset.mem_singleton_self i
    have memj : j ∉ ({i} : Finset (Fin k)) := by
      rw [Finset.mem_singleton]; exact hij.symm
    have hrowval : ∀ x : { x // x ∈ ({i} : Finset (Fin k)) }, x.val = i :=
      fun x => Finset.mem_singleton.mp x.2
    have hnpf_i : ((naturalPairFormat (⟨r, hr⟩ : ℕ+) i j i : ℕ+) : ℕ) = r := by
      unfold naturalPairFormat; rw [if_pos (Or.inl rfl)]; rfl
    have hnpf_j : ((naturalPairFormat (⟨r, hr⟩ : ℕ+) i j j : ℕ+) : ℕ) = r := by
      unfold naturalPairFormat; rw [if_pos (Or.inr rfl)]; rfl
    let eRow : Fin r ≃ ((x : { x // x ∈ ({i} : Finset (Fin k)) })
        → Fin (naturalPairFormat (⟨r, hr⟩ : ℕ+) i j x.val)) :=
      { toFun := fun m x => Fin.cast (by rw [hrowval x, hnpf_i]) m
        invFun := fun row => Fin.cast (by rw [hnpf_i]) (row ⟨i, memi⟩)
        left_inv := by intro m; simp
        right_inv := by
          intro row; funext x
          obtain ⟨x, hx⟩ := x
          have hxi : x = i := Finset.mem_singleton.mp hx
          subst hxi
          simp }
    let eCol : Fin r ≃ ((x : { x // x ∉ ({i} : Finset (Fin k)) })
        → Fin (naturalPairFormat (⟨r, hr⟩ : ℕ+) i j x.val)) :=
      { toFun := fun m x =>
          if hxj : x.val = j then Fin.cast (by rw [hxj, hnpf_j]) m
          else ⟨0, by
            have : ((naturalPairFormat (⟨r, hr⟩ : ℕ+) i j x.val : ℕ+) : ℕ) = 1 := by
              unfold naturalPairFormat
              rw [if_neg]
              · rfl
              · rintro (h | h)
                · exact x.2 (by rw [Finset.mem_singleton]; exact h)
                · exact hxj h
            omega⟩
        invFun := fun col => Fin.cast (by rw [hnpf_j]) (col ⟨j, memj⟩)
        left_inv := by intro m; simp
        right_inv := by
          intro col; funext x
          by_cases hxj : x.val = j
          · obtain ⟨x, hx⟩ := x
            simp only at hxj
            subst hxj
            simp
          · simp only [dif_neg hxj]
            have hone : ((naturalPairFormat (⟨r, hr⟩ : ℕ+) i j x.val : ℕ+) : ℕ) = 1 := by
              unfold naturalPairFormat
              rw [if_neg]
              · rfl
              · rintro (h | h)
                · exact x.2 (by rw [Finset.mem_singleton]; exact h)
                · exact hxj h
            apply Fin.ext
            have h1 := (col x).isLt
            have h2 :
                (⟨0, by omega⟩ :
                  Fin (naturalPairFormat (⟨r, hr⟩ : ℕ+) i j x.val)).val = 0 := rfl
            omega }
    have hid : flattenMatrix (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) {i}
        = Matrix.reindex eRow eCol (1 : Matrix (Fin r) (Fin r) F) := by
      ext rowS colS
      rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]
      change (unitPairTensor (F := F) ⟨r, hr⟩ i j hij)
          (fun x => if h : x ∈ ({i} : Finset (Fin k)) then rowS ⟨x, h⟩
            else colS ⟨x, h⟩) = _
      rw [unitPairTensor]
      rw [dif_pos memi, dif_neg memj]
      by_cases heq : eRow.symm rowS = eCol.symm colS
      · rw [if_pos heq]
        have : (rowS ⟨i, memi⟩).val = (colS ⟨j, memj⟩).val := by
          have hr' : (eRow.symm rowS).val = (rowS ⟨i, memi⟩).val := by
            change (Fin.cast (by rw [hnpf_i]) (rowS ⟨i, memi⟩)).val = _
            rfl
          have hc' : (eCol.symm colS).val = (colS ⟨j, memj⟩).val := by
            change (Fin.cast (by rw [hnpf_j]) (colS ⟨j, memj⟩)).val = _
            rfl
          rw [← hr', ← hc', heq]
        rw [if_pos this]
      · rw [if_neg heq]
        rw [if_neg]
        intro hcontra
        apply heq
        apply Fin.ext
        have hr' : (eRow.symm rowS).val = (rowS ⟨i, memi⟩).val := by
          change (Fin.cast (by rw [hnpf_i]) (rowS ⟨i, memi⟩)).val = _
          rfl
        have hc' : (eCol.symm colS).val = (colS ⟨j, memj⟩).val := by
          change (Fin.cast (by rw [hnpf_j]) (colS ⟨j, memj⟩)).val = _
          rfl
        rw [hr', hc', hcontra]
    rw [flatRank, hid, Matrix.rank_reindex, Matrix.rank_one, Fintype.card_fin]
  rw [hrank_eq] at hmono
  exact hmono

private lemma subrankPair_bddAbove_local {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (i j : Fin k) (hij : i ≠ j) :
    BddAbove { r : ℕ | ∃ hr : 0 < r,
      Restricts (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) T } := by
  refine ⟨flatRank T {i}, ?_⟩
  rintro s ⟨hs, hres⟩
  exact pairUnit_restricts_le_flatRank_local T i j hij hs hres

private lemma subrankPair_ge_two_of_unitPairTensor_two_restricts
    {k : ℕ} {d : Fin k → ℕ+} (T : KTensor F d) (i j : Fin k) (hij : i ≠ j)
    (hres : Restricts (unitPairTensor (F := F) (2 : ℕ+) i j hij) T) :
    2 ≤ subrankPair T i j := by
  classical
  unfold subrankPair
  rw [dif_neg hij]
  refine le_csSup (subrankPair_bddAbove_local T i j hij) ?_
  refine ⟨two_pos, ?_⟩
  simpa using hres

private lemma exists_submodule_le_finrank_eq_two
    {M : Type*} [AddCommGroup M] [Module F M]
    {W : Submodule F M} (hW : 2 ≤ Module.finrank F W) :
    ∃ E : Submodule F M, E ≤ W ∧ Module.finrank F E = 2 := by
  obtain ⟨b, hb⟩ :=
    exists_linearIndependent_of_le_finrank (R := F) (M := W) hW
  let E0 : Submodule F W := Submodule.span F (Set.range b)
  refine ⟨E0.map W.subtype, ?_, ?_⟩
  · rintro x ⟨y, _hy, rfl⟩
    exact y.property
  · have hE0 : Module.finrank F E0 = 2 := by
      have hspan := finrank_span_eq_card (R := F) (b := b) hb
      simpa [E0] using hspan
    calc
      Module.finrank F (E0.map W.subtype) = Module.finrank F E0 :=
        Submodule.finrank_map_subtype_eq W E0
      _ = 2 := hE0

/-- Format of the ordered block of legs in a cut `S`.  The order is the canonical
increasing order of the finset, via `S.orderIsoOfFin`. -/
private def cutRowFormat {k : ℕ} (d : Fin k → ℕ+) (S : Finset (Fin k)) :
    Fin S.card → ℕ+ :=
  fun a => d ((S.orderIsoOfFin rfl a).val)

/-- Reindex the ordered `S`-block tensor space to the row-vector space of the
`S`-flattening. -/
private noncomputable def cutRowLinearEquiv {k : ℕ} {d : Fin k → ℕ+}
    (S : Finset (Fin k)) :
    KTensor F (cutRowFormat d S) ≃ₗ[F]
      ((∀ i : {i : Fin k // i ∈ S}, Fin (d i.val)) → F) :=
  LinearEquiv.funCongrLeft F F
    (Equiv.piCongrLeft
      (fun i : {i : Fin k // i ∈ S} => Fin (d i.val))
      (S.orderIsoOfFin rfl).toEquiv).symm

/-- Apply a product-covector contraction on the ordered `S`-row block to every
column of the `S`-flattening of `T`.  Rows are the surviving localized leg in
the ordered cut; columns are the original complementary multi-indices. -/
private noncomputable def contractedCutMatrix {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (S : Finset (Fin k)) (iS : Fin S.card)
    (ψ : ∀ a : Fin S.card, a ≠ iS → Fin (cutRowFormat d S a) → F) :
    Matrix (Fin (cutRowFormat d S iS))
      (∀ j : {j : Fin k // j ∉ S}, Fin (d j.val)) F :=
  fun q col =>
    productCovectorContraction (F := F) (d := cutRowFormat d S) iS ψ
      ((cutRowLinearEquiv (F := F) (d := d) S).symm
        ((flattenMatrix T S).col col)) q

/-- The already-proved one-side bridge data implies that the S-side contracted
flattening matrix has rank at least two. -/
private lemma contractedCutMatrix_rank_ge_two_of_bridge
    {k : ℕ} {d : Fin k → ℕ+} (T : KTensor F d) (S : Finset (Fin k))
    (iS : Fin S.card)
    (E : Submodule F (KTensor F (cutRowFormat d S)))
    (ψ : ∀ a : Fin S.card, a ≠ iS → Fin (cutRowFormat d S a) → F)
    (hE_map_le :
      E.map (cutRowLinearEquiv (F := F) (d := d) S).toLinearMap ≤
        Submodule.span F (Set.range (flattenMatrix T S).col))
    (hψ_rank :
      Module.finrank F
        (LinearMap.range
          ((productCovectorContraction (F := F) (d := cutRowFormat d S)
            iS ψ).domRestrict E)) = 2) :
    2 ≤ (contractedCutMatrix (F := F) T S iS ψ).rank := by
  classical
  let c : KTensor F (cutRowFormat d S) →ₗ[F]
      (Fin (cutRowFormat d S iS) → F) :=
    productCovectorContraction (F := F) (d := cutRowFormat d S) iS ψ
  let e := cutRowLinearEquiv (F := F) (d := d) S
  let L :
      ((∀ i : {i : Fin k // i ∈ S}, Fin (d i.val)) → F) →ₗ[F]
        (Fin (cutRowFormat d S iS) → F) :=
    c.comp e.symm.toLinearMap
  let M : Matrix (Fin (cutRowFormat d S iS))
      (∀ j : {j : Fin k // j ∉ S}, Fin (d j.val)) F :=
    contractedCutMatrix (F := F) T S iS ψ
  have hcol : ∀ col, M.col col = L ((flattenMatrix T S).col col) := by
    intro col
    ext q
    rfl
  have hmap_span :
      (Submodule.span F (Set.range (flattenMatrix T S).col)).map L ≤
        Submodule.span F (Set.range M.col) := by
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨col, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨col, hcol col⟩
  have hrange_le :
      LinearMap.range (c.domRestrict E) ≤
        Submodule.span F (Set.range M.col) := by
    rintro y ⟨x, rfl⟩
    have hxW :
        e (x : KTensor F (cutRowFormat d S)) ∈
          Submodule.span F (Set.range (flattenMatrix T S).col) :=
      hE_map_le ⟨x, x.property, rfl⟩
    have hxmap :
        L (e (x : KTensor F (cutRowFormat d S))) ∈
          (Submodule.span F (Set.range (flattenMatrix T S).col)).map L :=
      ⟨e (x : KTensor F (cutRowFormat d S)), hxW, rfl⟩
    have hxspan := hmap_span hxmap
    have hLe :
        L (e (x : KTensor F (cutRowFormat d S))) =
          c (x : KTensor F (cutRowFormat d S)) := by
      simp [L, e]
    simpa [LinearMap.domRestrict_apply, hLe] using hxspan
  rw [Matrix.rank_eq_finrank_span_cols]
  change 2 ≤ Module.finrank F (Submodule.span F (Set.range M.col))
  calc
    2 = Module.finrank F (LinearMap.range (c.domRestrict E)) := hψ_rank.symm
    _ ≤ Module.finrank F (Submodule.span F (Set.range M.col)) :=
      Submodule.finrank_mono hrange_le

/-- Format of the ordered complement block of a cut `S`, indexed by
`Fintype.equivFin {j // j ∉ S}`. -/
private noncomputable def cutComplFormat {k : ℕ} (d : Fin k → ℕ+) (S : Finset (Fin k)) :
    Fin (Fintype.card {j : Fin k // j ∉ S}) → ℕ+ :=
  fun a => d (((Fintype.equivFin {j : Fin k // j ∉ S}).symm a).val)

/-- Reindex the complement-block tensor space to the row-vector space whose
coordinates are the original `Sᶜ` multi-indices. -/
private noncomputable def cutComplLinearEquiv {k : ℕ} {d : Fin k → ℕ+}
    (S : Finset (Fin k)) :
    KTensor F (cutComplFormat d S) ≃ₗ[F]
      ((∀ j : {j : Fin k // j ∉ S}, Fin (d j.val)) → F) :=
  LinearEquiv.funCongrLeft F F
    (Equiv.piCongrLeft
      (fun j : {j : Fin k // j ∉ S} => Fin (d j.val))
      (Fintype.equivFin {j : Fin k // j ∉ S}).symm).symm

/-- Apply a product-covector contraction on the complement block to every row
of a matrix whose columns are indexed by the full `Sᶜ` block. -/
private noncomputable def rowLocalizedCutMatrix
    {k : ℕ} {d : Fin k → ℕ+} {ρ : Type*} (S : Finset (Fin k))
    (M : Matrix ρ (∀ j : {j : Fin k // j ∉ S}, Fin (d j.val)) F)
    (jC : Fin (Fintype.card {j : Fin k // j ∉ S}))
    (ψ : ∀ a : Fin (Fintype.card {j : Fin k // j ∉ S}),
      a ≠ jC → Fin (cutComplFormat d S a) → F) :
    Matrix ρ (Fin (cutComplFormat d S jC)) F :=
  fun row q =>
    productCovectorContraction (F := F) (d := cutComplFormat d S) jC ψ
      ((cutComplLinearEquiv (F := F) (d := d) S).symm (M.row row)) q

/-- Row-side analogue of `contractedCutMatrix_rank_ge_two_of_bridge`: if a
two-plane in the row span is localized injectively on the complement block,
then the resulting two-leg matrix has rank at least two. -/
private lemma rowLocalizedCutMatrix_rank_ge_two_of_bridge
    {k : ℕ} {d : Fin k → ℕ+} {ρ : Type*} [Finite ρ]
    (S : Finset (Fin k))
    (M : Matrix ρ (∀ j : {j : Fin k // j ∉ S}, Fin (d j.val)) F)
    (jC : Fin (Fintype.card {j : Fin k // j ∉ S}))
    (E : Submodule F (KTensor F (cutComplFormat d S)))
    (ψ : ∀ a : Fin (Fintype.card {j : Fin k // j ∉ S}),
      a ≠ jC → Fin (cutComplFormat d S a) → F)
    (hE_map_le :
      E.map (cutComplLinearEquiv (F := F) (d := d) S).toLinearMap ≤
        Submodule.span F (Set.range M.row))
    (hψ_rank :
      Module.finrank F
        (LinearMap.range
          ((productCovectorContraction (F := F) (d := cutComplFormat d S)
            jC ψ).domRestrict E)) = 2) :
    2 ≤ (rowLocalizedCutMatrix (F := F) (d := d) S M jC ψ).rank := by
  classical
  let c : KTensor F (cutComplFormat d S) →ₗ[F]
      (Fin (cutComplFormat d S jC) → F) :=
    productCovectorContraction (F := F) (d := cutComplFormat d S) jC ψ
  let e := cutComplLinearEquiv (F := F) (d := d) S
  let L :
      (((∀ j : {j : Fin k // j ∉ S}, Fin (d j.val)) → F) →ₗ[F]
        (Fin (cutComplFormat d S jC) → F)) :=
    c.comp e.symm.toLinearMap
  let M2 : Matrix ρ (Fin (cutComplFormat d S jC)) F :=
    rowLocalizedCutMatrix (F := F) (d := d) S M jC ψ
  have hrow : ∀ row, M2.row row = L (M.row row) := by
    intro row
    ext q
    rfl
  have hmap_span :
      (Submodule.span F (Set.range M.row)).map L ≤
        Submodule.span F (Set.range M2.row) := by
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨row, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨row, hrow row⟩
  have hrange_le :
      LinearMap.range (c.domRestrict E) ≤
        Submodule.span F (Set.range M2.row) := by
    rintro y ⟨x, rfl⟩
    have hxW :
        e (x : KTensor F (cutComplFormat d S)) ∈
          Submodule.span F (Set.range M.row) :=
      hE_map_le ⟨x, x.property, rfl⟩
    have hxmap :
        L (e (x : KTensor F (cutComplFormat d S))) ∈
          (Submodule.span F (Set.range M.row)).map L :=
      ⟨e (x : KTensor F (cutComplFormat d S)), hxW, rfl⟩
    have hxspan := hmap_span hxmap
    have hLe :
        L (e (x : KTensor F (cutComplFormat d S))) =
          c (x : KTensor F (cutComplFormat d S)) := by
      simp [L, e]
    simpa [LinearMap.domRestrict_apply, hLe] using hxspan
  rw [Matrix.rank_eq_finrank_span_row]
  change 2 ≤ Module.finrank F (Submodule.span F (Set.range M2.row))
  calc
    2 = Module.finrank F (LinearMap.range (c.domRestrict E)) := hψ_rank.symm
    _ ≤ Module.finrank F (Submodule.span F (Set.range M2.row)) :=
      Submodule.finrank_mono hrange_le

/-- A nonzero selected `2 × 2` minor can be turned into the identity by the
inverse of the minor on the left and the row/column selector matrices. -/
private lemma selected_minor_left_right_identity {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) F)
    (rowEmb : Fin 2 ↪ Fin m) (colEmb : Fin 2 ↪ Fin n)
    (hdet : (M.submatrix rowEmb colEmb).det ≠ 0) :
    let R : Matrix (Fin 2) (Fin m) F := fun a x => if x = rowEmb a then 1 else 0
    let C : Matrix (Fin 2) (Fin n) F := fun b y => if y = colEmb b then 1 else 0
    ((M.submatrix rowEmb colEmb)⁻¹ * R) * M * Cᵀ =
      (1 : Matrix (Fin 2) (Fin 2) F) := by
  classical
  intro R C
  have hRM : R * M = M.submatrix rowEmb id := by
    ext a y
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (rowEmb a)]
    · simp [R]
    · intro x _ hx
      simp [R, hx]
    · intro hx
      exact False.elim (hx (Finset.mem_univ _))
  have hRMC : R * M * Cᵀ = M.submatrix rowEmb colEmb := by
    ext a b
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (colEmb b)]
    · simp [hRM, C]
    · intro y _ hy
      simp [C, hy]
    · intro hy
      exact False.elim (hy (Finset.mem_univ _))
  calc
    ((M.submatrix rowEmb colEmb)⁻¹ * R) * M * Cᵀ
        = (M.submatrix rowEmb colEmb)⁻¹ * (R * M * Cᵀ) := by
          rw [Matrix.mul_assoc ((M.submatrix rowEmb colEmb)⁻¹) R M]
          rw [Matrix.mul_assoc ((M.submatrix rowEmb colEmb)⁻¹) (R * M) Cᵀ]
    _ = (M.submatrix rowEmb colEmb)⁻¹ * (M.submatrix rowEmb colEmb) := by
      rw [hRMC]
    _ = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)

-- The dependent-coordinate assembly uses broad simplification and `simpa using`
-- for cast bookkeeping; `simp only`/plain `simp` is fragile or too expensive here.
set_option linter.flexible false in
set_option linter.unnecessarySimpa false in
/-- Final matrix-to-restriction assembly for the crossing pair.

The hypotheses record the two-sided product-covector contractions and a
nonzero `2 × 2` minor of the resulting two-leg matrix.  The remaining work is
the explicit construction of the two inverse/selector leg matrices and the
coordinate verification that they send `T` to `unitPairTensor 2 i j`. -/
private lemma restricts_of_crossing_2x2_minor
    {k : ℕ} {d : Fin k → ℕ+} (T : KTensor F d) (S : Finset (Fin k))
    (i : Fin k) (hiS : i ∈ S) (iS : Fin S.card)
    (hiS_eq : (S.orderIsoOfFin rfl iS).val = i)
    (ψS : ∀ a : Fin S.card, a ≠ iS → Fin (cutRowFormat d S a) → F)
    (jC : Fin (Fintype.card {j : Fin k // j ∉ S}))
    (ψSc : ∀ a : Fin (Fintype.card {j : Fin k // j ∉ S}),
      a ≠ jC → Fin (cutComplFormat d S a) → F)
    (rowEmb : Fin 2 ↪ Fin (cutRowFormat d S iS))
    (colEmb : Fin 2 ↪ Fin (cutComplFormat d S jC))
    (j : Fin k) (hjS : j ∉ S) (hij : i ≠ j)
    (hj_eq : j = ((Fintype.equivFin {j : Fin k // j ∉ S}).symm jC).val)
    (hdet :
      ((rowLocalizedCutMatrix (F := F) (d := d) S
        (contractedCutMatrix (F := F) T S iS ψS) jC ψSc).submatrix
          rowEmb colEmb).det ≠ 0) :
    Restricts (unitPairTensor (F := F) (2 : ℕ+) i j hij) T := by
  classical
  let M2 : Matrix (Fin (cutRowFormat d S iS)) (Fin (cutComplFormat d S jC)) F :=
    rowLocalizedCutMatrix (F := F) (d := d) S
      (contractedCutMatrix (F := F) T S iS ψS) jC ψSc
  let R : Matrix (Fin 2) (Fin (cutRowFormat d S iS)) F :=
    fun a x => if x = rowEmb a then 1 else 0
  let C : Matrix (Fin 2) (Fin (cutComplFormat d S jC)) F :=
    fun b y => if y = colEmb b then 1 else 0
  let Ai : Matrix (Fin 2) (Fin (cutRowFormat d S iS)) F :=
    (M2.submatrix rowEmb colEmb)⁻¹ * R
  let Aj : Matrix (Fin 2) (Fin (cutComplFormat d S jC)) F := C
  have hminor_id :
      Ai * M2 * Ajᵀ = (1 : Matrix (Fin 2) (Fin 2) F) := by
    simpa [Ai, Aj, R, C, M2] using
      selected_minor_left_right_identity (F := F) M2 rowEmb colEmb (by
        simpa [M2] using hdet)
  let A : ∀ a : Fin k, Matrix (Fin (naturalPairFormat (2 : ℕ+) i j a)) (Fin (d a)) F :=
    fun a => by
      by_cases hai : a = i
      · subst hai
        exact fun p x =>
          Ai (Fin.cast (by simp [naturalPairFormat]) p)
            (Fin.cast (by rw [cutRowFormat, hiS_eq]) x)
      · by_cases haj : a = j
        · subst haj
          exact fun p x =>
            Aj (Fin.cast (by simp [naturalPairFormat]) p)
              (Fin.cast (by rw [cutComplFormat, ← hj_eq]) x)
        · by_cases haS : a ∈ S
          · let aS : Fin S.card := (S.orderIsoOfFin rfl).symm ⟨a, haS⟩
            have haS_ne : aS ≠ iS := by
              intro h
              apply hai
              have hval :
                  ((S.orderIsoOfFin rfl aS).val) =
                    ((S.orderIsoOfFin rfl iS).val) := by
                rw [h]
              simpa [aS, hiS_eq] using hval
            have haS_val : ((S.orderIsoOfFin rfl aS).val) = a := by
              simp [aS]
            exact fun _ x =>
              ψS aS haS_ne (Fin.cast (by rw [cutRowFormat, haS_val]) x)
          · let aC : Fin (Fintype.card {j : Fin k // j ∉ S}) :=
              (Fintype.equivFin {j : Fin k // j ∉ S}) ⟨a, haS⟩
            have haC_ne : aC ≠ jC := by
              intro h
              apply haj
              have hval :
                  ((Fintype.equivFin {j : Fin k // j ∉ S}).symm aC).val =
                    ((Fintype.equivFin {j : Fin k // j ∉ S}).symm jC).val := by
                rw [h]
              simpa [aC, hj_eq] using hval
            have haC_val :
                ((Fintype.equivFin {j : Fin k // j ∉ S}).symm aC).val = a := by
              simp [aC]
            exact fun _ x =>
              ψSc aC haC_ne (Fin.cast (by rw [cutComplFormat, haC_val]) x)
  refine ⟨A, ?_⟩
  intro jdx
  let p : Fin 2 := Fin.cast (by simp [naturalPairFormat]) (jdx i)
  let q : Fin 2 := Fin.cast (by simp [naturalPairFormat]) (jdx j)
  let rowSub :
      (∀ a : Fin S.card, Fin (cutRowFormat d S a)) →
        (∀ x : {x : Fin k // x ∈ S}, Fin (d x.val)) :=
    fun row =>
      (Equiv.piCongrLeft
        (fun x : {x : Fin k // x ∈ S} => Fin (d x.val))
        (S.orderIsoOfFin rfl).toEquiv) row
  let colSub :
      (∀ a : Fin (Fintype.card {x : Fin k // x ∉ S}), Fin (cutComplFormat d S a)) →
        (∀ x : {x : Fin k // x ∉ S}, Fin (d x.val)) :=
    fun col =>
      (Equiv.piCongrLeft
        (fun x : {x : Fin k // x ∉ S} => Fin (d x.val))
        (Fintype.equivFin {x : Fin k // x ∉ S}).symm) col
  let assemble
      (row : ∀ a : Fin S.card, Fin (cutRowFormat d S a))
      (col : ∀ a : Fin (Fintype.card {x : Fin k // x ∉ S}), Fin (cutComplFormat d S a)) :
      ∀ a : Fin k, Fin (d a) :=
    fun a => if h : a ∈ S then rowSub row ⟨a, h⟩ else colSub col ⟨a, h⟩
  have hsum :
      (∑ idx : (∀ a : Fin k, Fin (d a)),
          (∏ a : Fin k, A a (jdx a) (idx a)) * T idx) =
        (Ai * M2 * Ajᵀ) p q := by
    symm
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply]
    change
      (∑ x : Fin (cutComplFormat d S jC),
        (∑ y : Fin (cutRowFormat d S iS),
          Ai p y *
            rowLocalizedCutMatrix (F := F) (d := d) S
              (contractedCutMatrix (F := F) T S iS ψS) jC ψSc y x) *
          Ajᵀ x q) =
        ∑ idx : (∀ a : Fin k, Fin (d a)),
          (∏ a : Fin k, A a (jdx a) (idx a)) * T idx
    unfold rowLocalizedCutMatrix contractedCutMatrix productCovectorContraction
    dsimp
    simp [cutComplLinearEquiv, cutRowLinearEquiv, flattenMatrix, Matrix.row]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      intro x
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      intro y
      arg 2
      intro x
      rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      intro y
      rw [Finset.sum_comm]
    change
      (∑ y : (∀ a : Fin (Fintype.card {x : Fin k // x ∉ S}), Fin (cutComplFormat d S a)),
        ∑ y₁ : (∀ a : Fin S.card, Fin (cutRowFormat d S a)),
          ∑ x : Fin (cutRowFormat d S iS),
            ∑ x₁ : Fin (cutComplFormat d S jC),
              Ai p x *
                  (productCovectorWeight (F := F) jC ψSc x₁ y *
                    (productCovectorWeight (F := F) iS ψS x y₁ *
                      T (assemble y₁ y))) *
                Aj q x₁) =
        ∑ idx : (∀ a : Fin k, Fin (d a)),
          (∏ a : Fin k, A a (jdx a) (idx a)) * T idx
    simp_rw [double_productCovectorWeight_sum (F := F) iS ψS jC ψSc
      (fun x => Ai p x) (fun x => Aj q x)]
    rw [Finset.sum_comm]
    let eRow :
        ((a : Fin S.card) → Fin (cutRowFormat d S a)) ≃
          ((x : {x : Fin k // x ∈ S}) → Fin (d x.val)) :=
      Equiv.piCongrLeft
        (fun x : {x : Fin k // x ∈ S} => Fin (d x.val))
        (S.orderIsoOfFin rfl).toEquiv
    let eCol :
        ((a : Fin (Fintype.card {x : Fin k // x ∉ S})) → Fin (cutComplFormat d S a)) ≃
          ((x : {x : Fin k // x ∉ S}) → Fin (d x.val)) :=
      Equiv.piCongrLeft
        (fun x : {x : Fin k // x ∉ S} => Fin (d x.val))
        (Fintype.equivFin {x : Fin k // x ∉ S}).symm
    let splitFin :
        (∀ a : Fin k, Fin (d a)) ≃
          (((a : Fin S.card) → Fin (cutRowFormat d S a)) ×
            ((a : Fin (Fintype.card {x : Fin k // x ∉ S})) → Fin (cutComplFormat d S a))) :=
      (Equiv.piEquivPiSubtypeProd (· ∈ S) (fun a : Fin k => Fin (d a))).trans
        (Equiv.prodCongr eRow.symm eCol.symm)
    rw [← Equiv.sum_comp splitFin.symm
      (fun idx : (∀ a : Fin k, Fin (d a)) =>
        (∏ a : Fin k, A a (jdx a) (idx a)) * T idx)]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl ?_
    intro row _
    refine Finset.sum_congr rfl ?_
    intro col _
    have hsplit_apply : splitFin.symm (row, col) = assemble row col := by
      funext a
      by_cases ha : a ∈ S
      · simp [splitFin, assemble, rowSub, colSub, eRow, eCol, ha,
          Equiv.piEquivPiSubtypeProd_symm_apply]
        congr
      · simp [splitFin, assemble, rowSub, colSub, eRow, eCol, ha,
          Equiv.piEquivPiSubtypeProd_symm_apply]
        congr
    rw [hsplit_apply]
    have hproduct_assembly :
        (∏ a : Fin k, A a (jdx a) (assemble row col a)) =
          ((∏ a : Fin (Fintype.card {x : Fin k // x ∉ S}),
              if h : a = jC then (1 : F) else ψSc a h (col a)) *
              Aj q (col jC)) *
            (Ai p (row iS) *
              ∏ a : Fin S.card,
                if h : a = iS then (1 : F) else ψS a h (row a)) := by
      -- Coordinate assembly: split the full leg product into the
      -- ordered `S` and `Sᶜ` block products and evaluate the four cases of `A`.
      let f : Fin k → F := fun a => A a (jdx a) (assemble row col a)
      let eBlock :
          (Fin S.card ⊕ Fin (Fintype.card {x : Fin k // x ∉ S})) ≃ Fin k :=
        (Equiv.sumCongr (S.orderIsoOfFin rfl).toEquiv
          (Fintype.equivFin {x : Fin k // x ∉ S}).symm).trans
          (Equiv.sumCompl (fun x : Fin k => x ∈ S))
      have hrowSub_apply (a : Fin S.card) :
          rowSub row (S.orderIsoOfFin rfl a) = row a := by
        simpa [rowSub] using
          (Equiv.piCongrLeft_apply_apply
            (P := fun x : {x : Fin k // x ∈ S} => Fin (d x.val))
            ((S.orderIsoOfFin rfl).toEquiv) row a)
      have hcolSub_apply (a : Fin (Fintype.card {x : Fin k // x ∉ S})) :
          colSub col ((Fintype.equivFin {x : Fin k // x ∉ S}).symm a) =
            col a := by
        simpa [colSub] using
          (Equiv.piCongrLeft_apply_apply
            (P := fun x : {x : Fin k // x ∉ S} => Fin (d x.val))
            (Fintype.equivFin {x : Fin k // x ∉ S}).symm col a)
      have hassemble_row (a : Fin S.card) :
          assemble row col ((S.orderIsoOfFin rfl a).val) = row a := by
        simpa [assemble] using hrowSub_apply a
      have hassemble_col (a : Fin (Fintype.card {x : Fin k // x ∉ S})) :
          assemble row col (((Fintype.equivFin {x : Fin k // x ∉ S}).symm a).val) =
            col a := by
        have hnot :
            (((Fintype.equivFin {x : Fin k // x ∉ S}).symm a).val) ∉ S :=
          ((Fintype.equivFin {x : Fin k // x ∉ S}).symm a).property
        simpa [assemble, hnot] using hcolSub_apply a
      have hS_index
          (a : Fin S.card) (hmem : S.orderEmbOfFin rfl a ∈ S) :
          (S.orderIsoOfFin rfl).symm ⟨S.orderEmbOfFin rfl a, hmem⟩ = a := by
        apply (S.orderIsoOfFin rfl).injective
        ext
        simp [Finset.coe_orderIsoOfFin_apply]
      have hC_index (a : Fin (Fintype.card {x : Fin k // x ∉ S}))
          (hnot : (((Fintype.equivFin {x : Fin k // x ∉ S}).symm a :
            {x : Fin k // x ∉ S}) : Fin k) ∉ S) :
          (Fintype.equivFin {x : Fin k // x ∉ S})
              ⟨(((Fintype.equivFin {x : Fin k // x ∉ S}).symm a :
                {x : Fin k // x ∉ S}) : Fin k), hnot⟩ = a := by
        have hsub :
            (⟨(((Fintype.equivFin {x : Fin k // x ∉ S}).symm a :
                {x : Fin k // x ∉ S}) : Fin k), hnot⟩ :
              {x : Fin k // x ∉ S}) =
              (Fintype.equivFin {x : Fin k // x ∉ S}).symm a := by
          ext
          rfl
        simpa [hsub]
      have hS_eval :
          ∀ a : Fin S.card,
            f (eBlock (Sum.inl a)) =
              if h : a = iS then Ai p (row iS) else ψS a h (row a) := by
        intro a
        by_cases ha : a = iS
        · subst a
          subst i
          simp [f, eBlock, A, p, Finset.coe_orderIsoOfFin_apply]
          have hrow_emb :
              assemble row col (S.orderEmbOfFin rfl iS) = row iS := by
            simpa [Finset.coe_orderIsoOfFin_apply] using hassemble_row iS
          rw [hrow_emb]
        · have hleg_ne_i : S.orderEmbOfFin rfl a ≠ i := by
            intro h
            apply ha
            apply (S.orderIsoOfFin rfl).injective
            exact Subtype.ext (by simpa [hiS_eq] using h)
          have hleg_ne_j : S.orderEmbOfFin rfl a ≠ j := by
            intro h
            exact hjS (h ▸ Finset.orderEmbOfFin_mem S rfl a)
          simp [f, eBlock, A, Finset.coe_orderIsoOfFin_apply, hleg_ne_i,
            hleg_ne_j, ha]
          have hrow_emb :
              assemble row col (S.orderEmbOfFin rfl a) = row a := by
            simpa [Finset.coe_orderIsoOfFin_apply] using hassemble_row a
          convert (rfl : ψS a ha (row a) = ψS a ha (row a)) using 2
          · exact hS_index a _
          · simpa [Fin.cast_eq_cast, hrow_emb] using
              (cast_heq_iff_heq _ (row a) (row a)).mpr HEq.rfl
      have hC_eval :
          ∀ a : Fin (Fintype.card {x : Fin k // x ∉ S}),
            f (eBlock (Sum.inr a)) =
              if h : a = jC then Aj q (col jC) else ψSc a h (col a) := by
        intro a
        by_cases ha : a = jC
        · subst a
          subst j
          have hleg_ne_i :
              (((Fintype.equivFin {x : Fin k // x ∉ S}).symm jC :
                  {x : Fin k // x ∉ S}) : Fin k) ≠ i := by
            exact hij.symm
          simp [f, eBlock, A, q, hassemble_col, hleg_ne_i]
        · have hleg_not_mem :
              (((Fintype.equivFin {x : Fin k // x ∉ S}).symm a :
                  {x : Fin k // x ∉ S}) : Fin k) ∉ S :=
            ((Fintype.equivFin {x : Fin k // x ∉ S}).symm a).property
          have hleg_ne_i :
              (((Fintype.equivFin {x : Fin k // x ∉ S}).symm a :
                  {x : Fin k // x ∉ S}) : Fin k) ≠ i := by
            intro h
            exact hleg_not_mem (h ▸ hiS)
          have hleg_ne_j :
              (((Fintype.equivFin {x : Fin k // x ∉ S}).symm a :
                  {x : Fin k // x ∉ S}) : Fin k) ≠ j := by
            intro h
            apply ha
            apply (Fintype.equivFin {x : Fin k // x ∉ S}).symm.injective
            exact Subtype.ext (by simpa [hj_eq] using h)
          simp [f, eBlock, A, hleg_ne_i, hleg_ne_j, hleg_not_mem, ha,
            hassemble_col]
          convert (rfl : ψSc a ha (col a) = ψSc a ha (col a)) using 2
          · exact hC_index a hleg_not_mem
          · simpa [Fin.cast_eq_cast] using
              (cast_heq_iff_heq _ (col a) (col a)).mpr HEq.rfl
      have hS_prod :
          (∏ a : Fin S.card, f (eBlock (Sum.inl a))) =
            Ai p (row iS) *
              ∏ a : Fin S.card,
                if h : a = iS then (1 : F) else ψS a h (row a) := by
        rw [show
          (∏ a : Fin S.card, f (eBlock (Sum.inl a))) =
            ∏ a : Fin S.card,
              if h : a = iS then Ai p (row iS) else ψS a h (row a) by
          exact Finset.prod_congr rfl (by intro a _; exact hS_eval a)]
        exact prod_dite_special_eq_mul (F := F) iS (Ai p (row iS))
          (fun a h => ψS a h (row a))
      have hC_prod :
          (∏ a : Fin (Fintype.card {x : Fin k // x ∉ S}), f (eBlock (Sum.inr a))) =
            (∏ a : Fin (Fintype.card {x : Fin k // x ∉ S}),
              if h : a = jC then (1 : F) else ψSc a h (col a)) *
              Aj q (col jC) := by
        rw [show
          (∏ a : Fin (Fintype.card {x : Fin k // x ∉ S}), f (eBlock (Sum.inr a))) =
            ∏ a : Fin (Fintype.card {x : Fin k // x ∉ S}),
              if h : a = jC then Aj q (col jC) else ψSc a h (col a) by
          exact Finset.prod_congr rfl (by intro a _; exact hC_eval a)]
        rw [prod_dite_special_eq_mul (F := F) jC (Aj q (col jC))
          (fun a h => ψSc a h (col a))]
        ring
      calc
        (∏ a : Fin k, A a (jdx a) (assemble row col a))
            = ∏ a : Fin S.card ⊕ Fin (Fintype.card {x : Fin k // x ∉ S}),
                f (eBlock a) := by
              exact (Equiv.prod_comp eBlock f).symm
        _ = (∏ a : Fin S.card, f (eBlock (Sum.inl a))) *
              ∏ a : Fin (Fintype.card {x : Fin k // x ∉ S}), f (eBlock (Sum.inr a)) := by
              exact Fintype.prod_sum_type (fun a => f (eBlock a))
        _ = (Ai p (row iS) *
              ∏ a : Fin S.card,
                if h : a = iS then (1 : F) else ψS a h (row a)) *
              ((∏ a : Fin (Fintype.card {x : Fin k // x ∉ S}),
                if h : a = jC then (1 : F) else ψSc a h (col a)) *
                Aj q (col jC)) := by
              rw [hS_prod, hC_prod]
        _ = ((∏ a : Fin (Fintype.card {x : Fin k // x ∉ S}),
              if h : a = jC then (1 : F) else ψSc a h (col a)) *
              Aj q (col jC)) *
            (Ai p (row iS) *
              ∏ a : Fin S.card,
                if h : a = iS then (1 : F) else ψS a h (row a)) := by
              ring
    rw [hproduct_assembly]
    ring
  rw [unitPairTensor, hsum, hminor_id, Matrix.one_apply]
  by_cases hpq : p = q
  · rw [if_pos hpq, if_pos]
    have hpq_val := congrArg Fin.val hpq
    simpa [p, q] using hpq_val
  · rw [if_neg hpq, if_neg]
    intro hval
    apply hpq
    apply Fin.ext
    simpa [p, q] using hval

/-- Crossing-pair assembly after the S-side bridge has been converted into
a concrete rank-`≥ 2` contracted flattening matrix.

Proof: view `contractedCutMatrix T S iS ψS` as the flattening of the
tensor obtained by contracting the `S \ {i}` legs, apply
`exists_leg_in_S_with_cut_image_product_covector_localization` to the complement
side, extract a rank-`2` two-leg matrix minor, and build the final
`Restricts (unitPairTensor 2 i j) T` leg matrices. -/
private theorem restricts_unitPair_of_contractedCutMatrix_rank_ge_two
    {k : ℕ} {d : Fin k → ℕ+} (T : KTensor F d) (S : Finset (Fin k))
    (i : Fin k) (hiS : i ∈ S) (iS : Fin S.card)
    (hiS_eq : (S.orderIsoOfFin rfl iS).val = i)
    (ψS : ∀ a : Fin S.card, a ≠ iS → Fin (cutRowFormat d S a) → F)
    (hM_rank : 2 ≤ (contractedCutMatrix (F := F) T S iS ψS).rank) :
    ∃ j ∉ S, ∃ hij : i ≠ j,
      Restricts (unitPairTensor (F := F) (2 : ℕ+) i j hij) T := by
  classical
  let M : Matrix (Fin (cutRowFormat d S iS))
      (∀ j : {j : Fin k // j ∉ S}, Fin (d j.val)) F :=
    contractedCutMatrix (F := F) T S iS ψS
  have hM_rank' : 2 ≤ M.rank := by
    simpa [M] using hM_rank
  let W : Submodule F
      (((∀ j : {j : Fin k // j ∉ S}, Fin (d j.val)) → F)) :=
    Submodule.span F (Set.range M.row)
  have hW : 2 ≤ Module.finrank F W := by
    rw [Matrix.rank_eq_finrank_span_row] at hM_rank'
    simpa [W] using hM_rank'
  obtain ⟨Erow, hErow_le, hErow_dim⟩ :=
    exists_submodule_le_finrank_eq_two (F := F) hW
  have hC_nonempty : Nonempty {j : Fin k // j ∉ S} := by
    by_contra hne
    haveI : IsEmpty {j : Fin k // j ∉ S} := not_nonempty_iff.mp hne
    have hwidth :
        M.rank ≤
          Fintype.card (∀ j : {j : Fin k // j ∉ S}, Fin (d j.val)) :=
      Matrix.rank_le_card_width M
    have hcard :
        Fintype.card (∀ j : {j : Fin k // j ∉ S}, Fin (d j.val)) = 1 := by
      simp
    have : M.rank ≤ 1 := by
      simpa [hcard] using hwidth
    omega
  have hC_card_pos : 0 < Fintype.card {j : Fin k // j ∉ S} :=
    Fintype.card_pos_iff.mpr hC_nonempty
  let e := cutComplLinearEquiv (F := F) (d := d) S
  let m : Erow →ₗ[F] KTensor F (cutComplFormat d S) :=
    e.symm.toLinearMap.domRestrict Erow
  let E : Submodule F (KTensor F (cutComplFormat d S)) :=
    LinearMap.range m
  have hm_inj : Function.Injective m := by
    intro x y hxy
    apply Subtype.ext
    exact e.symm.injective hxy
  have hE_dim : Module.finrank F E = 2 := by
    exact (LinearMap.finrank_range_of_inj hm_inj).trans hErow_dim
  have hErow_eq_map : E.map e.toLinearMap = Erow := by
    apply le_antisymm
    · rintro x ⟨y, hyE, rfl⟩
      rcases hyE with ⟨z, rfl⟩
      simp [m, e, z.property]
    · intro x hx
      refine ⟨e.symm x, ?_, ?_⟩
      · exact ⟨⟨x, hx⟩, rfl⟩
      · simp [e]
  have hE_map_le :
      E.map e.toLinearMap ≤
        Submodule.span F (Set.range M.row) := by
    rw [hErow_eq_map]
    exact hErow_le
  obtain ⟨jC, ψSc, hψSc_inj⟩ :=
    exists_product_covector_localization_anyField
      (F := F) hC_card_pos E hE_dim
  have hψSc_rank :
      Module.finrank F
        (LinearMap.range
          ((productCovectorContraction (F := F) (d := cutComplFormat d S)
            jC ψSc).domRestrict E)) = 2 := by
    exact (LinearMap.finrank_range_of_inj hψSc_inj).trans hE_dim
  let M2 : Matrix (Fin (cutRowFormat d S iS))
      (Fin (cutComplFormat d S jC)) F :=
    rowLocalizedCutMatrix (F := F) (d := d) S M jC ψSc
  have hM2_rank : 2 ≤ M2.rank := by
    simpa [M2] using
      rowLocalizedCutMatrix_rank_ge_two_of_bridge
        (F := F) (d := d) S M jC E ψSc hE_map_le hψSc_rank
  obtain ⟨rowEmb, colEmb, hdet⟩ :=
    Matrix.exists_submatrix_det_ne_zero_of_le_rank M2 1 (by simpa using hM2_rank)
  let j : Fin k := ((Fintype.equivFin {j : Fin k // j ∉ S}).symm jC).val
  have hjS : j ∉ S :=
    ((Fintype.equivFin {j : Fin k // j ∉ S}).symm jC).property
  have hij : i ≠ j := by
    intro h
    exact hjS (h ▸ hiS)
  refine ⟨j, hjS, hij, ?_⟩
  exact restricts_of_crossing_2x2_minor
    (F := F) T S i hiS iS hiS_eq ψS jC ψSc rowEmb colEmb
    j hjS hij rfl (by simpa [M2, M] using hdet)

/-- A focused subset application of PL.

From `flatRank T S ≥ 2`, the column space of the `S`-flattening contains a
two-dimensional subspace.  Reindex that subspace as a tensor on the ordered
`S`-legs and apply product-covector localization there.  The resulting local
leg `iS : Fin S.card` corresponds to an original leg `i ∈ S`, and the
localized contraction is injective on the chosen two-plane.

This is the reusable PL-on-one-side bridge; it deliberately stops before the
separate rank-preservation step that assembles the contracted full tensor with
the complementary spectator legs. -/
theorem exists_leg_in_S_with_cut_image_product_covector_localization
    {k : ℕ} {d : Fin k → ℕ+} (T : KTensor F d) (S : Finset (Fin k))
    (hS : S.Nonempty) (h2 : 2 ≤ flatRank T S) :
    ∃ i : Fin k, i ∈ S ∧ ∃ iS : Fin S.card,
      (S.orderIsoOfFin rfl iS).val = i ∧
      ∃ E : Submodule F (KTensor F (cutRowFormat d S)),
        Module.finrank F E = 2 ∧
        E.map (cutRowLinearEquiv (F := F) (d := d) S).toLinearMap ≤
          Submodule.span F (Set.range (flattenMatrix T S).col) ∧
        ∃ ψ : ∀ a : Fin S.card, a ≠ iS → Fin (cutRowFormat d S a) → F,
          Function.Injective
            ((productCovectorContraction (F := F) (d := cutRowFormat d S)
              iS ψ).domRestrict E) ∧
          Module.finrank F
            (LinearMap.range
              ((productCovectorContraction (F := F) (d := cutRowFormat d S)
                iS ψ).domRestrict E)) = 2 := by
  classical
  let W : Submodule F ((∀ i : {i : Fin k // i ∈ S}, Fin (d i.val)) → F) :=
    Submodule.span F (Set.range (flattenMatrix T S).col)
  have hW : 2 ≤ Module.finrank F W := by
    rw [flatRank, Matrix.rank_eq_finrank_span_cols] at h2
    simpa [W] using h2
  obtain ⟨Erow, hErow_le, hErow_dim⟩ :=
    exists_submodule_le_finrank_eq_two (F := F) hW
  let e := cutRowLinearEquiv (F := F) (d := d) S
  let m : Erow →ₗ[F] KTensor F (cutRowFormat d S) :=
    e.symm.toLinearMap.domRestrict Erow
  let E : Submodule F (KTensor F (cutRowFormat d S)) :=
    LinearMap.range m
  have hm_inj : Function.Injective m := by
    intro x y hxy
    apply Subtype.ext
    exact e.symm.injective hxy
  have hE_dim : Module.finrank F E = 2 := by
    exact (LinearMap.finrank_range_of_inj hm_inj).trans hErow_dim
  have hErow_eq_map : E.map e.toLinearMap = Erow := by
    apply le_antisymm
    · rintro x ⟨y, hyE, rfl⟩
      rcases hyE with ⟨z, rfl⟩
      simp [m, e, z.property]
    · intro x hx
      refine ⟨e.symm x, ?_, ?_⟩
      · exact ⟨⟨x, hx⟩, rfl⟩
      · simp [e]
  have hE_map_le :
      E.map e.toLinearMap ≤
        Submodule.span F (Set.range (flattenMatrix T S).col) := by
    rw [hErow_eq_map]
    exact hErow_le
  have hS_card_pos : 0 < S.card := Finset.card_pos.mpr hS
  obtain ⟨iS, ψ, hψ⟩ :=
    exists_product_covector_localization_anyField
      (F := F) hS_card_pos E hE_dim
  refine ⟨(S.orderIsoOfFin rfl iS).val,
    (S.orderIsoOfFin rfl iS).property, iS, rfl, E, hE_dim, hE_map_le,
    ψ, hψ, ?_⟩
  exact (LinearMap.finrank_range_of_inj hψ).trans hE_dim

/-- Crossing-pair bridge.

The field-general assembly:
apply product-covector localization on the two sides of the cut, obtain a
rank-`≥ 2` crossing two-leg contraction, then extract an invertible `2 × 2`
minor and assemble the leg matrices witnessing the rank-2 pair-unit
restriction. -/
private theorem exists_unitPairTensor_two_restricts_of_flatRank_cut_ge_two_aux
    {k : ℕ} (_hk : 2 ≤ k) {d : Fin k → ℕ+} (T : KTensor F d) (S : Finset (Fin k))
    (hS : S.Nonempty) (_hS' : S ≠ Finset.univ) (h2 : 2 ≤ flatRank T S) :
    ∃ i ∈ S, ∃ j ∉ S, ∃ hij : i ≠ j,
      Restricts (unitPairTensor (F := F) (2 : ℕ+) i j hij) T := by
  classical
  obtain ⟨i, hiS, iS, hiS_eq, E, hE_dim, hE_map_le,
      ψS, hψS_inj, hψS_rank⟩ :=
    exists_leg_in_S_with_cut_image_product_covector_localization
      (F := F) T S hS h2
  have hpost_bridge :
      ∃ j ∉ S, ∃ hij : i ≠ j,
        Restricts (unitPairTensor (F := F) (2 : ℕ+) i j hij) T := by
    have hS_contracted_rank :
        2 ≤ (contractedCutMatrix (F := F) T S iS ψS).rank :=
      contractedCutMatrix_rank_ge_two_of_bridge
        (F := F) T S iS E ψS hE_map_le hψS_rank
    exact restricts_unitPair_of_contractedCutMatrix_rank_ge_two
      (F := F) T S i hiS iS hiS_eq ψS hS_contracted_rank
  obtain ⟨j, hjS, hij, hres⟩ := hpost_bridge
  exact ⟨i, hiS, j, hjS, hij, hres⟩

/-!
The localization and restriction assembly is isolated in the theorem below.
Its statement is the crossing-pair extraction; the proof proceeds in three
steps:

* product-covector localization (PL) localizes a two-dimensional cut image by
  product covectors on one side;
* applying this on both sides of the cut yields a rank-`≥ 2` matrix on a
  crossing pair of legs;
* extracting an invertible `2 × 2` minor assembles the corresponding
  `Restricts (unitPairTensor 2 i j) T` witness.
-/

/-- Crossing-pair bridge: a rank-`≥ 2` nontrivial cut yields a crossing rank-2 pair-unit
restriction.  This is the remaining formal assembly from product-covector
localization on both sides of the cut plus the final `Restricts` matrices. -/
theorem exists_unitPairTensor_two_restricts_of_flatRank_cut_ge_two_anyField
    {k : ℕ} (hk : 2 ≤ k) {d : Fin k → ℕ+} (T : KTensor F d) (S : Finset (Fin k))
    (hS : S.Nonempty) (hS' : S ≠ Finset.univ) (h2 : 2 ≤ flatRank T S) :
    ∃ i ∈ S, ∃ j ∉ S, ∃ hij : i ≠ j,
      Restricts (unitPairTensor (F := F) (2 : ℕ+) i j hij) T := by
  exact exists_unitPairTensor_two_restricts_of_flatRank_cut_ge_two_aux
    (F := F) hk T S hS hS' h2

/-- Field-general crossing-pair extraction: if a nontrivial cut has flattening
rank at least two, some crossing pair has pair-subrank at least two. -/
theorem exists_crossing_pair_of_flatRank_cut_ge_two_anyField
    {k : ℕ} (hk : 2 ≤ k) {d : Fin k → ℕ+} (T : KTensor F d) (S : Finset (Fin k))
    (hS : S.Nonempty) (hS' : S ≠ Finset.univ) (h2 : 2 ≤ flatRank T S) :
    ∃ i ∈ S, ∃ j ∉ S, ∃ _hij : i ≠ j, 2 ≤ subrankPair T i j := by
  classical
  obtain ⟨i, hiS, j, hjS, hij, hres⟩ :=
    exists_unitPairTensor_two_restricts_of_flatRank_cut_ge_two_anyField
      (F := F) hk T S hS hS' h2
  exact ⟨i, hiS, j, hjS, hij,
    subrankPair_ge_two_of_unitPairTensor_two_restricts T i j hij hres⟩

end Semicontinuity
