/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.Order.BourbakiWitt
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# LSS — the recursive orthogonal-projection retraction `O_G`

This file builds the core recursive orthogonal-projection retraction shared by both
the `GOR⁺_σ` construction (Gortler–Theran) and the `O_G` ℚ-descent (Vrana–Christandl).

## Sources (verbatim)

* Gortler–Theran, arXiv:2310.11565,
  `the Gortler-Theran GOR proof notes`:
  - tex:119-121 — definition of an orthogonal representation (OR): "if `i ≠ j` is not an
    edge of `G`, then `v_i ⊥ v_j`".
  - tex:175-187 — the inductive construction: "Find the non-neighbors `i_1 < … < i_k < i`
    of `i` that come before it. If the vectors `v_{i_1}, …, v_{i_k}` are linearly
    independent, place `v_i` anywhere in the `(D-k)`-dimensional subspace orthogonal to
    their span. Otherwise, set `v_i = 0`. This construction always produces an OR of `G`."

* Vrana–Christandl, arXiv:1603.03964,
  `the Vrana-Christandl genmamu reference notes`:
  - tex:201 — the `O_G` map: "`(O_G f)(v_1) = f(v_1)`. If `i > 1`, we let
    `A_i = {v_j | j < i and {v_i, v_j} ∉ E}`. Let `P_i` denote the orthogonal projection
    onto the subspace spanned by `{(O_G f)(v) | v ∈ A_i}`. Then we set
    `(O_G f)(v_i) = (I − P_i) f(v_i)`."
  - tex:203 — "`O_G f` is an orthogonal representation for any `f`, and if `f` is an
    orthogonal representation, then `O_G f = f`."
  - tex:205-213 — explicit Gram–Schmidt form of `P_i`, with rational coefficients
    `⟨g_m, x⟩ / ⟨g_m, g_m⟩`, hence `f : V → ℚ^d ⟹ O_G f : V → ℚ^d`.

## Discrepancy: gorProof "v_i = 0 if dependent" vs. genmamu projection `O_G`

gorProof tex:180-184 *zeros out* `v_i` when the preceding non-neighbors are linearly
**dependent**; genmamu tex:201 instead uses `(I − P_i) f(v_i)`, the orthogonal-complement
component, which is generically **nonzero** even in the dependent case. These two recipes
genuinely differ. **We follow genmamu's projection `O_G`** (as the task and the ℚ-descent
require): `P_i` is the orthogonal projection onto the *span* of the already-retracted
preceding non-neighbors, and dependence is handled automatically because the span is the
same set whether or not its generators are independent. The output `(I − P_i) f(v_i)` is
*always* orthogonal to every preceding non-neighbor, which is exactly what makes
`orthoRetract_isOR` hold unconditionally. We do **not** zero out.

## Main declarations

* `IsOR G v` — `v` is an orthogonal representation of `G` (gorProof:119-121).
* `precNonNbr G i` — the preceding non-neighbors of `i` (genmamu `A_i`, tex:201).
* `orthoRetract G f` — the `O_G` map (genmamu tex:201), by strong recursion on `i.val`.
* `orthoRetract_isOR` — `orthoRetract G f` is always an OR (genmamu tex:203).
* `orthoRetract_eq_self_of_isOR` — fixes ORs (genmamu tex:203, gorProof:130-131 analogue).
* `orthoRetract_rational` — preserves rationality (genmamu tex:205-213).
-/

open scoped InnerProductSpace
open RealInnerProductSpace

namespace LSS

variable {n D : ℕ}

/-- **Orthogonal representation (OR)** of a graph `G` in `ℝ^D`
(Gortler–Theran gorProof tex:119-121): an assignment `v : Fin n → ℝ^D` such that any two
distinct non-adjacent vertices are mapped to orthogonal vectors.

> "An orthogonal representation (OR) of `G` in `ℝ^D` is an assignment to each vertex `i` a
>  vector `v_i` in `ℝ^D` so that if `i ≠ j` is not an edge of `G`, then `v_i ⊥ v_j`."
-/
def IsOR (G : SimpleGraph (Fin n)) (v : Fin n → EuclideanSpace ℝ (Fin D)) : Prop :=
  ∀ i j : Fin n, i ≠ j → ¬ G.Adj i j → ⟪v i, v j⟫_ℝ = 0

/-- The **preceding non-neighbors** of vertex `i` (Vrana–Christandl `A_i`, genmamu tex:201):
the vertices `j` with `j < i` (in the fixed ordering `Fin n`) that are *not* neighbors of `i`.

> "`A_i = {v_j | j < i and {v_i, v_j} ∉ E}`."
-/
def precNonNbr (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j.val < i.val ∧ ¬ G.Adj i j)

@[simp]
theorem mem_precNonNbr {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {i j : Fin n} :
    j ∈ precNonNbr G i ↔ j.val < i.val ∧ ¬ G.Adj i j := by
  simp [precNonNbr]

set_option linter.unusedVariables false in
/-- The **recursive orthogonal-projection retraction** `O_G` (Vrana–Christandl genmamu
tex:201). Defined by strong recursion on `i.val`: `orthoRetract G f i` is `f i` minus its
orthogonal projection onto the span of the *already-retracted* preceding non-neighbors,
i.e. `(I − P_i) f(v_i)` where `P_i` projects onto
`span ℝ {(O_G f)(v_j) | j ∈ A_i}`.

The projection is `Submodule.starProjection K : E →L[ℝ] E` (the orthogonal projection viewed
as an endomorphism of the full space). Since `EuclideanSpace ℝ (Fin D)` is finite-dimensional,
every submodule `K` is complete, so `K.HasOrthogonalProjection` is available by instance
inference.

We follow genmamu's projection convention (see the module docstring): the span automatically
absorbs linear dependence, and `(I − P_i) f(v_i)` is always orthogonal to the span. -/
noncomputable def orthoRetract (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : Fin n → EuclideanSpace ℝ (Fin D)) : Fin n → EuclideanSpace ℝ (Fin D)
  | i =>
    f i -
      (Submodule.span ℝ
        (↑((precNonNbr G i).image
          (fun j => if h : j.val < i.val then orthoRetract G f j else 0)))
            : Submodule ℝ (EuclideanSpace ℝ (Fin D))).starProjection (f i)
  termination_by i => i.val
  decreasing_by all_goals exact h

variable {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
  {f : Fin n → EuclideanSpace ℝ (Fin D)}

/-- The submodule onto which `orthoRetract G f i` is orthogonally projected: the span of the
already-retracted preceding non-neighbors of `i`. -/
noncomputable def precSpan (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : Fin n → EuclideanSpace ℝ (Fin D)) (i : Fin n) :
    Submodule ℝ (EuclideanSpace ℝ (Fin D)) :=
  Submodule.span ℝ (↑((precNonNbr G i).image (orthoRetract G f)))

/-- Inside `precNonNbr G i` the guard `j.val < i.val` always holds, so the span used in the
definition of `orthoRetract` coincides with `precSpan G f i`. -/
theorem orthoRetract_apply (i : Fin n) :
    orthoRetract G f i = f i - (precSpan G f i).starProjection (f i) := by
  have hspan :
      Submodule.span ℝ
          (↑((precNonNbr G i).image
            (fun j => if _ : j.val < i.val then orthoRetract G f j else 0))
              : Set (EuclideanSpace ℝ (Fin D)))
        = precSpan G f i := by
    unfold precSpan
    congr 1
    apply congrArg
    apply Finset.image_congr
    intro j hj
    rw [Finset.mem_coe, mem_precNonNbr] at hj
    simp only [hj.1, dif_pos]
  conv_lhs => rw [orthoRetract]
  simp only [hspan]

/-- The membership characterization of `precSpan`: a retracted preceding non-neighbor lies in
the span. -/
theorem orthoRetract_mem_precSpan {i j : Fin n} (hj : j ∈ precNonNbr G i) :
    orthoRetract G f j ∈ precSpan G f i := by
  apply Submodule.subset_span
  exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ hj)

/-- When `j < i` is a non-neighbor of `i`, the retracted vector at `i` is orthogonal to the
retracted vector at `j`. This is the one-sided core of `orthoRetract_isOR`. -/
theorem orthoRetract_inner_eq_zero_of_lt {i j : Fin n}
    (hlt : j.val < i.val) (hadj : ¬ G.Adj i j) :
    ⟪orthoRetract G f i, orthoRetract G f j⟫_ℝ = 0 := by
  have hmem : orthoRetract G f j ∈ precSpan G f i :=
    orthoRetract_mem_precSpan (mem_precNonNbr.2 ⟨hlt, hadj⟩)
  rw [orthoRetract_apply i]
  exact (precSpan G f i).starProjection_inner_eq_zero (f i) _ hmem

/-- **genmamu tex:203 (first claim).** `orthoRetract G f` (the map `O_G f`) is *always* an
orthogonal representation of `G`, for any input `f`. (genmamu tex:203, first claim.)

Proof: for distinct non-adjacent `i, j`, WLOG `j < i`; then `j ∈ A_i = precNonNbr G i`, so the
retracted `orthoRetract G f j` lies in `precSpan G f i`, and `orthoRetract G f i = (I − P_i)(f i)`
is orthogonal to that span by `Submodule.starProjection_inner_eq_zero`. -/
theorem orthoRetract_isOR : IsOR G (orthoRetract G f) := by
  intro i j hij hadj
  rcases lt_trichotomy i.val j.val with hlt | heq | hgt
  · -- i < j: use symmetry of the inner product and the i-side lemma at j
    rw [real_inner_comm]
    exact orthoRetract_inner_eq_zero_of_lt hlt (fun h => hadj h.symm)
  · exact absurd (Fin.ext heq) hij
  · exact orthoRetract_inner_eq_zero_of_lt hgt hadj

/-- **genmamu tex:203 (second claim).** If `f` is already an orthogonal representation, then
`orthoRetract G f = f`; that is, `O_G` fixes ORs. (genmamu tex:203, second claim.)

Proof by strong induction on `i.val`. Assuming `orthoRetract G f j = f j` for all `j < i`,
the span `precSpan G f i` equals the span of `{f j | j ∈ A_i}`. Since `f` is an OR, `f i ⊥ f j`
for all such `j`, so `f i ∈ (precSpan G f i)ᗮ`, hence `P_i (f i) = 0` and
`orthoRetract G f i = f i − 0 = f i`. -/
theorem orthoRetract_eq_self_of_isOR (hf : IsOR G f) : orthoRetract G f = f := by
  funext i
  -- Strong induction on `i.val`.
  suffices h : ∀ m, ∀ i : Fin n, i.val = m → orthoRetract G f i = f i from h i.val i rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro i hi
    have ih : ∀ j : Fin n, j.val < i.val → orthoRetract G f j = f j := by
      intro j hj
      exact IH j.val (hi ▸ hj) j rfl
    -- First, on `precNonNbr G i` the retracted vectors agree with `f`.
    have hspan_eq : precSpan G f i
        = Submodule.span ℝ (↑((precNonNbr G i).image f)) := by
      unfold precSpan
      congr 1
      apply congrArg
      apply Finset.image_congr
      intro j hj
      rw [Finset.mem_coe, mem_precNonNbr] at hj
      exact ih j hj.1
    -- `f i` is orthogonal to every generator of that span, hence in its orthogonal complement.
    have hperp : f i ∈ (precSpan G f i)ᗮ := by
      rw [hspan_eq, Submodule.mem_orthogonal']
      intro u hu
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
      · intro x hx
        rw [Finset.mem_coe, Finset.mem_image] at hx
        obtain ⟨j, hj, rfl⟩ := hx
        rw [mem_precNonNbr] at hj
        have hij : i ≠ j := by
          intro h; rw [h] at hj; exact absurd rfl (Nat.ne_of_gt hj.1)
        exact hf i j hij hj.2
      · simp
      · intro x y _ _ hx hy; rw [inner_add_right, hx, hy, add_zero]
      · intro c x _ hx; rw [inner_smul_right, hx, mul_zero]
    rw [orthoRetract_apply i, (precSpan G f i).starProjection_apply_eq_zero_iff.2 hperp,
      sub_zero]

/-! ### Rationality (genmamu tex:205-213) -/

/-- A vector of `EuclideanSpace ℝ (Fin D)` has rational coordinates. -/
def IsRat (x : EuclideanSpace ℝ (Fin D)) : Prop :=
  ∀ c, x c ∈ Set.range ((↑) : ℚ → ℝ)

theorem isRat_zero : IsRat (0 : EuclideanSpace ℝ (Fin D)) := by
  intro c; exact ⟨0, by simp⟩

theorem IsRat.add {x y : EuclideanSpace ℝ (Fin D)} (hx : IsRat x) (hy : IsRat y) :
    IsRat (x + y) := by
  intro c
  obtain ⟨a, ha⟩ := hx c
  obtain ⟨b, hb⟩ := hy c
  exact ⟨a + b, by push_cast [ha, hb]; rfl⟩

theorem IsRat.sub {x y : EuclideanSpace ℝ (Fin D)} (hx : IsRat x) (hy : IsRat y) :
    IsRat (x - y) := by
  intro c
  obtain ⟨a, ha⟩ := hx c
  obtain ⟨b, hb⟩ := hy c
  refine ⟨a - b, ?_⟩
  have : (x - y) c = x c - y c := rfl
  rw [this, ← ha, ← hb]; push_cast; rfl

/-- A rational scalar times a rational vector is rational. -/
theorem IsRat.ratSmul {q : ℝ} (hq : q ∈ Set.range ((↑) : ℚ → ℝ))
    {x : EuclideanSpace ℝ (Fin D)} (hx : IsRat x) : IsRat (q • x) := by
  intro c
  obtain ⟨r, hr⟩ := hq
  obtain ⟨a, ha⟩ := hx c
  refine ⟨r * a, ?_⟩
  have : (q • x) c = q * x c := rfl
  rw [this, ← hr, ← ha]; push_cast; rfl

/-- The rational numbers, as a subring of `ℝ` via the cast ring homomorphism; its underlying
set is exactly `Set.range ((↑) : ℚ → ℝ)`. -/
private noncomputable def ratSubring : Subring ℝ := (Rat.castHom ℝ).range

private theorem mem_ratSubring {r : ℝ} : r ∈ ratSubring ↔ r ∈ Set.range ((↑) : ℚ → ℝ) := by
  constructor
  · rintro ⟨q, rfl⟩; exact ⟨q, rfl⟩
  · rintro ⟨q, rfl⟩; exact ⟨q, rfl⟩

theorem isRat_inner {x y : EuclideanSpace ℝ (Fin D)} (hx : IsRat x) (hy : IsRat y) :
    ⟪x, y⟫_ℝ ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  rw [PiLp.inner_apply, ← mem_ratSubring]
  apply Subring.sum_mem
  intro c _
  rw [mem_ratSubring]
  obtain ⟨a, ha⟩ := hx c
  obtain ⟨b, hb⟩ := hy c
  refine ⟨a * b, ?_⟩
  simp only [RCLike.inner_apply, conj_trivial]
  rw [← ha, ← hb]; push_cast; ring

/-- The rational-cast image is closed under division (the cast of a quotient of rationals). -/
theorem isRat_div {a b : ℝ} (ha : a ∈ Set.range ((↑) : ℚ → ℝ))
    (hb : b ∈ Set.range ((↑) : ℚ → ℝ)) : a / b ∈ Set.range ((↑) : ℚ → ℝ) := by
  obtain ⟨p, rfl⟩ := ha
  obtain ⟨q, rfl⟩ := hb
  exact ⟨p / q, by push_cast; rfl⟩

/-- `‖v‖²` is rational for a rational vector `v` (it equals `⟪v, v⟫_ℝ`). -/
theorem isRat_normSq {v : EuclideanSpace ℝ (Fin D)} (hv : IsRat v) :
    ((‖v‖ ^ 2 : ℝ)) ∈ Set.range ((↑) : ℚ → ℝ) := by
  rw [← real_inner_self_eq_norm_sq]
  exact isRat_inner hv hv

/-- **Singleton case** of projection-rationality. The orthogonal projection of a rational `x`
onto the line `ℝ ∙ v` (with `v` rational) is rational. Uses Mathlib's explicit formula
`starProjection_singleton : (ℝ ∙ v).starProjection x = (⟪v, x⟫ / ‖v‖²) • v`, whose scalar is a
quotient of rationals (genmamu tex:211: `P_i x = ∑ ⟨g_m,x⟩/⟨g_m,g_m⟩ g_m`). -/
theorem starProjection_singleton_isRat {v x : EuclideanSpace ℝ (Fin D)}
    (hv : IsRat v) (hx : IsRat x) :
    IsRat ((ℝ ∙ v).starProjection x) := by
  rw [Submodule.starProjection_singleton ℝ x]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  exact IsRat.ratSmul (isRat_div (isRat_inner hv hx) (isRat_normSq hv)) hv

/-- **General span case** of projection-rationality. The orthogonal projection of a rational
vector `x` onto the span of a finite set `s` of rational vectors is rational.

Proof by `Finset.induction` on `s`. The step verifies the universal property of the orthogonal
projection (`Submodule.eq_starProjection_of_mem_of_inner_eq_zero`) for the explicit candidate
`p_s + P_{ℝ∙a'} x`, where `p_s` is the projection onto `span ℝ s` (rational by IH), and
`a' = a − p_s` (the Gram–Schmidt orthogonalization of the new vector `a` against `span ℝ s`,
rational by IH applied to `a`). This is genmamu's orthogonalize-then-project recipe
(tex:205-211). -/
theorem starProjection_span_isRat {s : Finset (EuclideanSpace ℝ (Fin D))}
    (hs : ∀ v ∈ s, IsRat v) {x : EuclideanSpace ℝ (Fin D)} (hx : IsRat x) :
    IsRat ((Submodule.span ℝ (↑s : Set (EuclideanSpace ℝ (Fin D)))).starProjection x) := by
  classical
  induction s using Finset.induction generalizing x with
  | empty =>
    simp only [Finset.coe_empty, Submodule.span_empty, Submodule.starProjection_bot,
      ContinuousLinearMap.zero_apply]
    exact isRat_zero
  | insert a s ha IH =>
    -- IH is available for all rational inputs (`generalizing x`).
    have hs' : ∀ v ∈ s, IsRat v := fun v hv => hs v (Finset.mem_insert_of_mem hv)
    have hai : IsRat a := hs a (Finset.mem_insert_self a s)
    set Ks : Submodule ℝ (EuclideanSpace ℝ (Fin D)) := Submodule.span ℝ (↑s : Set _) with hKs
    -- the Gram–Schmidt orthogonalization of `a` against `Ks`.
    set a' : EuclideanSpace ℝ (Fin D) := a - Ks.starProjection a with ha'
    have ha'_rat : IsRat a' := by
      rw [ha']; exact (hai).sub (IH hs' hai)
    -- candidate projection onto `span (insert a s)`.
    set p : EuclideanSpace ℝ (Fin D) :=
      Ks.starProjection x + (ℝ ∙ a').starProjection x with hp
    have hp_rat : IsRat p := by
      rw [hp]; exact (IH hs' hx).add (starProjection_singleton_isRat ha'_rat hx)
    -- `a'` is orthogonal to `Ks`.
    have ha'_perp : a' ∈ Ksᗮ := by rw [ha']; exact Ks.sub_starProjection_mem_orthogonal a
    -- membership facts
    have hKs_le : Ks ≤ Submodule.span ℝ (↑(insert a s) : Set _) := by
      rw [hKs]; apply Submodule.span_mono
      rw [Finset.coe_insert]; exact Set.subset_insert a _
    have ha_mem : a ∈ Submodule.span ℝ (↑(insert a s) : Set _) := by
      apply Submodule.subset_span
      rw [Finset.coe_insert]; exact Set.mem_insert a _
    have ha'_mem : a' ∈ Submodule.span ℝ (↑(insert a s) : Set _) := by
      rw [ha']
      exact Submodule.sub_mem _ ha_mem (hKs_le (Ks.starProjection_apply_mem a))
    -- the candidate `p` lies in the bigger span
    have hp_mem : p ∈ Submodule.span ℝ (↑(insert a s) : Set _) := by
      rw [hp]
      refine Submodule.add_mem _ (hKs_le (Ks.starProjection_apply_mem x)) ?_
      have : (ℝ ∙ a') ≤ Submodule.span ℝ (↑(insert a s) : Set _) := by
        rw [Submodule.span_singleton_le_iff_mem]; exact ha'_mem
      exact this ((ℝ ∙ a').starProjection_apply_mem x)
    -- `x - p ⊥ Ks` and `x - p ⊥ a'`, hence `x - p ⊥` every generator.
    have hperp_Ks : ∀ w ∈ Ks, ⟪x - p, w⟫_ℝ = 0 := by
      intro w hw
      have h1 : ⟪x - Ks.starProjection x, w⟫_ℝ = 0 := Ks.starProjection_inner_eq_zero x w hw
      have h2 : ⟪(ℝ ∙ a').starProjection x, w⟫_ℝ = 0 := by
        -- `(ℝ ∙ a').starProjection x ∈ ℝ ∙ a' ⊆ Ksᗮ`, so ⊥ `w ∈ Ks`
        have hmem : (ℝ ∙ a').starProjection x ∈ Ksᗮ := by
          have : (ℝ ∙ a') ≤ Ksᗮ := by
            rw [Submodule.span_singleton_le_iff_mem]; exact ha'_perp
          exact this ((ℝ ∙ a').starProjection_apply_mem x)
        exact (Submodule.mem_orthogonal' Ks _).1 hmem w hw
      rw [hp, inner_sub_left, inner_add_left, h2, add_zero,
        ← inner_sub_left]
      exact h1
    have hperp_a' : ⟪x - p, a'⟫_ℝ = 0 := by
      -- `⟪Ks.starProjection x, a'⟫ = 0` since `a' ∈ Ksᗮ`
      have h1 : ⟪Ks.starProjection x, a'⟫_ℝ = 0 := by
        rw [real_inner_comm]
        exact (Submodule.mem_orthogonal' Ks _).1 ha'_perp _ (Ks.starProjection_apply_mem x)
      -- `⟪x - (ℝ∙a').starProjection x, a'⟫ = 0` by projection property on `ℝ∙a'`
      have h2 : ⟪x - (ℝ ∙ a').starProjection x, a'⟫_ℝ = 0 :=
        (ℝ ∙ a').starProjection_inner_eq_zero x a' (Submodule.mem_span_singleton_self a')
      rw [hp]
      have : x - (Ks.starProjection x + (ℝ ∙ a').starProjection x)
          = (x - (ℝ ∙ a').starProjection x) - Ks.starProjection x := by abel
      rw [this, inner_sub_left, h2, h1, sub_zero]
    -- conclude `p` is the projection onto `span (insert a s)`
    have heq : (Submodule.span ℝ (↑(insert a s) : Set _)).starProjection x = p := by
      apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hp_mem
      intro w hw
      -- reduce orthogonality to generators `a` and `s`
      rw [Finset.coe_insert] at hw
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
      · intro y hy
        rcases hy with hy | hy
        · -- y = a = Ks.starProjection a + a'
          rw [hy]
          have hdec : a = Ks.starProjection a + a' := by rw [ha']; abel
          rw [hdec, inner_add_right, hperp_Ks _ (Ks.starProjection_apply_mem a), hperp_a',
            add_zero]
        · exact hperp_Ks y (Submodule.subset_span hy)
      · simp
      · intro u w _ _ hu hw; rw [inner_add_right, hu, hw, add_zero]
      · intro c w _ hw; rw [inner_smul_right, hw, mul_zero]
    rw [heq]; exact hp_rat

/-- **genmamu tex:205-213.** The retraction `orthoRetract G f` preserves rationality: if every
coordinate of every `f i` is rational, then so is every coordinate of every `orthoRetract G f i`.
(genmamu tex:205-213: each `P_i` maps `ℚ^d` into itself, so `O_G f` stays rational.)

Proof by strong induction on `i.val`: `orthoRetract G f i = f i − P_i (f i)`, where `P_i` is the
projection onto the span of the already-retracted preceding non-neighbors (all rational by IH),
and the projection of a rational vector onto the span of rational vectors is rational by
`starProjection_span_isRat`. -/
theorem orthoRetract_rational
    (hf : ∀ i, ∀ c, (f i) c ∈ Set.range ((↑) : ℚ → ℝ)) :
    ∀ i, ∀ c, (orthoRetract G f i) c ∈ Set.range ((↑) : ℚ → ℝ) := by
  -- reformulate via `IsRat`
  have hfR : ∀ i, IsRat (f i) := fun i => hf i
  suffices h : ∀ i, IsRat (orthoRetract G f i) from fun i c => h i c
  intro i
  suffices h : ∀ m, ∀ i : Fin n, i.val = m → IsRat (orthoRetract G f i) from h i.val i rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro i hi
    have ih : ∀ j : Fin n, j.val < i.val → IsRat (orthoRetract G f j) := by
      intro j hj; exact IH j.val (hi ▸ hj) j rfl
    rw [orthoRetract_apply i]
    refine (hfR i).sub ?_
    -- the projection is onto `precSpan G f i = span of retracted preceding non-neighbors`
    have hgen : ∀ v ∈ (precNonNbr G i).image (orthoRetract G f), IsRat v := by
      intro v hv
      rw [Finset.mem_image] at hv
      obtain ⟨j, hj, rfl⟩ := hv
      rw [mem_precNonNbr] at hj
      exact ih j hj.1
    have := starProjection_span_isRat (s := (precNonNbr G i).image (orthoRetract G f))
      hgen (x := f i) (hfR i)
    rw [precSpan]
    exact this

end LSS
