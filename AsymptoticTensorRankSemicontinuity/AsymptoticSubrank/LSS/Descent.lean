/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.LSS.Retraction
import Mathlib.Topology.GDelta.MetrizableSpace

/-!
# LSS — the ℚ-descent: a real GOR yields a rational GOR

This file formalizes rational descent in the Lovász–Saks–Schrijver /
Gortler–Theran (GOR) argument. Given that a graph `G` has *some* real general-position orthogonal
representation (GOR), we produce a *rational* one.

## Sources (verbatim)

* Gortler–Theran, arXiv:2310.11565,
  `the Gortler-Theran GOR proof notes`:
  - tex:121-124 — definition of *general position*: "A general position orthogonal
    representation (GOR) of `G` in `ℝ^D` is an OR with the added condition that the `v_i` are
    in general linear position. This means that any `D` of the vectors `v_i` are linearly
    independent."

* Vrana–Christandl, arXiv:1603.03964,
  `the Vrana-Christandl genmamu reference notes`:
  - tex:215 — "If `f : V → ℝ^d` is a function such that none of the denominators in the above
    expression of `P_i` is `0`, then `O_G f` is clearly continuous at `f`. This holds in
    particular if `f` is a general-position orthogonal representation, because in this case
    `O_G f = f`, and the families `(f(v))_{v∈A_i}` are linearly independent since `|A_i| ≤ d`."
  - tex:217 — "Now pick any general-position orthogonal representation `f : V → ℝ^d`. By
    continuity at `f` and using that being in general position is an open condition, there is an
    open neighbourhood `U` of `f` such that `f'∈U` implies that `O_G f'` is also a
    general-position orthogonal representation. Since `U≠∅` is open, there is a function
    `c₀ : V → ℚ^d` in `U`, therefore `c := O_G c₀` has the desired properties."

## Main declarations

* `IsGP v` — `v` is in *general position* (every `D`-subset is linearly independent).
* `IsGOR G v` — `v` is a *general-position orthogonal representation* (`IsOR G v ∧ IsGP v`).
* `isOpen_isGP` — general position is an **open** condition (det-`≠ 0`, continuous, finite ∩).
* `continuousAt_orthoRetract_of_isGOR` — `O_G` is continuous at a GOR whose preceding
  non-neighbor families are independent (genmamu:215).
* `exists_rat_gor_of_exists_real_gor` — **the descent** (genmamu:217): a real GOR ⟹ a rational GOR.
-/

open scoped InnerProductSpace
open RealInnerProductSpace

namespace LSS

variable {n D : ℕ}

/-! ### General position and GORs (gorProof:121-124) -/

/-- **General position** (Gortler–Theran gorProof tex:121-124): the assignment `v` is in
general linear position, i.e. *any `D` of the vectors are linearly independent*. We encode
"any `D`" as: every `D`-element subset `s` of the vertices indexes a linearly independent
family `(v i)_{i ∈ s}`.

> "the `v_i` are in general linear position. This means that any `D` of the vectors `v_i` are
>  linearly independent." -/
def IsGP (v : Fin n → EuclideanSpace ℝ (Fin D)) : Prop :=
  ∀ s : Finset (Fin n), s.card = D →
    LinearIndependent ℝ (fun i : (s : Set (Fin n)) => v i.val)

/-- **General-position orthogonal representation (GOR)** (Gortler–Theran gorProof tex:121):
an orthogonal representation that is additionally in general position. -/
def IsGOR (G : SimpleGraph (Fin n)) (v : Fin n → EuclideanSpace ℝ (Fin D)) : Prop :=
  IsOR G v ∧ IsGP v

theorem IsGOR.isOR {G : SimpleGraph (Fin n)} {v : Fin n → EuclideanSpace ℝ (Fin D)}
    (h : IsGOR G v) : IsOR G v := h.1

theorem IsGOR.isGP {G : SimpleGraph (Fin n)} {v : Fin n → EuclideanSpace ℝ (Fin D)}
    (h : IsGOR G v) : IsGP v := h.2

/-! ### General position is an open condition (genmamu:217)

We reformulate linear independence of the `D` vectors indexed by a `D`-subset `s` as a
determinant being nonzero, which is an open condition (the determinant is continuous and
`{x | x ≠ 0}` is open), and then intersect over the finitely many `D`-subsets. -/

/-- The `D × D` matrix whose rows are the (Euclidean) coordinates of the vectors `v i`,
`i ∈ s`, where the `D`-subset `s` is reindexed by `e : ↥s ≃ Fin D`. Row `k`, column `c` is the
`c`-th coordinate of `v (e.symm k)`. -/
noncomputable def gpMatrix (v : Fin n → EuclideanSpace ℝ (Fin D)) {s : Finset (Fin n)}
    (e : (s : Set (Fin n)) ≃ Fin D) : Matrix (Fin D) (Fin D) ℝ :=
  fun k c => v (e.symm k).val c

/-- The matrix entries of `gpMatrix` are jointly continuous in `v`: each entry is
`v ↦ v (e.symm k) c`, a coordinate evaluation composed with a coordinate projection. -/
theorem continuous_gpMatrix_entry {s : Finset (Fin n)} (e : (s : Set (Fin n)) ≃ Fin D)
    (k c : Fin D) :
    Continuous (fun v : Fin n → EuclideanSpace ℝ (Fin D) => gpMatrix v e k c) := by
  -- `gpMatrix v e k c = (v (e.symm k)) c`: a coordinate evaluation of a coordinate projection.
  change Continuous (fun v : Fin n → EuclideanSpace ℝ (Fin D) => (v (e.symm k).val) c)
  fun_prop

/-- `v ↦ (gpMatrix v e).det` is continuous. -/
theorem continuous_gpMatrix_det {s : Finset (Fin n)} (e : (s : Set (Fin n)) ≃ Fin D) :
    Continuous (fun v : Fin n → EuclideanSpace ℝ (Fin D) => (gpMatrix v e).det) := by
  apply Continuous.matrix_det
  apply continuous_pi
  intro k
  apply continuous_pi
  intro c
  exact continuous_gpMatrix_entry e k c

/-- The canonical linear equivalence `EuclideanSpace ℝ (Fin D) ≃ₗ[ℝ] (Fin D → ℝ)` "forget the
`ℓ²` structure"; it sends `x` to the plain function `fun c => x c`. -/
private noncomputable def euclToPi : EuclideanSpace ℝ (Fin D) ≃ₗ[ℝ] (Fin D → ℝ) :=
  WithLp.linearEquiv 2 ℝ (Fin D → ℝ)

private theorem euclToPi_apply (x : EuclideanSpace ℝ (Fin D)) (c : Fin D) :
    euclToPi x c = x c := rfl

/-- **Reformulation of linear independence via the determinant.** For a `D`-subset `s` and a
reindexing `e : ↥s ≃ Fin D`, the family `(v i)_{i ∈ s}` is linearly independent iff the
determinant of `gpMatrix v e` is nonzero. -/
theorem linearIndependent_iff_gpMatrix_det_ne_zero
    (v : Fin n → EuclideanSpace ℝ (Fin D)) {s : Finset (Fin n)}
    (e : (s : Set (Fin n)) ≃ Fin D) :
    LinearIndependent ℝ (fun i : (s : Set (Fin n)) => v i.val)
      ↔ (gpMatrix v e).det ≠ 0 := by
  classical
  -- Step 1: reindex by `e` (linear independence invariant under reindexing).
  rw [← linearIndependent_equiv e.symm]
  -- Step 2: rewrite the reindexed family as `euclToPi.symm ∘ (rows of gpMatrix)`.
  have hrw : (fun i : (s : Set (Fin n)) => v i.val) ∘ e.symm
      = euclToPi.symm.toLinearMap ∘ (fun k : Fin D => gpMatrix v e k) := by
    funext k
    apply euclToPi.injective
    funext c
    simp only [Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rfl
  rw [hrw, euclToPi.symm.toLinearMap.linearIndependent_iff (LinearEquiv.ker _)]
  -- `gpMatrix v e k = (gpMatrix v e).row k`, a square matrix over the field ℝ.
  rw [show (fun k : Fin D => gpMatrix v e k) = (gpMatrix v e).row from rfl,
    Matrix.linearIndependent_rows_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero]

/-- **General position is an open condition** (genmamu tex:217: "using that being in general
position is an open condition"). The set of general-position assignments is open: it is the
finite intersection, over the (finitely many) `D`-subsets `s`, of the preimages of `{x | x ≠ 0}`
under the continuous determinant map `v ↦ (gpMatrix v e).det`. -/
theorem isOpen_isGP :
    IsOpen { v : Fin n → EuclideanSpace ℝ (Fin D) | IsGP v } := by
  classical
  -- For each `D`-subset `s`, fix a reindexing `e_s : ↥(↑s) ≃ Fin D`.
  let e : ∀ s : { s : Finset (Fin n) // s.card = D }, (s.1 : Set (Fin n)) ≃ Fin D :=
    fun s => Finset.equivFinOfCardEq s.2
  -- The GP set is `⋂_{s : card = D} { v | (gpMatrix v e_s).det ≠ 0 }`.
  have key : { v : Fin n → EuclideanSpace ℝ (Fin D) | IsGP v }
      = ⋂ (s : { s : Finset (Fin n) // s.card = D }),
          { v | (gpMatrix v (e s)).det ≠ 0 } := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hv s
      exact (linearIndependent_iff_gpMatrix_det_ne_zero v (e s)).1 (hv s.1 s.2)
    · intro hv s hs
      exact (linearIndependent_iff_gpMatrix_det_ne_zero v (e ⟨s, hs⟩)).2 (hv ⟨s, hs⟩)
  rw [key]
  apply isOpen_iInter_of_finite
  intro s
  exact (continuous_gpMatrix_det _).isOpen_preimage _ isOpen_ne

/-! ### Continuity of `O_G` at a GOR (genmamu tex:215) -/

set_option maxHeartbeats 1000000 in
-- The orthogonal-projection-onto-span term forces heavy `HasOrthogonalProjection` instance
-- synthesis in `EuclideanSpace`; the default heartbeat budgets are insufficient.
set_option synthInstance.maxHeartbeats 400000 in
/-- **One Gram–Schmidt step** (genmamu tex:205-211, pointwise). The orthogonal projection onto the
span of `insert a t` decomposes as the projection onto `span t` plus the projection onto the line
spanned by the Gram–Schmidt orthogonalization `a' = a − P_{span t} a`. This is the pointwise
algebraic identity used inside `starProjection_span_isRat` (Retraction.lean), isolated here so the
continuity proof can split into two continuous summands. -/
private theorem starProjection_span_insert
    (t : Finset (EuclideanSpace ℝ (Fin D))) (a x : EuclideanSpace ℝ (Fin D)) :
    (Submodule.span ℝ (↑(insert a t) : Set (EuclideanSpace ℝ (Fin D)))).starProjection x
      = (Submodule.span ℝ (↑t : Set _)).starProjection x
        + (ℝ ∙ (a - (Submodule.span ℝ (↑t : Set _)).starProjection a)).starProjection x := by
  classical
  set Ks : Submodule ℝ (EuclideanSpace ℝ (Fin D)) := Submodule.span ℝ (↑t : Set _) with hKs
  set a' : EuclideanSpace ℝ (Fin D) := a - Ks.starProjection a with ha'
  set p : EuclideanSpace ℝ (Fin D) :=
    Ks.starProjection x + (ℝ ∙ a').starProjection x with hp
  -- `a'` is orthogonal to `Ks`.
  have ha'_perp : a' ∈ Ksᗮ := by rw [ha']; exact Ks.sub_starProjection_mem_orthogonal a
  -- membership facts
  have hKs_le : Ks ≤ Submodule.span ℝ (↑(insert a t) : Set _) := by
    rw [hKs]; apply Submodule.span_mono
    rw [Finset.coe_insert]; exact Set.subset_insert a _
  have ha_mem : a ∈ Submodule.span ℝ (↑(insert a t) : Set _) := by
    apply Submodule.subset_span
    rw [Finset.coe_insert]; exact Set.mem_insert a _
  have ha'_mem : a' ∈ Submodule.span ℝ (↑(insert a t) : Set _) := by
    rw [ha']
    exact Submodule.sub_mem _ ha_mem (hKs_le (Ks.starProjection_apply_mem a))
  have hp_mem : p ∈ Submodule.span ℝ (↑(insert a t) : Set _) := by
    rw [hp]
    refine Submodule.add_mem _ (hKs_le (Ks.starProjection_apply_mem x)) ?_
    have : (ℝ ∙ a') ≤ Submodule.span ℝ (↑(insert a t) : Set _) := by
      rw [Submodule.span_singleton_le_iff_mem]; exact ha'_mem
    exact this ((ℝ ∙ a').starProjection_apply_mem x)
  -- `x - p ⊥ Ks` and `x - p ⊥ a'`.
  have hperp_Ks : ∀ w ∈ Ks, ⟪x - p, w⟫_ℝ = 0 := by
    intro w hw
    have h1 : ⟪x - Ks.starProjection x, w⟫_ℝ = 0 := Ks.starProjection_inner_eq_zero x w hw
    have h2 : ⟪(ℝ ∙ a').starProjection x, w⟫_ℝ = 0 := by
      have hmem : (ℝ ∙ a').starProjection x ∈ Ksᗮ := by
        have : (ℝ ∙ a') ≤ Ksᗮ := by
          rw [Submodule.span_singleton_le_iff_mem]; exact ha'_perp
        exact this ((ℝ ∙ a').starProjection_apply_mem x)
      exact (Submodule.mem_orthogonal' Ks _).1 hmem w hw
    rw [hp, inner_sub_left, inner_add_left, h2, add_zero, ← inner_sub_left]
    exact h1
  have hperp_a' : ⟪x - p, a'⟫_ℝ = 0 := by
    have h1 : ⟪Ks.starProjection x, a'⟫_ℝ = 0 := by
      rw [real_inner_comm]
      exact (Submodule.mem_orthogonal' Ks _).1 ha'_perp _ (Ks.starProjection_apply_mem x)
    have h2 : ⟪x - (ℝ ∙ a').starProjection x, a'⟫_ℝ = 0 :=
      (ℝ ∙ a').starProjection_inner_eq_zero x a' (Submodule.mem_span_singleton_self a')
    rw [hp]
    have : x - (Ks.starProjection x + (ℝ ∙ a').starProjection x)
        = (x - (ℝ ∙ a').starProjection x) - Ks.starProjection x := by abel
    rw [this, inner_sub_left, h2, h1, sub_zero]
  -- conclude `p` is the projection onto `span (insert a t)`.
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hp_mem
  intro w hw
  rw [Finset.coe_insert] at hw
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · intro y hy
    rcases hy with hy | hy
    · rw [hy]
      have hdec : a = Ks.starProjection a + a' := by rw [ha']; abel
      rw [hdec, inner_add_right, hperp_Ks _ (Ks.starProjection_apply_mem a), hperp_a', add_zero]
    · exact hperp_Ks y (Submodule.subset_span hy)
  · simp
  · intro u w _ _ hu hw; rw [inner_add_right, hu, hw, add_zero]
  · intro c w _ hw; rw [inner_smul_right, hw, mul_zero]

set_option maxHeartbeats 1000000 in
-- The orthogonal-projection-onto-span term forces heavy `HasOrthogonalProjection` instance
-- synthesis in `EuclideanSpace`; the default heartbeat budgets are insufficient.
set_option synthInstance.maxHeartbeats 400000 in
/-- **Gram–Schmidt projection continuity helper** (genmamu tex:205-211). Let `s` be a finite set
of indices, `w j g` a family of vectors depending continuously (at `f`) on the parameter `g`, and
`z g` a continuously-varying vector. If the values `(w j f)_{j ∈ s}` are *linearly independent*,
then the orthogonal projection of `z g` onto the span of `(w j g)_{j ∈ s}` is continuous at `f`.

This is the continuity shadow of `starProjection_span_isRat` (Retraction.lean): the same
orthogonalize-then-project decomposition
`P_{insert a s} = P_{span s} + P_{ℝ ∙ a'}`  with  `a' = w a − P_{span s}(w a)`,
where `P_{ℝ ∙ a'}(z) = (⟪a', z⟫ / ‖a'‖²) • a'` (`Submodule.starProjection_singleton`) is
continuous because `a' f ≠ 0` (linear independence ⟹ `w a f ∉ span (w '' s)`), so the
denominator `‖a' g‖²` is continuous and nonzero at `f` (`ContinuousAt.div`). -/
private theorem continuousAt_starProjection_span
    {f : Fin n → EuclideanSpace ℝ (Fin D)}
    {s : Finset (Fin n)}
    {w : Fin n → (Fin n → EuclideanSpace ℝ (Fin D)) → EuclideanSpace ℝ (Fin D)}
    (hw : ∀ j ∈ s, ContinuousAt (fun g => w j g) f)
    (hindep : LinearIndependent ℝ (fun j : (s : Set (Fin n)) => w j.val f))
    {z : (Fin n → EuclideanSpace ℝ (Fin D)) → EuclideanSpace ℝ (Fin D)}
    (hz : ContinuousAt z f) :
    ContinuousAt
      (fun g => (Submodule.span ℝ
        (↑(s.image (fun j => w j g)) : Set (EuclideanSpace ℝ (Fin D)))).starProjection
          (z g)) f := by
  classical
  induction s using Finset.induction generalizing z with
  | empty =>
    simpa only [Finset.image_empty, Finset.coe_empty, Submodule.span_empty,
      Submodule.starProjection_bot, ContinuousLinearMap.zero_apply] using continuousAt_const
  | insert a s ha IH =>
    -- Restrict the hypotheses to `s`.
    have hw_s : ∀ j ∈ s, ContinuousAt (fun g => w j g) f :=
      fun j hj => hw j (Finset.mem_insert_of_mem hj)
    have hwa : ContinuousAt (fun g => w a g) f := hw a (Finset.mem_insert_self a s)
    have hindep_s : LinearIndependent ℝ (fun j : (s : Set (Fin n)) => w j.val f) := by
      have hsub : (s : Set (Fin n)) ⊆ ((insert a s : Finset (Fin n)) : Set (Fin n)) := by
        intro j hj; exact Finset.mem_insert_of_mem hj
      exact hindep.comp (Set.inclusion hsub) (Set.inclusion_injective hsub)
    -- `Ks g` is the span of the `s`-part; `a' g` the Gram–Schmidt orthogonalization of `w a g`.
    set Ks : (Fin n → EuclideanSpace ℝ (Fin D)) → Submodule ℝ (EuclideanSpace ℝ (Fin D)) :=
      fun g => Submodule.span ℝ (↑(s.image (fun j => w j g)) : Set _) with hKsdef
    set a' : (Fin n → EuclideanSpace ℝ (Fin D)) → EuclideanSpace ℝ (Fin D) :=
      fun g => w a g - (Ks g).starProjection (w a g) with ha'def
    -- Rewrite the goal using the one-step Gram–Schmidt decomposition.
    have hrw : (fun g => (Submodule.span ℝ
        (↑((insert a s).image (fun j => w j g)) : Set _)).starProjection (z g))
        = fun g => (Ks g).starProjection (z g) + (ℝ ∙ a' g).starProjection (z g) := by
      funext g
      rw [Finset.image_insert, starProjection_span_insert]
    rw [hrw]
    -- First summand: induction hypothesis with the same `z`.
    have hP1 : ContinuousAt (fun g => (Ks g).starProjection (z g)) f :=
      IH hw_s hindep_s hz
    -- `g ↦ a' g` is continuous at `f`.
    have hca' : ContinuousAt (fun g => a' g) f := by
      rw [ha'def]
      exact hwa.sub (IH hw_s hindep_s hwa)
    -- `a' f ≠ 0`: linear independence ⟹ `w a f ∉ Ks f`.
    have ha'_ne : a' f ≠ 0 := by
      -- `a ∈ insert a s`, and the subset `S = {j | ↑j ∈ s}` of the index excludes it.
      have ha_mem_ins : a ∈ (insert a s : Finset (Fin n)) := Finset.mem_insert_self a s
      set xa : ((insert a s : Finset (Fin n)) : Set (Fin n)) := ⟨a, ha_mem_ins⟩ with hxa
      set S : Set ((insert a s : Finset (Fin n)) : Set (Fin n)) :=
        {j | (j : Fin n) ∈ s} with hS
      have hxa_notin : xa ∉ S := by
        rw [hS, hxa]; simp only [Set.mem_setOf_eq]; exact ha
      have hnot := hindep.notMem_span_image (s := S) (x := xa) hxa_notin
      -- The image of `S` under `j ↦ w ↑j f` is `(fun j => w j f) '' s`.
      have himg : (fun j : ((insert a s : Finset (Fin n)) : Set (Fin n)) => w j.val f) '' S
          = (fun j : Fin n => w j f) '' (s : Set (Fin n)) := by
        ext y
        simp only [Set.mem_image, hS, Set.mem_setOf_eq, Finset.mem_coe]
        constructor
        · rintro ⟨j, hj, rfl⟩; exact ⟨j.val, hj, rfl⟩
        · rintro ⟨j, hj, rfl⟩
          exact ⟨⟨j, Finset.mem_insert_of_mem hj⟩, hj, rfl⟩
      rw [himg] at hnot
      -- so `w a f ∉ span ((fun j => w j f) '' s) = Ks f`.
      have hspan_eq : Ks f
          = Submodule.span ℝ ((fun j : Fin n => w j f) '' (s : Set (Fin n))) := by
        simp only [hKsdef]; congr 1; rw [Finset.coe_image]
      rw [ha'def]; simp only
      intro hzero
      apply hnot
      have heq : w a f = (Ks f).starProjection (w a f) := by
        rw [sub_eq_zero] at hzero; exact hzero
      have hmem : w a f ∈ Ks f := by
        rw [heq]; exact (Ks f).starProjection_apply_mem (w a f)
      rwa [hspan_eq] at hmem
    -- Second summand: the singleton projection `(⟪a' g, z g⟫ / ‖a' g‖²) • a' g`.
    apply hP1.add
    have hsingle : (fun g => (ℝ ∙ a' g).starProjection (z g))
        = fun g => (⟪a' g, z g⟫_ℝ / (‖a' g‖ ^ 2)) • a' g := by
      funext g
      rw [Submodule.starProjection_singleton ℝ (z g)]
      simp only [RCLike.ofReal_real_eq_id, id_eq]
    rw [hsingle]
    -- numerator, denominator continuity at `f`.
    have hnum : ContinuousAt (fun g => ⟪a' g, z g⟫_ℝ) f :=
      (continuous_inner.continuousAt).comp (hca'.prodMk hz)
    have hden : ContinuousAt (fun g => (‖a' g‖ ^ 2 : ℝ)) f := by
      have : ContinuousAt (fun g => ‖a' g‖) f := hca'.norm
      exact this.pow 2
    have hden_ne : (‖a' f‖ ^ 2 : ℝ) ≠ 0 := by
      have : ‖a' f‖ ≠ 0 := norm_ne_zero_iff.2 ha'_ne
      exact pow_ne_zero 2 this
    exact (hnum.div hden hden_ne).smul hca'

set_option maxHeartbeats 1000000 in
-- The orthogonal-projection-onto-span term forces heavy `HasOrthogonalProjection` instance
-- synthesis in `EuclideanSpace`; the default heartbeat budgets are insufficient.
set_option synthInstance.maxHeartbeats 400000 in
/-- **genmamu tex:215.** The retraction `O_G` is continuous at any general-position orthogonal
representation `f` whose preceding-non-neighbor families are linearly independent.
(genmamu tex:215: `O_G` is continuous wherever no denominator in `P_i` vanishes, in
particular at a general-position OR, where `O_G f = f` and each family `(f(v))_{v∈A_i}`
is linearly independent because `|A_i| ≤ d`.)

Proof strategy (genmamu:205-215): expand `O_G g i = g i − P_i (g i)` where `P_i` is the
orthogonal projection onto the span of the already-retracted preceding non-neighbors. By the
explicit Gram–Schmidt form (tex:205-211), the only non-continuity in `g ↦ P_i (g i)` arises
when a Gram–Schmidt denominator `⟨g_m, g_m⟩` vanishes. The paper obtains nonvanishing from
linear independence of the preceding-non-neighbor families: in genmamu tex:215, its connectivity
hypotheses give `|A_i| ≤ d`, so general position implies the families `(f(v))_{v ∈ A_i}` are
linearly independent. This descent file abstracts that source as the explicit hypothesis
`hindep`, because `IsGOR G f` alone does not imply independence when `A_i` has more than `D`
vertices. With `hindep`, all denominators are nonzero at `f`, making each `g ↦ O_G g i`
continuous at `f` by induction on `i.val`.

**Proof.** Continuity into the product `Fin n → ℝ^D` is coordinatewise
(`continuousAt_pi`), so it suffices to prove `g ↦ orthoRetract G g i` is continuous at `f` for
each `i`, by strong induction on `i.val`. Write `orthoRetract G g i = g i − P_i (g i)` with
`P_i (g i) = (precSpan G g i).starProjection (g i)` (`orthoRetract_apply`); `g ↦ g i` is
continuous, so it remains to handle `g ↦ P_i (g i)`. The generators `(orthoRetract G g j)_{j∈A_i}`
are each continuous at `f` by the induction hypothesis (`j.val < i.val`), and at `f` they equal
`(f j)` (since `orthoRetract G f = f`), which is linearly independent by `hindep i`. The genuine
obstacle — Mathlib has no continuity lemma for projection onto the span of a *varying* family — is
given by `continuousAt_starProjection_span` below: it follows the explicit Gram–Schmidt sum
(genmamu:205–211), splitting `P_{span (insert a s)} = P_{span s} + P_{ℝ ∙ a'}` with
`a' = w a − P_{span s}(w a)` (`starProjection_span_insert`), where the per-line term
`P_{ℝ ∙ a'}(z) = (⟪a', z⟫ / ‖a'‖²) • a'` (`Submodule.starProjection_singleton`) is continuous via
`ContinuousAt.div`, whose denominator `‖a' f‖² ≠ 0` because linear independence forces
`w a f ∉ span (w '' s)`, i.e. `a' f ≠ 0` (`LinearIndependent.notMem_span_image`). -/
theorem continuousAt_orthoRetract_of_isGOR {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {f : Fin n → EuclideanSpace ℝ (Fin D)} (hf : IsGOR G f)
    (hindep : ∀ i : Fin n,
      LinearIndependent ℝ (fun j : (precNonNbr G i : Set (Fin n)) => f j.val)) :
    ContinuousAt (fun g => orthoRetract G g) f := by
  -- STEP A: continuity into the product is coordinatewise.
  rw [continuousAt_pi]
  intro i
  -- STEP B: strong induction on `i.val`.
  suffices H : ∀ m, ∀ i : Fin n, i.val = m →
      ContinuousAt (fun g => orthoRetract G g i) f from H i.val i rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro i hi
    have ih : ∀ j : Fin n, j.val < i.val →
        ContinuousAt (fun g => orthoRetract G g j) f := by
      intro j hj; exact IH j.val (hi ▸ hj) j rfl
    -- STEP C: `orthoRetract G g i = g i − (precSpan G g i).starProjection (g i)`.
    have hfun : (fun g : Fin n → EuclideanSpace ℝ (Fin D) => orthoRetract G g i)
        = fun g => g i - (precSpan G g i).starProjection (g i) := by
      funext g; exact orthoRetract_apply i
    rw [hfun]
    apply ContinuousAt.sub ((continuous_apply i).continuousAt)
    -- STEP D/E: continuity of the projection via the Gram–Schmidt helper.
    have hgen : ∀ j ∈ precNonNbr G i,
        ContinuousAt (fun g => orthoRetract G g j) f := by
      intro j hj
      exact ih j (mem_precNonNbr.1 hj).1
    -- At `f` the retracted preceding non-neighbors equal `f`, which is independent.
    have hindep_f : LinearIndependent ℝ
        (fun j : (precNonNbr G i : Set (Fin n)) => orthoRetract G f j.val) := by
      have hfix : orthoRetract G f = f := orthoRetract_eq_self_of_isOR hf.1
      simpa only [hfix] using hindep i
    have hgoal := continuousAt_starProjection_span (f := f) (s := precNonNbr G i)
      (w := fun j g => orthoRetract G g j) hgen hindep_f
      (z := fun g => g i) ((continuous_apply i).continuousAt)
    -- The helper's span `span ℝ (image (fun j => orthoRetract G g j))` is `precSpan G g i`
    -- (eta of `orthoRetract G g`), so the goal matches up to defeq.
    exact hgoal

/-! ### The ℚ-descent (genmamu tex:217) -/

/-- Rational points are dense in `Fin n → EuclideanSpace ℝ (Fin D)`: the rationals are dense in
`ℝ` (`Rat.denseRange_cast`), and density is preserved by the product/coordinate structure.

Proof: the map is `Pi.map (fun _ i => …)` over the `Fin n` factors; by `DenseRange.piMap` it
suffices that each factor `(Fin D → ℚ) → EuclideanSpace ℝ (Fin D)` is dense. Each factor is
`(EuclideanSpace.equiv …).symm ∘ Pi.map (fun _ => Rat.cast)`: the inner pi-map of the dense
`Rat.cast` is dense (`DenseRange.piMap` + `Rat.denseRange_cast`), and the outer continuous-linear
equivalence (a homeomorphism, hence surjective with dense range) preserves density
(`DenseRange.comp`). -/
theorem denseRange_ratPoints :
    DenseRange (fun q : Fin n → Fin D → ℚ =>
      (fun i => (EuclideanSpace.equiv (Fin D) ℝ).symm (fun c => ((q i c : ℝ))) :
        Fin n → EuclideanSpace ℝ (Fin D))) := by
  -- Present the map as a `Pi.map` over the `Fin n` factors.
  have hrw : (fun q : Fin n → Fin D → ℚ =>
      (fun i => (EuclideanSpace.equiv (Fin D) ℝ).symm (fun c => ((q i c : ℝ))) :
        Fin n → EuclideanSpace ℝ (Fin D)))
      = Pi.map (fun (_ : Fin n) (g : Fin D → ℚ) =>
          (EuclideanSpace.equiv (Fin D) ℝ).symm (fun c => ((g c : ℝ)))) := by
    rfl
  rw [hrw]
  apply DenseRange.piMap
  intro _
  -- Each factor is `equiv.symm ∘ (Pi.map (fun _ => Rat.cast))`.
  have hfac : (fun (g : Fin D → ℚ) =>
      (EuclideanSpace.equiv (Fin D) ℝ).symm (fun c => ((g c : ℝ))))
      = (fun h : Fin D → ℝ => (EuclideanSpace.equiv (Fin D) ℝ).symm h)
        ∘ Pi.map (fun (_ : Fin D) => ((↑) : ℚ → ℝ)) := by
    rfl
  rw [hfac]
  refine DenseRange.comp ?_ ?_ (EuclideanSpace.equiv (Fin D) ℝ).symm.continuous
  · exact (EuclideanSpace.equiv (Fin D) ℝ).symm.surjective.denseRange
  · exact DenseRange.piMap (fun _ => Rat.denseRange_cast)

set_option linter.unusedDecidableInType false in
/-- **THE DESCENT — genmamu tex:217.** If a graph `G` has *some* real general-position
orthogonal representation whose preceding-non-neighbor families are linearly independent, then it
has a *rational* one (every coordinate of every vector is the cast of a rational).
(genmamu tex:217: general position is an open condition, so a real GOR `f` has a
neighbourhood `U` on which `O_G` stays a GOR; pick a rational `c₀ ∈ U`, then
`c := O_G c₀` is the desired rational GOR.)

Proof: let `f₀` be a real GOR with independent preceding families. In genmamu this independence
is supplied by the connectivity bound `|A_i| ≤ d` (tex:215); here it is an explicit descent
hypothesis. `O_G` is continuous at `f₀` (`continuousAt_orthoRetract_of_isGOR`) and
`O_G f₀ = f₀ ∈ {IsGP}`, which is open (`isOpen_isGP`); hence there is an open neighbourhood
`U ∋ f₀` with `O_G '' U ⊆ {IsGP}`. Rational points are dense, so some rational `c₀ ∈ U`. Then
`c := O_G c₀` is rational (`orthoRetract_rational`), an OR (`orthoRetract_isOR`), and in general
position (`O_G c₀ ∈ O_G '' U ⊆ {IsGP}`), i.e. a rational GOR. -/
theorem exists_rat_gor_of_exists_real_gor (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : ∃ f : Fin n → EuclideanSpace ℝ (Fin D), IsGOR G f ∧
      ∀ i : Fin n,
        LinearIndependent ℝ (fun j : (precNonNbr G i : Set (Fin n)) => f j.val)) :
    ∃ f : Fin n → EuclideanSpace ℝ (Fin D),
      IsGOR G f ∧ (∀ i c, (f i) c ∈ Set.range ((↑) : ℚ → ℝ)) := by
  classical
  obtain ⟨f₀, hf₀, hf₀_indep⟩ := h
  -- `O_G` is continuous at `f₀`.
  have hcont : ContinuousAt (fun g => orthoRetract G g) f₀ :=
    continuousAt_orthoRetract_of_isGOR hf₀ hf₀_indep
  -- `O_G f₀ = f₀`, which is in the open GP set.
  have hfix : orthoRetract G f₀ = f₀ := orthoRetract_eq_self_of_isOR hf₀.1
  have hf₀_gp : IsGP f₀ := hf₀.2
  -- The preimage of the open GP set under `O_G` is a neighbourhood of `f₀`.
  have hpre : (fun g => orthoRetract G g) ⁻¹'
      { v : Fin n → EuclideanSpace ℝ (Fin D) | IsGP v } ∈ nhds f₀ := by
    apply hcont.preimage_mem_nhds
    rw [hfix]
    exact isOpen_isGP.mem_nhds hf₀_gp
  -- Extract an OPEN neighbourhood `U ∋ f₀` inside that preimage (genmamu:217 "open nbhd `U`").
  obtain ⟨U, hU_sub, hU_open, hU_mem⟩ := mem_nhds_iff.1 hpre
  -- Rational points are dense, so `U ≠ ∅` open meets the rational points: ∃ rational `c₀ ∈ U`.
  obtain ⟨q, hq⟩ := (denseRange_ratPoints (n := n) (D := D)).exists_mem_open hU_open ⟨f₀, hU_mem⟩
  -- Name the rational point `c₀` and its retraction `c := O_G c₀`.
  set c₀ : Fin n → EuclideanSpace ℝ (Fin D) :=
    (fun i => (EuclideanSpace.equiv (Fin D) ℝ).symm (fun c => ((q i c : ℝ)))) with hc₀
  -- `c₀` has rational coordinates.
  have hc₀_rat : ∀ i, ∀ c, (c₀ i) c ∈ Set.range ((↑) : ℚ → ℝ) := by
    intro i c; exact ⟨q i c, rfl⟩
  -- `c₀ ∈ U ⊆ {O_G · is GP}`, so `O_G c₀` is in general position.
  have hc₀_gp : IsGP (orthoRetract G c₀) := hU_sub hq
  refine ⟨orthoRetract G c₀, ⟨orthoRetract_isOR, hc₀_gp⟩, ?_⟩
  -- `O_G c₀` is rational since `c₀` is.
  exact orthoRetract_rational (fun i c => hc₀_rat i c)

end LSS
