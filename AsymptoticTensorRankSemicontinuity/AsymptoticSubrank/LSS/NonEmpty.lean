/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# LSS non-emptiness for the I-placed-first base case

This file formalizes the "I-placed-first" non-vanishing base case
(`lem:nonempt1`) in the Lovász–Saks–Schrijver / Gortler–Theran argument.

# Sources

* **Gortler–Theran**, `GOR-LSS-2310.11565-gorProof.tex` lines 525-537 (`lem:nonempt1`):

  > "Let `I ⊆ [n]`, `|I| = D`, and `τ` an ordering with `I = {τ_1,…,τ_D}`.
  >  Then `GOR⁺_τ ∩ GP(I)` is non-empty."

  (The proof: each `τ_i ∈ I` has fewer than `D` preceding non-neighbors, so the
  process can place `v_{τ_1},…,v_{τ_D}` in general position and later steps preserve
  it. SOURCE TYPO: line 535 reads "preceding neighbors"; the dimension argument
  below shows it must be "preceding *non*-neighbors" — the count that actually
  bounds the number of orthogonality constraints on `v_{τ_i}`.)

* **Lovász–Saks–Schrijver**, `lovasz-saks-schrijver-orthrep-connectivity.tex`
  lines 215-219: completing `{f(u_1),…,f(u_m)}` to a basis of `f(v)^⊥` and varying
  the free vectors realizes every vector orthogonal to the span of the `v_{i_j}`.

  This is the **surjectivity** of the construction onto the orthogonal complement
  that (N1) below formalizes.

# Contents

* (N1) `crossMinors_surj_orthogonal` — over `ℝ`: given `m ≤ e` linearly independent
  columns `w_1,…,w_m ∈ ℝ^{e+1}` and ANY target `z` orthogonal (in the standard dot
  product) to every `w_i` with `z ≠ 0`, there exist free columns `x_1,…,x_{e-m}` so
  that `crossMinors (w | x) = z`.  (The construction's scalar `y` is then set to `1`.)

  The route is the SUFFICIENT version named in the strategy: complete `{w_i, z}` to a
  basis using vectors that lie in `(span{z})ᗮ`; then the `(e+1)`-st missing column of
  `crossMinors(w|x)` is forced to be a scalar multiple of `z` (it is orthogonal to all
  `e` columns, which span a hyperplane whose orthogonal complement is `ℝ·z`), and the
  scalar is nonzero because the columns are independent; finally rescale.

* (N2) `detI_phiσ_ne_zero_of_first` — the reframed `lem:nonempt1`: for the ordering `τ`
  whose first `D = e+1` vertices are `I = {τ_1,…,τ_D}`, the general-position determinant
  of the `I`-vertices is NOT the zero polynomial.  A `MvPolynomial` is `≠ 0` iff some
  real evaluation is `≠ 0`; the greedy dimension-count of `lem:nonempt1` builds the
  evaluation point.
-/
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.LSS.Construction
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Data.Real.CompleteField
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.DotProduct

namespace LSS

open Matrix Finset

/-! ## (N1) — `crossMinors` is nonzero iff the columns are independent, and lands in
the (1-dimensional) orthogonal complement of the column span.

We work over `ℝ`. The `(e+1) × e` matrix `F` has `e` columns living in `ℝ^{e+1}`.
`crossMinors F : Fin (e+1) → ℝ` is the generalized cross product. Two facts drive
everything:

* `crossMinors_orthogonal` (already in `Construction`): each column of `F` dot-products
  to `0` with `crossMinors F` — i.e. `crossMinors F ⊥ span(columns)`.
* `crossMinors_ne_zero_of_indep`: when the `e` columns are linearly independent (so `F`
  has rank `e`, and the orthogonal complement of their span is 1-dimensional),
  `crossMinors F ≠ 0`.

Together: `crossMinors F` is a nonzero vector in the 1-dimensional complement, hence any
other complement vector `z` is a scalar multiple of it; rescaling one free column realizes
`z` exactly. -/

/-- The transpose-times-vector statement of "`z` is orthogonal to every column of `F`"
in the standard dot product: `∑ i, z i * F i c = 0` for every column `c`, i.e.
`vecMul z F = 0`. -/
theorem dotProduct_cols_eq_zero_iff {e : ℕ} (F : Matrix (Fin (e + 1)) (Fin e) ℝ)
    (z : Fin (e + 1) → ℝ) :
    (∀ c, ∑ i, z i * F i c = 0) ↔ Matrix.vecMul z F = 0 := by
  constructor
  · intro h; funext c; simpa [Matrix.vecMul, dotProduct] using h c
  · intro h c; have := congrFun h c; simpa [Matrix.vecMul, dotProduct] using this

/-- Local copy of the augmented `(e+1)×(e+1)` matrix (column `0` is `g`, columns `1..e`
are `F`); `Construction`'s `augment` is `private`. -/
private def augmentN {e : ℕ} (g : Fin (e + 1) → ℝ) (F : Matrix (Fin (e + 1)) (Fin e) ℝ) :
    Matrix (Fin (e + 1)) (Fin (e + 1)) ℝ :=
  Matrix.of (fun i => Fin.cons (g i) (F i))

/-- Laplace expansion of `det (augmentN g F)` along column `0`:
`det (augmentN g F) = ∑ i, g i * crossMinors F i`. -/
private lemma det_augmentN_eq {e : ℕ} (g : Fin (e + 1) → ℝ)
    (F : Matrix (Fin (e + 1)) (Fin e) ℝ) :
    (augmentN g F).det = ∑ i, g i * crossMinors F i := by
  rw [Matrix.det_succ_column_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsub : (augmentN g F).submatrix i.succAbove Fin.succ
      = F.submatrix i.succAbove id := by
    ext a b; simp [augmentN, Matrix.submatrix_apply]
  have h0 : (augmentN g F) i 0 = g i := rfl
  rw [hsub, h0, crossMinors]; ring

/-- The columns of `augmentN z F` are `Fin.cons z (cols F)`: column `0` is `z`,
column `c.succ` is column `c` of `F`. -/
private lemma augmentN_col {e : ℕ} (z : Fin (e + 1) → ℝ)
    (F : Matrix (Fin (e + 1)) (Fin e) ℝ) :
    (fun j => fun i => augmentN z F i j) = Fin.cons z (fun c i => F i c) := by
  funext j
  refine Fin.cases ?_ (fun c => ?_) j
  · funext i; rfl
  · funext i; simp [augmentN]

/-- **(N1) core: nonvanishing.** If the `e` columns of the `(e+1) × e` real matrix `F`
are linearly independent, then `crossMinors F ≠ 0`.

Reason (LSS "elementary linear algebra"): independent columns span an `e`-dimensional
subspace `S` of `ℝ^{e+1}`, whose orthogonal complement `Sᗮ` is 1-dimensional. The vector
`crossMinors F` lies in `Sᗮ` (`crossMinors_orthogonal`); were it `0`, the augmented
`(e+1)×(e+1)` matrix obtained by adjoining any complement vector would still be singular,
but a basis-completing vector makes it nonsingular — contradiction. Concretely: pick any
`z ⊥ S` with `z ≠ 0` (exists since `dim Sᗮ = 1 ≥ 1`); then `det (z | F) = ⟨z, crossMinors F⟩`
and `{z} ∪ columns` is a basis so this determinant is `≠ 0`, forcing `crossMinors F ≠ 0`. -/
theorem crossMinors_ne_zero_of_indep {e : ℕ} (F : Matrix (Fin (e + 1)) (Fin e) ℝ)
    (hF : LinearIndependent ℝ (fun c => (fun i => F i c) : Fin e → (Fin (e + 1) → ℝ))) :
    crossMinors F ≠ 0 := by
  -- Extend the `e` independent columns by one vector `z` to a basis of `ℝ^{e+1}`.
  have hfin : e < Module.finrank ℝ (Fin (e + 1) → ℝ) := by
    rw [Module.finrank_pi]; simp
  obtain ⟨z, hz⟩ := exists_linearIndependent_cons_of_lt_finrank hF hfin
  -- The square matrix `augmentN z F` has columns `Fin.cons z (cols F) = hz`'s family, so it
  -- is a unit, hence its determinant is nonzero.
  have hcols : LinearIndependent ℝ (augmentN z F).col := by
    have : (augmentN z F).col = Fin.cons z (fun c i => F i c) := by
      change (fun j => fun i => augmentN z F i j) = _
      exact augmentN_col z F
    rw [this]; exact hz
  have hunit : IsUnit (augmentN z F) := Matrix.linearIndependent_cols_iff_isUnit.1 hcols
  have hdet : (augmentN z F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 hunit).ne_zero
  -- But `det (augmentN z F) = ∑ i, z i * crossMinors F i`; if `crossMinors F = 0` the sum is `0`.
  intro hcm
  apply hdet
  rw [det_augmentN_eq]
  simp [hcm]

private theorem exists_linearIndependent_append_of_le_finrank {V : Type*} [AddCommGroup V]
    [Module ℝ V] [FiniteDimensional ℝ V] {n k : ℕ} {v : Fin n → V}
    (hv : LinearIndependent ℝ v) (h : n + k ≤ Module.finrank ℝ V) :
    ∃ x : Fin k → V, LinearIndependent ℝ (Fin.append v x) := by
  induction k with
  | zero =>
      refine ⟨Fin.elim0, ?_⟩
      simpa using hv
  | succ k ih =>
      have hle : n + k ≤ Module.finrank ℝ V := by omega
      obtain ⟨x, hx⟩ := ih hle
      have hlt : n + k < Module.finrank ℝ V := by omega
      obtain ⟨y, hy⟩ := exists_linearIndependent_snoc_of_lt_finrank hx hlt
      refine ⟨Fin.snoc x y, ?_⟩
      rw [Fin.append_snoc]
      exact hy

private lemma dot_kernel_parallel {n : ℕ} {z q : Fin n → ℝ} (hz : z ≠ 0)
    (hq : ∀ v : Fin n → ℝ, z ⬝ᵥ v = 0 → v ⬝ᵥ q = 0) :
    q = ((q ⬝ᵥ z) / (z ⬝ᵥ z)) • z := by
  have hzz : z ⬝ᵥ z ≠ 0 := by
    intro h
    exact hz (dotProduct_self_eq_zero.mp h)
  let a : ℝ := (q ⬝ᵥ z) / (z ⬝ᵥ z)
  let u : Fin n → ℝ := q - a • z
  have hzu : z ⬝ᵥ u = 0 := by
    simp [u, a, dotProduct_sub, dotProduct_smul, hzz, dotProduct_comm]
  have huq : u ⬝ᵥ q = 0 := hq u hzu
  have huz : u ⬝ᵥ z = 0 := by simpa [dotProduct_comm] using hzu
  have huu : u ⬝ᵥ u = 0 := by
    calc
      u ⬝ᵥ u = u ⬝ᵥ (q - a • z) := by simp [u]
      _ = u ⬝ᵥ q - u ⬝ᵥ (a • z) := by simp [dotProduct_sub]
      _ = 0 := by simp [huq, dotProduct_smul, huz]
  have hu0 : u = 0 := dotProduct_self_eq_zero.mp huu
  ext i
  have := congrFun hu0 i
  simp [u, a] at this ⊢
  linarith

/-- **(N1) — surjectivity onto the orthogonal complement.**
Given `m ≤ e` linearly independent columns `w : Fin m → ℝ^{e+1}` and ANY target
`z : ℝ^{e+1}` with `z ≠ 0` and `z` orthogonal (standard dot product) to every `w_i`,
there exist free columns `x : Fin (e - m) → ℝ^{e+1}` such that the full `(e+1) × e` matrix
`F = (w | x)` satisfies `crossMinors F = c • z` for some scalar `c ≠ 0` — i.e.
`crossMinors F` is a **nonzero multiple of the prescribed `z`**.

This is LSS tex:215-219 — "by varying the second factor, every vector orthogonal to the
span of `v_{i_1},…,v_{i_k}` can be obtained". The construction's scalar `y` then absorbs the
factor `c` (LSS sets `det(…) = 1`, i.e. `y = 1/c`); for the downstream
linear-independence argument a nonzero multiple of `z` is exactly as good as `z`.

Proof (SUFFICIENT version, LSS tex:217 "extend to a basis of `f(v)^⊥`"): the family
`Fin.snoc w z` is independent (`w` independent and `z ⊥ span w` with `z ≠ 0` ⟹ `z ∉ span w`).
Complete it to a basis of `ℝ^{e+1}` by `e - m` further vectors `x_1,…,x_{e-m}`; use them as
the free columns. Then `F = (w | x)` has the `e` independent columns `{w_i} ∪ {x_j}` (a
subset of the basis), so `crossMinors F ≠ 0` by `crossMinors_ne_zero_of_indep`, and it is
orthogonal to all of them (`crossMinors_orthogonal`); since `z` is also orthogonal to all of
them and the orthogonal complement of their `e`-dimensional span is 1-dimensional,
`crossMinors F` and `z` are parallel: `crossMinors F = c • z` with `c ≠ 0`
(as `crossMinors F ≠ 0`). -/
theorem crossMinors_surj_orthogonal {e m : ℕ} (hm : m ≤ e)
    (w : Fin m → (Fin (e + 1) → ℝ))
    (hw : LinearIndependent ℝ w)
    (z : Fin (e + 1) → ℝ) (hz : z ≠ 0)
    (hperp : ∀ j : Fin m, ∑ i, z i * w j i = 0) :
    ∃ (x : Fin (e - m) → (Fin (e + 1) → ℝ)) (c : ℝ), c ≠ 0 ∧
      crossMinors (Matrix.of fun (i : Fin (e + 1)) (cc : Fin e) =>
        if h : cc.val < m then w ⟨cc.val, h⟩ i
        else x ⟨cc.val - m, by omega⟩ i) = c • z := by
  classical
  let φ : (Fin (e + 1) → ℝ) →ₗ[ℝ] ℝ := dotProductBilin ℝ ℝ z
  let K : Submodule ℝ (Fin (e + 1) → ℝ) := LinearMap.ker φ
  have hzz : z ⬝ᵥ z ≠ 0 := by
    intro h
    exact hz (dotProduct_self_eq_zero.mp h)
  have hφsurj : Function.Surjective φ := by
    intro a
    refine ⟨(a / (z ⬝ᵥ z)) • z, ?_⟩
    simp [φ, dotProductBilin, hzz]
  have hfinKer : Module.finrank ℝ (LinearMap.ker φ) = e := by
    have hrank := LinearMap.finrank_range_add_finrank_ker φ
    have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.2 hφsurj
    rw [hrange, Module.finrank_pi] at hrank
    simp at hrank
    omega
  have hfinK : Module.finrank ℝ K = e := by
    simpa [K] using hfinKer
  let kw : Fin m → K := fun j => ⟨w j, by simpa [K, φ, dotProductBilin, dotProduct] using hperp j⟩
  have hwK : LinearIndependent ℝ kw := by
    apply LinearIndependent.of_comp K.subtype
    simpa [kw, K] using hw
  obtain ⟨xK, hxK⟩ := exists_linearIndependent_append_of_le_finrank
    (V := K) (k := e - m) hwK (by
    rw [hfinK]
    omega)
  let x : Fin (e - m) → (Fin (e + 1) → ℝ) := fun j => xK j
  let F : Matrix (Fin (e + 1)) (Fin e) ℝ :=
    Matrix.of fun i cc =>
      if h : cc.val < m then w ⟨cc.val, h⟩ i
      else x ⟨cc.val - m, by omega⟩ i
  let colsK : Fin e → K := fun cc =>
    ⟨(fun i => F i cc), by
      by_cases h : cc.val < m
      · simpa [F, K, φ, dotProductBilin, dotProduct, h] using hperp ⟨cc.val, h⟩
      · have : (fun i => F i cc) = x ⟨cc.val - m, by omega⟩ := by
          ext i
          simp [F, h]
        rw [this]
        exact (xK ⟨cc.val - m, by omega⟩).property⟩
  have hcolsK : LinearIndependent ℝ colsK := by
    have hme : m + (e - m) = e := Nat.add_sub_of_le hm
    refine (linearIndependent_equiv (finCongr hme)).1 ?_
    have hcomp : colsK ∘ (finCongr hme) = Fin.append kw xK := by
      funext cc
      refine Fin.addCases
        (motive := fun cc => colsK ((finCongr hme) cc) = Fin.append kw xK cc)
        (fun j => ?_) (fun j => ?_) cc
      · ext i
        simp [colsK, kw, F]
      · ext i
        simp [colsK, kw, F, x]
    rw [hcomp]
    exact hxK
  have hF : LinearIndependent ℝ
      (fun c => (fun i => F i c) : Fin e → (Fin (e + 1) → ℝ)) := by
    have := hcolsK.map' K.subtype (Submodule.ker_subtype K)
    simpa [colsK, K] using this
  let q : Fin (e + 1) → ℝ := crossMinors F
  have hq0 : q ≠ 0 := by
    simpa [q] using crossMinors_ne_zero_of_indep F hF
  have hspanK : Submodule.span ℝ (Set.range colsK) = ⊤ := by
    apply hcolsK.span_eq_top_of_card_eq_finrank'
    simp [hfinK]
  have hqker : ∀ v : Fin (e + 1) → ℝ, z ⬝ᵥ v = 0 → v ⬝ᵥ q = 0 := by
    intro v hv
    let vk : K := ⟨v, by simpa [K, φ, dotProductBilin] using hv⟩
    have hvspan : vk ∈ Submodule.span ℝ (Set.range colsK) := by
      rw [hspanK]
      exact Submodule.mem_top
    refine Submodule.span_induction (s := Set.range colsK)
      (p := fun y _ => ((y : K) : Fin (e + 1) → ℝ) ⬝ᵥ q = 0) ?_ ?_ ?_ ?_ hvspan
    · rintro y ⟨cc, rfl⟩
      simpa [colsK, q, dotProduct, mul_comm] using crossMinors_orthogonal F cc
    · simp [dotProduct]
    · intro y₁ y₂ hy₁ hy₂ hdot₁ hdot₂
      simp [hdot₁, hdot₂]
    · intro a y hy hdot
      simp [hdot]
  let c : ℝ := (q ⬝ᵥ z) / (z ⬝ᵥ z)
  have hqeq : q = c • z := by
    simpa [c, q] using dot_kernel_parallel (z := z) (q := q) hz hqker
  have hc : c ≠ 0 := by
    intro hc
    apply hq0
    rw [hqeq, hc]
    simp
  refine ⟨x, c, hc, ?_⟩
  simpa [F, q] using hqeq

/-! ## (N2) — `lem:nonempt1`: `det_I(φτ) ≠ 0` for the "I-placed-first" ordering.

Setup. Fix a graph `G` on `Fin n`, dimension `D = e + 1` with `D ≤ n`, and an ordering
`τ` of `[n]`. The `I`-vertices are the **first `D` vertices** of `τ`: the vertex at
position `a : Fin D` is `Ivtx τ a := τ ⟨a.val, …⟩`.

The general-position determinant of the `I`-vertices is the `D × D` polynomial
determinant whose row `a` is the `D`-vector `φτ(Ivtx a)`:
`detI G τ e := Matrix.det (Matrix.of fun a b => phiσ G τ e (Ivtx τ a) b)`.

Goal (`lem:nonempt1`, gorProof tex:525-537): `detI ≠ 0` as a `MvPolynomial`.

A `MvPolynomial` is `≠ 0` iff some real evaluation is `≠ 0` (`ne_zero_of_eval_ne_zero`).
Under a ring-hom evaluation `eval θ`, `det` commutes (`RingHom.map_det`), so it suffices to
produce a real point `θ` where the `D × D` real matrix
`realRow θ a b := eval θ (phiσ G τ e (Ivtx τ a) b)` has nonzero determinant — equivalently
its rows are linearly independent.

That real point is built by the greedy dimension-count of `lem:nonempt1` (gorProof tex:533-537),
which is where (N1) `crossMinors_surj_orthogonal` is consumed: at step `i ≤ D`, vertex `τ_i`
has `< D` preceding non-neighbours (because it has `< i ≤ D` predecessors *at all* — this is
why "I first" needs no connectivity), so its constraint complement has dimension
`D - m_i > (i-1) - m_i = ` dimension of the already-spanned part inside it, leaving room to
pick `φτ(τ_i)` independent of the previous rows; (N1) realizes that choice via free columns. -/

variable {n : ℕ}

/-- The vertex at position `a : Fin (e+1)` in the ordering `τ` (an `I`-vertex, given that
`I` is the first `D = e+1` vertices of `τ`). Requires `e + 1 ≤ n`. -/
def Ivtx (τ : Equiv.Perm (Fin n)) {e : ℕ} (hn : e + 1 ≤ n) (a : Fin (e + 1)) : Fin n :=
  τ ⟨a.val, lt_of_lt_of_le a.isLt hn⟩

/-- The `D × D` general-position polynomial determinant of the `I`-vertices (`I` = first
`D = e+1` vertices of `τ`): the determinant of the matrix whose row `a` is `φτ(Ivtx a)`. -/
noncomputable def detI (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (τ : Equiv.Perm (Fin n)) (e : ℕ) (hn : e + 1 ≤ n) : Poly n :=
  Matrix.det (Matrix.of fun (a b : Fin (e + 1)) => phiσ G τ e (Ivtx τ hn a) b)

/-- A `MvPolynomial` is nonzero as soon as one of its real evaluations is nonzero
(`eval θ` is a ring hom, so it sends `0` to `0`). -/
theorem ne_zero_of_eval_ne_zero {p : Poly n} (θ : Fin n × ℕ → ℝ)
    (h : MvPolynomial.eval θ p ≠ 0) : p ≠ 0 := by
  intro hp; exact h (by rw [hp]; simp)

/-- Evaluating the polynomial determinant `detI` at a real point `θ` equals the determinant
of the **real** matrix whose row `a` is `φτ(Ivtx a)` evaluated at `θ`. This is `RingHom.map_det`
for the ring hom `MvPolynomial.eval θ`. -/
theorem eval_detI (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (τ : Equiv.Perm (Fin n)) (e : ℕ) (hn : e + 1 ≤ n) (θ : Fin n × ℕ → ℝ) :
    MvPolynomial.eval θ (detI G τ e hn)
      = Matrix.det (Matrix.of fun (a b : Fin (e + 1)) =>
          MvPolynomial.eval θ (phiσ G τ e (Ivtx τ hn a) b)) := by
  rw [detI, RingHom.map_det]
  rfl

/-! ### Eval-commutation of the recursive `phiσ` construction.

`MvPolynomial.eval θ` is a ring hom, so it commutes with `crossMinors` (a polynomial
determinant in the matrix entries), the scalar `yVar v` (a single variable), and the
recursion. We package the resulting *real* recursion as `realPhi θ` and prove
`realPhi θ v = eval θ ∘ phiσ G τ e v`. -/

/-- The ring-hom `eval θ` commutes with `crossMinors`: it equals the cross product of the
entrywise-evaluated matrix. (`crossMinors F j = (-1)^j · det(submatrix)`, and `eval θ` is
a ring hom, so it pushes through `det`.) -/
theorem eval_crossMinors {d : ℕ} (θ : Fin n × ℕ → ℝ)
    (F : Matrix (Fin (d + 1)) (Fin d) (Poly n)) (j : Fin (d + 1)) :
    MvPolynomial.eval θ (crossMinors F j)
      = crossMinors (Matrix.of fun i k => MvPolynomial.eval θ (F i k)) j := by
  simp only [crossMinors, map_mul, map_pow, map_neg, map_one, RingHom.map_det]
  rfl

/-- The **real** recursive construction obtained by evaluating `phiσ` at a real point `θ`.
Same recursion as `phiσ`/`phiStep`, but over `ℝ`: at vertex `v`, the matrix `F_v` has the
already-built real vectors of the preceding non-neighbours as its first columns and the real
numbers `θ (v, fresh slot)` as its remaining columns, and
`realPhi θ v = θ(v,0) · crossMinors F_v`. -/
noncomputable def realPhi (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (τ : Equiv.Perm (Fin n)) (e : ℕ) (θ : Fin n × ℕ → ℝ) (v : Fin n) : Fin (e + 1) → ℝ :=
  fun i =>
    θ (v, 0) *
      crossMinors
        (Matrix.of fun (a : Fin (e + 1)) (j : Fin e) =>
          match (precList G τ v)[j.val]? with
          | some u =>
            if (τ.symm u).val < (τ.symm v).val then realPhi G τ e θ u a else 0
          | none => θ (v, 1 + (((j.val - (precList G τ v).length)) * (e + 1) + a.val))) i
  termination_by (τ.symm v).val
  decreasing_by
    -- the recursive call sits inside the guard `if (τ.symm u).val < (τ.symm v).val`,
    -- so the decreasing hypothesis is exactly that guard.
    assumption

/-- Unfolding equation for `realPhi` (pointwise in `i`). -/
theorem realPhi_eq (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (τ : Equiv.Perm (Fin n)) (e : ℕ) (θ : Fin n × ℕ → ℝ) (v : Fin n) (i : Fin (e + 1)) :
    realPhi G τ e θ v i =
        θ (v, 0) *
          crossMinors
            (Matrix.of fun (a : Fin (e + 1)) (j : Fin e) =>
              match (precList G τ v)[j.val]? with
              | some u =>
                if (τ.symm u).val < (τ.symm v).val then realPhi G τ e θ u a else 0
              | none => θ (v, 1 + (((j.val - (precList G τ v).length)) * (e + 1) + a.val))) i := by
  rw [realPhi.eq_def]

/-- **Eval-commutation.** Evaluating `phiσ` at a real point `θ` equals the real recursion
`realPhi θ`. Proved by strong recursion on the `τ`-position of `v`. -/
theorem eval_phiσ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (τ : Equiv.Perm (Fin n)) (e : ℕ) (θ : Fin n × ℕ → ℝ) (v : Fin n) :
    (fun i => MvPolynomial.eval θ (phiσ G τ e v i)) = realPhi G τ e θ v := by
  -- Strong recursion on `τ`-position.
  have hwf : ∀ p : ℕ, ∀ w : Fin n, (τ.symm w).val = p →
      (fun i => MvPolynomial.eval θ (phiσ G τ e w i)) = realPhi G τ e θ w := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      intro w hw
      funext i
      rw [phiσ_eq G τ e w, phiStep, realPhi_eq]
      simp only [yVar, map_mul, MvPolynomial.eval_X]
      congr 1
      rw [eval_crossMinors]
      congr 1
      funext a j
      simp only [Matrix.of_apply, phiMat, Matrix.of_apply]
      rcases hmatch : (precList G τ w)[j.val]? with _ | u
      · -- fresh column: `eval θ (freshVar …) = θ (w, slot)`
        simp only [freshVar, MvPolynomial.eval_X]
      · -- preceding-non-neighbour column carrying `phiσ u`.
        have hmem : u ∈ precList G τ w := by
          obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp hmatch
          exact List.getElem_mem h
        have huP : u ∈ precNonNbrσ G τ w := by
          have : u ∈ (precNonNbrσ G τ w).sort (· ≤ ·) := by simpa [precList] using hmem
          simpa using (Finset.mem_sort (· ≤ ·)).1 this
        have hlt : (τ.symm u).val < (τ.symm w).val := precNonNbrσ_lt G τ huP
        simp only [hlt, if_true]
        -- apply IH at `u` (strictly smaller `τ`-position).
        have := ih (τ.symm u).val (by rw [hw] at hlt; exact hlt) u rfl
        exact congrFun this a
  exact hwf (τ.symm v).val v rfl

/-! ### Locality of `eval θ (phiσ …)` in the variables.

`eval θ (phiσ G τ e v)` only reads the slots `(w, _)` of `θ` for vertices `w` with
`τ`-position `≤` that of `v`. Hence changing `θ` at the slots of a *strictly later* vertex
leaves the earlier evaluated vectors unchanged — the per-vertex-disjoint namespacing. -/

/-- If `θ₁` and `θ₂` agree on every slot `(w, _)` of every vertex `w` with `τ`-position
`≤ p`, then `realPhi θ₁ v = realPhi θ₂ v` for every `v` with `τ`-position `≤ p`. -/
theorem realPhi_congr (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (τ : Equiv.Perm (Fin n)) (e : ℕ) (θ₁ θ₂ : Fin n × ℕ → ℝ)
    (v : Fin n)
    (hagree : ∀ w : Fin n, (τ.symm w).val ≤ (τ.symm v).val → ∀ s : ℕ, θ₁ (w, s) = θ₂ (w, s)) :
    realPhi G τ e θ₁ v = realPhi G τ e θ₂ v := by
  have hwf : ∀ p : ℕ, ∀ w : Fin n, (τ.symm w).val = p →
      (∀ w' : Fin n, (τ.symm w').val ≤ p → ∀ s : ℕ, θ₁ (w', s) = θ₂ (w', s)) →
      realPhi G τ e θ₁ w = realPhi G τ e θ₂ w := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      intro w hw hag
      funext i
      rw [realPhi_eq, realPhi_eq]
      -- `θ₁ (w,0) = θ₂ (w,0)`
      rw [hag w (by omega) 0]
      congr 1
      congr 1
      funext a j
      simp only [Matrix.of_apply]
      rcases hmatch : (precList G τ w)[j.val]? with _ | u
      · -- fresh slot of `w`: agree.
        exact hag w (by omega) _
      · have hmem : u ∈ precList G τ w := by
          obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp hmatch
          exact List.getElem_mem h
        have huP : u ∈ precNonNbrσ G τ w := by
          have : u ∈ (precNonNbrσ G τ w).sort (· ≤ ·) := by simpa [precList] using hmem
          simpa using (Finset.mem_sort (· ≤ ·)).1 this
        have hlt : (τ.symm u).val < (τ.symm w).val := precNonNbrσ_lt G τ huP
        simp only [hlt, if_true]
        have heq := ih (τ.symm u).val (by rw [hw] at hlt; exact hlt) u rfl
          (fun w' hw' s => hag w' (by omega) s)
        exact congrFun heq a
  exact hwf (τ.symm v).val v rfl (fun w' hw' s => hagree w' hw' s)

/-! ### The greedy dimension count (gorProof tex:533-537).

Given `i < e+1` real vectors `p_0,…,p_{i-1} ∈ ℝ^{e+1}`, there is a nonzero `z ⊥ every p_k`
(`∑ a, z a * p_k a = 0`) and `z ∉ span(range p)`. This is the load-bearing inequality
`e + 1 > i`: the kernel of the `(e+1) → ℝ^i` "dot with each `p_k`" map has dimension
`≥ (e+1) - i ≥ 1`. The orthogonality then forces `z ∉ span(range p)` (else `z ⊥ z`). -/

/-- **Greedy escape vector.** For `i < e+1` real vectors `p : Fin i → ℝ^{e+1}` there is a
nonzero `z` orthogonal to every `p k` (standard dot product) and outside `span(range p)`. -/
theorem exists_perp_not_mem_span {e i : ℕ} (hie : i < e + 1)
    (p : Fin i → (Fin (e + 1) → ℝ)) :
    ∃ z : Fin (e + 1) → ℝ, z ≠ 0 ∧ (∀ k, ∑ a, z a * p k a = 0) ∧
      z ∉ Submodule.span ℝ (Set.range p) := by
  classical
  -- The "dot with each `p k`" linear map `L : ℝ^{e+1} → ℝ^i`.
  let L : (Fin (e + 1) → ℝ) →ₗ[ℝ] (Fin i → ℝ) :=
    { toFun := fun z k => ∑ a, z a * p k a
      map_add' := by
        intro x y; funext k; simp [Finset.sum_add_distrib, add_mul]
      map_smul' := by
        intro c x; funext k; simp [Finset.mul_sum, mul_assoc] }
  -- `dim (ker L) ≥ (e+1) - i ≥ 1`.
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  have hrange_le : Module.finrank ℝ (LinearMap.range L) ≤ i := by
    have : Module.finrank ℝ (LinearMap.range L) ≤ Module.finrank ℝ (Fin i → ℝ) :=
      Submodule.finrank_le _
    simpa using this
  have hdom : Module.finrank ℝ (Fin (e + 1) → ℝ) = e + 1 := by
    rw [Module.finrank_pi]; simp
  have hkerpos : 0 < Module.finrank ℝ (LinearMap.ker L) := by
    rw [hdom] at hrank; omega
  have hkerne : LinearMap.ker L ≠ ⊥ := by
    intro h
    rw [h] at hkerpos
    simp at hkerpos
  obtain ⟨z, hzmem, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hkerne
  have hperp : ∀ k, ∑ a, z a * p k a = 0 := by
    intro k
    have : L z = 0 := hzmem
    exact congrFun this k
  refine ⟨z, hz0, hperp, ?_⟩
  -- `z ⊥ every `p k` and `z ≠ 0` ⟹ `z ∉ span(range p)` (else `z ⊥ z`).
  intro hzspan
  apply hz0
  -- write `z` as a combination of the `p k`; then `z ⬝ z = ∑ c_k (z ⬝ p_k) = 0`.
  have hzz : (∑ a, z a * z a) = 0 := by
    refine Submodule.span_induction
      (p := fun y _ => (∑ a, z a * y a) = 0) ?_ ?_ ?_ ?_ hzspan
    · rintro y ⟨k, rfl⟩
      exact hperp k
    · simp
    · intro y₁ y₂ _ _ h₁ h₂
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, h₁, h₂, add_zero]
    · intro c y _ h
      have : (∑ a, z a * (c * y a)) = c * ∑ a, z a * y a := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => by ring
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [show (∑ x, z x * (c * y x)) = c * ∑ a, z a * y a from this, h, mul_zero]
  -- `∑ z a * z a = 0` over `ℝ` forces `z = 0`.
  funext a
  by_contra hza
  have hzane : z a ≠ 0 := hza
  have hpos : 0 < ∑ a, z a * z a := by
    apply Finset.sum_pos'
    · intro b _; exact mul_self_nonneg _
    · exact ⟨a, Finset.mem_univ a, mul_self_pos.mpr hzane⟩
  rw [hzz] at hpos
  exact lt_irrefl 0 hpos

/-- **The greedy real witness (the heart of `lem:nonempt1`, gorProof tex:533-537).**
There is a real evaluation point `θ` at which the `D = e+1` evaluated `I`-vertex vectors
`fun b => eval θ (φτ(Ivtx a) b)` (for `a : Fin (e+1)`) are linearly independent.

Built by induction on the position `i = 0,…,e`: maintaining independence of the first `i`
rows, at step `i` the preceding non-neighbours of `τ_i` number `m_i ≤ i ≤ e`, so their
span's orthogonal complement `K_i` has dimension `(e+1) - m_i`; the previously placed rows
contribute dimension `i - m_i` inside `K_i`; since `(e+1) - m_i > i - m_i` (⟺ `e + 1 > i`,
true for `i ≤ e`), `K_i ⊄ span(previous)`, so a fresh independent direction `z_i ∈ K_i`
exists, realized as `φτ(τ_i) = z_i` by (N1) `crossMinors_surj_orthogonal` (setting the free
columns and scalar `y_{τ_i} = 1` via the per-vertex-disjoint fresh variables of `θ`). -/
theorem exists_eval_linearIndependent_Ivtx (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (τ : Equiv.Perm (Fin n)) (e : ℕ) (hn : e + 1 ≤ n) :
    ∃ θ : Fin n × ℕ → ℝ,
      LinearIndependent ℝ
        (fun (a : Fin (e + 1)) => fun b => MvPolynomial.eval θ (phiσ G τ e (Ivtx τ hn a) b)) := by
  classical
  -- `τ`-position of the `a`-th `I`-vertex is `a.val`.
  have hpos : ∀ a : Fin (e + 1), (τ.symm (Ivtx τ hn a)).val = a.val := by
    intro a; simp [Ivtx]
  -- Reduce to linear independence of the **real** rows `realPhi θ (Ivtx a)` (via eval-commutation).
  suffices h : ∃ θ : Fin n × ℕ → ℝ,
      LinearIndependent ℝ (fun (a : Fin (e + 1)) => realPhi G τ e θ (Ivtx τ hn a)) by
    obtain ⟨θ, hθ⟩ := h
    refine ⟨θ, ?_⟩
    have : (fun (a : Fin (e + 1)) => fun b => MvPolynomial.eval θ (phiσ G τ e (Ivtx τ hn a) b))
        = (fun (a : Fin (e + 1)) => realPhi G τ e θ (Ivtx τ hn a)) := by
      funext a; exact eval_phiσ G τ e θ (Ivtx τ hn a)
    rw [this]; exact hθ
  -- **Greedy induction** on the prefix length `i ≤ e+1`.
  suffices haux : ∀ i : ℕ, ∀ hi : i ≤ e + 1,
      ∃ θ : Fin n × ℕ → ℝ,
        LinearIndependent ℝ
          (fun (a : Fin i) => realPhi G τ e θ (Ivtx τ hn (Fin.castLE hi a))) by
    obtain ⟨θ, hθ⟩ := haux (e + 1) le_rfl
    refine ⟨θ, ?_⟩
    have hcast : (fun (a : Fin (e + 1)) => realPhi G τ e θ (Ivtx τ hn (Fin.castLE le_rfl a)))
        = (fun (a : Fin (e + 1)) => realPhi G τ e θ (Ivtx τ hn a)) := by
      funext a; congr 1
    rw [hcast] at hθ; exact hθ
  intro i
  induction i with
  | zero =>
      intro _
      exact ⟨fun _ => 0, linearIndependent_empty_type⟩
  | succ i ih =>
      intro hi
      have hi' : i < e + 1 := by omega
      have hile : i ≤ e + 1 := by omega
      obtain ⟨θ, hθ⟩ := ih hile
      -- the new vertex (position `i`) and the previous rows.
      set v : Fin n := Ivtx τ hn ⟨i, hi'⟩ with hv
      set r : Fin i → (Fin (e + 1) → ℝ) :=
        fun a => realPhi G τ e θ (Ivtx τ hn (Fin.castLE hile a)) with hr
      -- escape vector `z ⊥ previous rows`, `z ∉ span(previous)`.
      obtain ⟨z, hz0, hzperp, hznotmem⟩ := exists_perp_not_mem_span hi' r
      -- the preceding non-neighbour columns of `v`.
      set len : ℕ := (precList G τ v).length with hlen
      -- `len = card precNonNbr v ≤ pos(v) = i ≤ e`.
      have hlencard : len = (precNonNbrσ G τ v).card := by
        rw [hlen]; unfold precList; rw [Finset.length_sort]
      -- every preceding non-neighbour has `τ`-position `< i`, hence `< e+1`.
      have hprec_pos : ∀ u ∈ precList G τ v, (τ.symm u).val < i := by
        intro u hu
        have huP : u ∈ precNonNbrσ G τ v := by
          have : u ∈ (precNonNbrσ G τ v).sort (· ≤ ·) := by simpa [precList] using hu
          simpa using (Finset.mem_sort (· ≤ ·)).1 this
        have := precNonNbrσ_lt G τ huP
        rw [hv, hpos] at this; simpa using this
      -- `len ≤ i ≤ e`: the non-neighbours all sit at positions `0..i-1`, so there are
      -- `≤ i ≤ e` of them (bound the card of `precNonNbr v`, all `τ`-positions `< i`).
      have hlen_le_i : len ≤ i := by
        rw [hlencard]
        -- inject `precNonNbr v` into `Finset.range i` via `u ↦ (τ.symm u).val`.
        have hsub : (precNonNbrσ G τ v).card ≤ (Finset.range i).card := by
          apply Finset.card_le_card_of_injOn (f := fun u => (τ.symm u).val)
          · intro u hu
            have huP : u ∈ precNonNbrσ G τ v := by simpa using hu
            have hmem : u ∈ precList G τ v := by
              unfold precList; rw [Finset.mem_sort]; exact huP
            simp only [Finset.coe_range, Set.mem_Iio]; exact hprec_pos u hmem
          · intro u₁ _ u₂ _ heq
            exact τ.symm.injective (Fin.eq_of_val_eq heq)
        simpa using hsub
      have hlen_le_e : len ≤ e := by omega
      -- the non-neighbour columns, as the previous-row family they really are.
      -- For `u = precList.get j`, `realPhi θ u = r ⟨pos u, _⟩`: `u` is a previous `I`-vertex.
      have hget_pos : ∀ j : Fin len, ((τ.symm ((precList G τ v).get j)).val) < i := by
        intro j; exact hprec_pos _ (List.get_mem _ _)
      -- the `r`-index of a non-neighbour column.
      set widx : Fin len → Fin i :=
        fun j => ⟨(τ.symm ((precList G τ v).get j)).val, hget_pos j⟩ with hwidx
      have hIvtx_get : ∀ j : Fin len,
          Ivtx τ hn (Fin.castLE hile (widx j)) = (precList G τ v).get j := by
        intro j
        change τ ⟨(τ.symm ((precList G τ v).get j)).val, _⟩ = (precList G τ v).get j
        have : (⟨(τ.symm ((precList G τ v).get j)).val, lt_of_lt_of_le
            (Fin.castLE hile (widx j)).isLt hn⟩ : Fin n) = τ.symm ((precList G τ v).get j) := by
          apply Fin.eq_of_val_eq; rfl
        rw [this, Equiv.apply_symm_apply]
      set w : Fin len → (Fin (e + 1) → ℝ) :=
        fun j => realPhi G τ e θ ((precList G τ v).get j) with hw
      have hw_eq_r : ∀ j : Fin len, w j = r (widx j) := by
        intro j; rw [hw, hr]; simp only; rw [hIvtx_get j]
      -- `w` independent (a reindexing of a subfamily of the independent `r`).
      have hwinj : Function.Injective widx := by
        intro j₁ j₂ heq
        simp only [hwidx, Fin.mk.injEq] at heq
        have : (precList G τ v).get j₁ = (precList G τ v).get j₂ :=
          τ.symm.injective (Fin.eq_of_val_eq heq)
        exact (List.nodup_iff_injective_get.1 (by
          unfold precList; exact Finset.sort_nodup _ _)) this
      have hwindep : LinearIndependent ℝ w := by
        have : w = r ∘ widx := by funext j; rw [hw_eq_r]; rfl
        rw [this]
        exact hθ.comp widx hwinj
      -- `z ⊥` each non-neighbour column.
      have hzperp_w : ∀ j : Fin len, ∑ a, z a * w j a = 0 := by
        intro j; rw [hw_eq_r]; exact hzperp (widx j)
      -- (N1) surjectivity: free columns `x` and a nonzero scale `c`, `crossMinors (w|x) = c • z`.
      obtain ⟨x, c, hc, hcross⟩ :=
        crossMinors_surj_orthogonal hlen_le_e w hwindep z hz0 hzperp_w
      -- **Define `θ'`**: `θ` with vertex `v`'s slots overwritten — scalar `y_v = 1` and the fresh
      -- columns set to `x`. Slot `1 + (k*(e+1) + ρ)` carries `x_k ρ` (decoded via `/`, `%`).
      set θ' : Fin n × ℕ → ℝ :=
        fun q =>
          if q.1 = v then
            (match q.2 with
             | 0 => 1
             | Nat.succ s =>
                 if h : s / (e + 1) < e - len then
                   x ⟨s / (e + 1), h⟩ ⟨s % (e + 1), Nat.mod_lt _ (by omega)⟩
                 else 0)
          else θ q with hθ'
      -- `θ'` only differs from `θ` at vertex `v` (position `i`), so it leaves earlier rows fixed.
      have hθ'_pos : (τ.symm v).val = i := by rw [hv, hpos]
      have hreal_fix : ∀ u : Fin n, (τ.symm u).val < i →
          realPhi G τ e θ' u = realPhi G τ e θ u := by
        intro u hu
        apply realPhi_congr
        intro w' hw' s
        -- `w'` has position `≤ pos u < i = pos v`, so `w' ≠ v`, so `θ' (w', s) = θ (w', s)`.
        have hw'ne : w' ≠ v := by
          intro h; rw [h, hθ'_pos] at hw'; omega
        rw [hθ']; simp only [hw'ne, if_false]
      -- the matrix of `realPhi θ' v` equals the (N1) matrix `(w | x)`.
      have hmateq : (Matrix.of fun (a : Fin (e + 1)) (j : Fin e) =>
            match (precList G τ v)[j.val]? with
            | some u =>
              if (τ.symm u).val < (τ.symm v).val then realPhi G τ e θ' u a else 0
            | none => θ' (v, 1 + (((j.val - (precList G τ v).length)) * (e + 1) + a.val)))
          = (Matrix.of fun (a : Fin (e + 1)) (cc : Fin e) =>
              if h : cc.val < len then w ⟨cc.val, h⟩ a
              else x ⟨cc.val - len, by omega⟩ a) := by
        funext a j
        simp only [Matrix.of_apply]
        by_cases hjlen : j.val < len
        · -- column inside `precList`: reads a previous non-neighbour row `w⟨j,_⟩`.
          have hsome : (precList G τ v)[j.val]? = some ((precList G τ v).get ⟨j.val, hjlen⟩) := by
            rw [List.getElem?_eq_getElem hjlen]; rfl
          rw [hsome]
          have hposu : (τ.symm ((precList G τ v).get ⟨j.val, hjlen⟩)).val < (τ.symm v).val := by
            rw [hθ'_pos]; exact hget_pos ⟨j.val, hjlen⟩
          simp only [hposu, if_true, hjlen, dif_pos]
          rw [hreal_fix _ (by rw [hθ'_pos] at hposu; exact hposu)]
        · -- fresh column: reads `θ'` at the decoded slot, which is `x⟨j-len,_⟩ a`.
          have hnone : (precList G τ v)[j.val]? = none := by
            rw [List.getElem?_eq_none_iff]; omega
          rw [hnone]
          simp only [hjlen, dif_neg, not_false_iff]
          -- decode `θ' (v, 1 + ((j-len)*(e+1)+a))`.
          rw [hθ']
          simp only [if_true]
          have hs : 1 + ((j.val - len) * (e + 1) + a.val)
              = Nat.succ ((j.val - len) * (e + 1) + a.val) := by omega
          rw [hs]
          have hdiv : ((j.val - len) * (e + 1) + a.val) / (e + 1) = j.val - len := by
            rw [add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < e + 1),
              Nat.div_eq_of_lt a.isLt, zero_add]
          have hmod : ((j.val - len) * (e + 1) + a.val) % (e + 1) = a.val := by
            rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a.isLt]
          -- the dite-condition holds: `j - len < e - len`.
          have hcond : ((j.val - len) * (e + 1) + a.val) / (e + 1) < e - len := by rw [hdiv]; omega
          change (if h : ((j.val - len) * (e + 1) + a.val) / (e + 1) < e - len then
                  x ⟨((j.val - len) * (e + 1) + a.val) / (e + 1), h⟩
                    ⟨((j.val - len) * (e + 1) + a.val) % (e + 1), Nat.mod_lt _ (by omega)⟩
                else 0) = x ⟨j.val - len, by omega⟩ a
          rw [dif_pos hcond]
          congr 1
          · exact Fin.ext hdiv
          · exact Fin.ext hmod
      -- Hence `realPhi θ' v = θ'(v,0) • crossMinors(w|x) = 1 • (c • z) = c • z`.
      have hθ'v0 : θ' (v, 0) = 1 := by rw [hθ']; simp
      have hrealv : realPhi G τ e θ' v = c • z := by
        funext bb
        rw [realPhi_eq]
        rw [hθ'v0, one_mul]
        have : (Matrix.of fun (a : Fin (e + 1)) (j : Fin e) =>
              match (precList G τ v)[j.val]? with
              | some u =>
                if (τ.symm u).val < (τ.symm v).val then realPhi G τ e θ' u a else 0
              | none => θ' (v, 1 + (((j.val - (precList G τ v).length)) * (e + 1) + a.val)))
            = (Matrix.of fun (a : Fin (e + 1)) (cc : Fin e) =>
                if h : cc.val < len then w ⟨cc.val, h⟩ a
                else x ⟨cc.val - len, by omega⟩ a) := hmateq
        rw [this, hcross]
      -- **Independence of the extended family** via `linearIndependent_fin_snoc`.
      refine ⟨θ', ?_⟩
      -- the new family on `Fin (i+1)` is `Fin.snoc (previous, fixed by θ') (realPhi θ' v)`.
      have hfam : (fun (a : Fin (i + 1)) => realPhi G τ e θ' (Ivtx τ hn (Fin.castLE hi a)))
          = Fin.snoc r (realPhi G τ e θ' v) := by
        funext a
        refine Fin.lastCases ?_ (fun a => ?_) a
        · -- last index `i`: the new vertex `v`.
          simp only [Fin.snoc_last]
          congr 1
        · -- earlier index: previous row, unchanged by `θ'` (via `hreal_fix`).
          rw [Fin.snoc_castSucc]
          show realPhi G τ e θ' (Ivtx τ hn (Fin.castLE hi a.castSucc)) = r a
          have hposlt : (τ.symm (Ivtx τ hn (Fin.castLE hi a.castSucc))).val < i := by
            rw [hpos]; simp [Fin.castLE]
          rw [hreal_fix _ hposlt, hr]
          congr 1
      rw [hfam]
      rw [linearIndependent_fin_snoc]
      refine ⟨hθ, ?_⟩
      -- `realPhi θ' v = c • z ∉ span(r)`, since `c ≠ 0` and `z ∉ span(r)`.
      rw [hrealv]
      intro hmem
      apply hznotmem
      have := Submodule.smul_mem _ (c⁻¹) hmem
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

/-- **(N2) — `lem:nonempt1` (Gortler–Theran, gorProof tex:525-537).**
For the ordering `τ` whose first `D = e+1` vertices are `I = {τ_1,…,τ_D}`, the
general-position determinant of the `I`-vertices is NOT the zero polynomial:
`detI G τ e ≠ 0`.

This is the "I-placed-first" non-vanishing base case: `GOR⁺_τ ∩ GP(I)` is non-empty because
the construction can place the `I`-vertices in general position (the witness real point
`θ` of `exists_eval_linearIndependent_Ivtx`), and a `MvPolynomial` with a nonvanishing
evaluation is itself nonzero.

Proof: evaluate at the greedy real witness `θ`; `eval_detI` turns the polynomial determinant
into the real determinant of the evaluated rows, which is `≠ 0` because those rows are
linearly independent; then `ne_zero_of_eval_ne_zero` lifts back to the polynomial. -/
theorem detI_phiσ_ne_zero_of_first (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (τ : Equiv.Perm (Fin n)) (e : ℕ) (hn : e + 1 ≤ n) :
    detI G τ e hn ≠ 0 := by
  obtain ⟨θ, hθ⟩ := exists_eval_linearIndependent_Ivtx G τ e hn
  refine ne_zero_of_eval_ne_zero θ ?_
  rw [eval_detI]
  -- The real matrix has linearly independent rows, so its determinant is nonzero.
  set A : Matrix (Fin (e + 1)) (Fin (e + 1)) ℝ :=
    Matrix.of fun (a b : Fin (e + 1)) =>
      MvPolynomial.eval θ (phiσ G τ e (Ivtx τ hn a) b) with hA
  -- `hθ : LinearIndependent ℝ (fun a => A a)` (the rows of `A`).
  -- Independent rows ⟹ `A` is a unit ⟹ `det A ≠ 0`.
  have hunit : IsUnit A := Matrix.linearIndependent_rows_iff_isUnit.1 hθ
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hunit
  exact hdet.ne_zero

end LSS
