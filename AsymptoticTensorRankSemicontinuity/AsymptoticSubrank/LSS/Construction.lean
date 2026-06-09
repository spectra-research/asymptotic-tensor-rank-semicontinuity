/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace LSS

open Matrix Finset

/-! ## C1 — The generalized cross product (vector of signed maximal minors)

We work over an arbitrary `CommRing R`, so the construction applies both to `ℝ` (for a
concrete OR) and to `MvPolynomial _ ℝ` (for the polynomial map `φσ`).

To avoid `d - 1` truncated-subtraction pain we state the matrix as `(d+1) × d`
(`Matrix (Fin (d+1)) (Fin d) R`); `crossMinors` then produces a vector in `Fin (d+1) → R`.
This matches LSS's `d × (d-1)` matrix with `d ↦ d+1`. -/

variable {R : Type*} [CommRing R]

/-- **C1.** The generalized cross product / vector of signed maximal minors of a
`(d+1) × d` matrix `F`. The `j`-th coordinate is the signed `d × d` minor obtained by
dropping row `j`:
`crossMinors F j = (-1)^j · det (F with row j dropped)`.

This is the LSS vector `(p_1,…,p_d)` (LSS tex:189) with the sign convention that makes the
Laplace cofactor expansion work out cleanly. -/
def crossMinors {d : ℕ} (F : Matrix (Fin (d + 1)) (Fin d) R) : Fin (d + 1) → R :=
  fun j => (-1) ^ (j : ℕ) * (F.submatrix j.succAbove id).det

/-- The augmented `(d+1) × (d+1)` matrix obtained by adjoining a column `g` as the new
column `0`, with the columns of `F` shifted to columns `1,…,d`. Its row `i` is
`Fin.cons (g i) (F i)`, so column `0` is `g` and column `j.succ` is column `j` of `F`. -/
private def augment {d : ℕ} (g : Fin (d + 1) → R) (F : Matrix (Fin (d + 1)) (Fin d) R) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) R :=
  Matrix.of (fun i => Fin.cons (g i) (F i))

omit [CommRing R] in
@[simp] private lemma augment_apply_zero {d : ℕ} (g : Fin (d + 1) → R)
    (F : Matrix (Fin (d + 1)) (Fin d) R) (i : Fin (d + 1)) :
    augment g F i 0 = g i := rfl

omit [CommRing R] in
@[simp] private lemma augment_apply_succ {d : ℕ} (g : Fin (d + 1) → R)
    (F : Matrix (Fin (d + 1)) (Fin d) R) (i : Fin (d + 1)) (j : Fin d) :
    augment g F i j.succ = F i j := by simp [augment]

/-- The cofactor (Laplace) expansion of `det (augment g F)` along its first column is exactly
`∑ i, g i * crossMinors F i`. This is `Matrix.det_succ_column_zero` rewritten through the
defining equations of `augment` and `crossMinors`. -/
private lemma det_augment_eq {d : ℕ} (g : Fin (d + 1) → R)
    (F : Matrix (Fin (d + 1)) (Fin d) R) :
    (augment g F).det = ∑ i, g i * crossMinors F i := by
  rw [Matrix.det_succ_column_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- `(-1)^i * (augment g F) i 0 * det (sub) = g i * crossMinors F i`
  have hsub : (augment g F).submatrix i.succAbove Fin.succ
      = F.submatrix i.succAbove id := by
    ext a b
    simp [Matrix.submatrix_apply]
  rw [hsub, augment_apply_zero, crossMinors]
  ring

/-- **C1 — the mathematical heart.** For every column `c` of the `(d+1) × d` matrix `F`,
the dot product of that column with `crossMinors F` vanishes:
`∑ i, (F i c) * crossMinors F i = 0`.

In particular, taking `F = (φ_{u_1},…,φ_{u_m},x_1,…,x_{d-1-m})` (LSS tex:186) and `c` the
index of a preceding non-neighbour `φ_u`, this says `φ_u ⊥ crossMinors F = (p_1,…,p_d)`,
i.e. `φ_u ⊥ φ_v` (LSS tex:191).

Proof (LSS "elementary linear algebra"): `∑ i, (F i c) * crossMinors F i` is the Laplace
cofactor expansion along column `0` of the `(d+1) × (d+1)` matrix `augment (F · c) F`, which
has its column `0` equal to its column `c.succ` (both are `F · c`), so its determinant is
`0` by `Matrix.det_zero_of_column_eq`. -/
theorem crossMinors_orthogonal {d : ℕ} (F : Matrix (Fin (d + 1)) (Fin d) R) (c : Fin d) :
    ∑ i, (F i c) * crossMinors F i = 0 := by
  have hcol : (augment (fun i => F i c) F).det = 0 := by
    apply Matrix.det_zero_of_column_eq (i := (0 : Fin (d + 1))) (j := c.succ)
    · exact (Fin.succ_ne_zero c).symm
    · intro k
      simp
  rw [← det_augment_eq] at *
  -- `det_augment_eq` with `g = F · c` gives the sum = det = 0
  simpa using hcol

/-! ## C2 — The recursive determinant-based polynomial map `φσ`

We fix a graph `G` on `Fin n`, a dimension parameter so that each `φ_v` lives in `Fin d → R`
(here `d` plays the role of LSS's `d`; the matrix `F` is `d × (d-1)`, i.e. we use the
`(d-1)+1 = d` shape, requiring `d = D` with `D ≥ 1`, written `d = e + 1`).

### Variable-indexing scheme

The polynomial ring is `MvPolynomial (Fin n × ℕ) ℝ`: a fresh variable is indexed by a pair
`(vertex, slot)`. For vertex `v` we use:
* slots `(v, 0)` — the scalar `y_v` (LSS tex:189);
* slots `(v, 1 + (k * d + r))` — the `r`-th coordinate of the `k`-th fresh column `x_{k+1}`
  (LSS tex:186), for `k` ranging over the fresh columns and `r : Fin d`.

Because slots are namespaced by vertex, different vertices never share a variable, so we
never have to compute the exact total parameter count `N` — exactly the freedom LSS notes:
"the number of these variables does not matter" (LSS tex:180).

We assemble the matrix `F_v : (Fin d) × (Fin (d-1))` whose first `|P_v|` columns are the
already-built `φ_u` (`u ∈ P_v`, the preceding non-neighbours in `σ`-order) and whose
remaining columns are fresh free variables `x`. Then `φ_v = y_v · crossMinors F_v`. -/

open MvPolynomial

variable {n : ℕ}

/-- The polynomial ring carrying the fresh variables of the construction.
Variables are indexed by `(vertex, slot)` pairs (see the module docstring). -/
abbrev Poly (n : ℕ) := MvPolynomial (Fin n × ℕ) ℝ

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (σ : Equiv.Perm (Fin n))

/-- The **preceding non-neighbours of `v` in the order `σ`** (LSS/GOR tex:177): the vertices
`u` that come strictly before `v` in the ordering `σ` and are not adjacent to `v`. We index
them by their `σ`-position `j : Fin n` with `(σ.symm v's position)` strictly larger.

Concretely a vertex `u` is a preceding non-neighbour of `v` iff
`σ.symm u < σ.symm v` and `¬ G.Adj v u`. -/
def precNonNbrσ (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => (σ.symm u).val < (σ.symm v).val ∧ ¬ G.Adj v u)

@[simp] theorem mem_precNonNbrσ {v u : Fin n} :
    u ∈ precNonNbrσ G σ v ↔ (σ.symm u).val < (σ.symm v).val ∧ ¬ G.Adj v u := by
  simp [precNonNbrσ]

/-- A preceding non-neighbour comes strictly earlier in `σ`, so recursion on `σ`-position
terminates. -/
theorem precNonNbrσ_lt {v u : Fin n} (hu : u ∈ precNonNbrσ G σ v) :
    (σ.symm u).val < (σ.symm v).val := (mem_precNonNbrσ G σ).1 hu |>.1

/-- The non-neighbours of `v` are linearly ordered by their `σ`-position; we enumerate
`precNonNbrσ G σ v` as a list sorted by `σ`-position so we can address them as the columns
`0,1,…,|P_v|-1` of `F_v`. -/
noncomputable def precList (v : Fin n) : List (Fin n) :=
  letI : LinearOrder (Fin n) := LinearOrder.lift' (fun w => (σ.symm w).val) (by
    intro a b h; exact σ.symm.injective (Fin.eq_of_val_eq h))
  (precNonNbrσ G σ v).sort (· ≤ ·)

/-- The fresh free-variable building block: the `r`-th coordinate of the `k`-th fresh column
`x_{k+1}` for vertex `v` is the monomial variable `X (v, 1 + (k * d + r))`. -/
noncomputable def freshVar (d : ℕ) (v : Fin n) (k : ℕ) (r : Fin d) : Poly n :=
  MvPolynomial.X (v, 1 + (k * d + r.val))

/-- The scalar `y_v` for vertex `v` (LSS tex:189): the variable `X (v, 0)`. -/
noncomputable def yVar (v : Fin n) : Poly n := MvPolynomial.X (v, 0)

/-- **C2 — the recursive polynomial representation `φσ`.**

`phiσ G σ d v : Fin d → Poly n` is the polynomial vector assigned to vertex `v`. It is
defined by strong recursion on the `σ`-position `(σ.symm v).val`:

* assemble the `d × d` matrix `F_v` whose column `j` (for `j : Fin d`) is:
  * the already-built `φσ G σ d u` for the `j`-th preceding non-neighbour `u = (precList v)[j]`,
    if `j < |P_v|`;
  * the fresh free column `x_{j-|P_v|}` (coordinates `freshVar d v (j-|P_v|)`) otherwise;
* set `φσ G σ d v = y_v · crossMinors F_v` (LSS tex:186-189).

(Note: LSS use a `d × (d-1)` matrix and `m ≤ d-1` non-neighbours; we use the `d × d`
column convention `crossMinors` is stated for and drop the last column by *never indexing
it from `crossMinors`*. To match LSS faithfully we pass the `d × (d-1)`-shaped data by
filling exactly `d-1` columns and reading `crossMinors` of the resulting `((d-1)+1) × (d-1)`
matrix. See `phiMat` below for the precise shape.) -/
noncomputable def phiMat (e : ℕ) (φ : Fin n → Fin (e + 1) → Poly n) (v : Fin n) :
    Matrix (Fin (e + 1)) (Fin e) (Poly n) :=
  Matrix.of fun (i : Fin (e + 1)) (j : Fin e) =>
    match (precList G σ v)[j.val]? with
    | some u => φ u i
    | none   => freshVar (e + 1) v (j.val - (precList G σ v).length) i

/-- The single-step construction of `φ_v` from already-built `φ_u`'s (LSS tex:186-189):
given the family `φ` of previously assigned polynomial vectors, `φ_v = y_v · crossMinors F_v`
where `F_v = phiMat`. -/
noncomputable def phiStep (e : ℕ) (φ : Fin n → Fin (e + 1) → Poly n) (v : Fin n) :
    Fin (e + 1) → Poly n :=
  fun i => yVar v * crossMinors (phiMat G σ e φ v) i

/-- The recursive `φσ`, by strong recursion on `σ`-position. `d = e + 1` is the dimension
(LSS's `d`, `D ≥ 1`). -/
noncomputable def phiσ (e : ℕ) (v : Fin n) : Fin (e + 1) → Poly n :=
  phiStep G σ e
    (fun u => if (σ.symm u).val < (σ.symm v).val then phiσ e u else fun _ => 0) v
  termination_by (σ.symm v).val
  decreasing_by assumption

/-! ### The OR property of `φσ`

The key identity: for distinct non-adjacent `u v`, `∑ i, (φσ u i) * (φσ v i) = 0`.

Strategy (LSS tex:191). WLOG `u` precedes `v` in `σ` (otherwise swap). Then `u ∈ P_v`, so
`φσ u` is a column of `v`'s matrix `F_v = phiMat`. The orthogonality
`∑ i, (F_v i c) * crossMinors (F_v) i = 0` (`crossMinors_orthogonal`, C1) gives the result,
and the scalar `y_v` factors out:
`∑ i, (φσ u i) * (φσ v i) = ∑ i, (φσ u i) * (y_v · crossMinors F_v i)
   = y_v · ∑ i, (F_v i c) * crossMinors F_v i = y_v · 0 = 0`.

The "`u ∈ P_v ⟹ φσ u is column c of F_v`" step needs that `precList v` actually lists `u`
at some index `c < length`, and that at that index `phiMat` reads off `φσ u` (the guard
`(σ.symm u).val < (σ.symm v).val` in `phiσ`'s self-reference fires because `u ∈ P_v`).
The bridge reduces the dot-product statement to `crossMinors_orthogonal`. -/

/-- Unfolding `phiσ` one step: `phiσ G σ e v = phiStep` of the previously assigned vectors,
where a previous vector `φσ u` is read for `u` strictly earlier than `v`, and `0` otherwise.
This is the definitional equation produced by the well-founded recursion. -/
theorem phiσ_eq (e : ℕ) (v : Fin n) :
    phiσ G σ e v =
      phiStep G σ e
        (fun u => if (σ.symm u).val < (σ.symm v).val then phiσ G σ e u else fun _ => 0) v := by
  rw [phiσ]

/-- **Bridging lemma.** If `u` is a preceding non-neighbour of `v`
(`u ∈ precNonNbrσ G σ v`) then the polynomial dot product `∑ i, φσ u i * φσ v i` is `0`.

This is the LSS "`φ_u ⊥ φ_v`" step (LSS tex:191) reduced to C1. The reduction:
`φσ v i = y_v · crossMinors (phiMat … v) i`, and because `u ∈ P_v` the vertex `u` appears in
`precList G σ v` at some index `c`, so column `c` of `phiMat G σ e φ v` is `φσ u`
(the self-reference guard `(σ.symm u).val < (σ.symm v).val` fires since `u ∈ P_v`). Hence

`∑ i, φσ u i * φσ v i = ∑ i, φσ u i * (y_v · crossMinors F i)
   = y_v * ∑ i, (F i c) * crossMinors F i = y_v * 0 = 0`

by `crossMinors_orthogonal` (C1).

The hypothesis `hcard : (precNonNbrσ G σ v).card ≤ e` is LSS's `m ≤ d-1` (LSS tex:186):
the number of preceding non-neighbours fits in the `d-1 = e` non-`y` columns of `F_v`. It is
needed so that `u`'s position `idxOf u (precList v) < length = card ≤ e` is an actual column
index `c : Fin e`. (Without it the claim is false, e.g. `e = 0` with `v` having a preceding
non-neighbour leaves `Fin e` empty.) The index bookkeeping reconciling
`precList`/`Finset.sort`/`List.getElem?` against the recursion guard matches the
mathematical content `crossMinors_orthogonal`. -/
theorem phiσ_dot_zero_of_prec (e : ℕ) {u v : Fin n}
    (huP : u ∈ precNonNbrσ G σ v) (hcard : (precNonNbrσ G σ v).card ≤ e) :
    ∑ i, (phiσ G σ e u i) * (phiσ G σ e v i) = 0 := by
  -- Abbreviate the previously-assigned family used inside `phiσ v`.
  set φprev : Fin n → Fin (e + 1) → Poly n :=
    (fun w => if (σ.symm w).val < (σ.symm v).val then phiσ G σ e w else fun _ => 0) with hφprev
  set F : Matrix (Fin (e + 1)) (Fin e) (Poly n) := phiMat G σ e φprev v with hF
  -- Unfold `φσ v` to `y_v · crossMinors F`.
  have hvstep : ∀ i, phiσ G σ e v i = yVar v * crossMinors F i := by
    intro i
    rw [phiσ_eq G σ e v, phiStep]
  -- `u ∈ P_v` appears at column `c = idxOf u (precList v)` of `phiMat`, carrying `φσ u`.
  -- `precList G σ v` lists `precNonNbrσ G σ v` (`Finset.mem_sort`), so `u` is in it at index
  -- `idxOf u < length = card ≤ e`. At that column `phiMat` reads `precList[idxOf u]? = some u`
  -- (`List.getElem?_eq_getElem` + `List.getElem_idxOf`), giving `φprev u i`; the recursion guard
  -- `(σ.symm u).val < (σ.symm v).val` fires (`precNonNbrσ_lt`), so `φprev u = phiσ G σ e u`.
  obtain ⟨c, hc⟩ : ∃ c : Fin e, ∀ i, F i c = phiσ G σ e u i := by
    have hmem : u ∈ precList G σ v := by
      unfold precList; rw [Finset.mem_sort]; exact huP
    have hlen : (precList G σ v).length = (precNonNbrσ G σ v).card := by
      unfold precList; rw [Finset.length_sort]
    have hidx : (precList G σ v).idxOf u < (precList G σ v).length :=
      List.idxOf_lt_length_of_mem hmem
    have hlt : (precList G σ v).idxOf u < e := by rw [hlen] at hidx; omega
    refine ⟨⟨(precList G σ v).idxOf u, hlt⟩, fun i => ?_⟩
    have hget : (precList G σ v)[(precList G σ v).idxOf u] = u :=
      List.getElem_idxOf hidx
    simp only [hF, phiMat, Matrix.of_apply]
    rw [List.getElem?_eq_getElem hidx, hget]
    change φprev u i = phiσ G σ e u i
    rw [hφprev]
    have hguard : (σ.symm u).val < (σ.symm v).val := precNonNbrσ_lt G σ huP
    simp [hguard]
  -- The product, pull out `φσ v`'s shape, then factor `y_v` and the cross-product sum.
  calc
    ∑ i, (phiσ G σ e u i) * (phiσ G σ e v i)
        = ∑ i, (phiσ G σ e u i) * (yVar v * crossMinors F i) := by
          refine Finset.sum_congr rfl fun i _ => ?_; rw [hvstep]
    _ = yVar v * ∑ i, (phiσ G σ e u i) * crossMinors F i := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
    _ = yVar v * ∑ i, (F i c) * crossMinors F i := by
          refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
          rw [hc i]
    _ = yVar v * 0 := by rw [crossMinors_orthogonal]
    _ = 0 := by ring

/-- **C2 — headline: `φσ` always produces an OR.**
For distinct non-adjacent vertices `u v` the polynomial dot product
`∑ i, (φσ u i) * (φσ v i)` is identically `0`.

This is LSS Theorem 2.1's "`φ_u · φ_v` is identically 0 whenever `u,v` nonadjacent"
(LSS tex:180, 191) / GOR "This construction always produces an OR of `G`" (gorProof tex:186).

Proof follows the strategy above. The bridging step — that a preceding non-neighbour
`u ∈ P_v` appears as a column of `phiMat G σ e φ v` carrying `φσ u`, reducing the dot product
to `crossMinors_orthogonal`, is `phiσ_dot_zero_of_prec`.

The hypotheses `hcardv`/`hcardu` are LSS's `m ≤ d-1` bound (LSS tex:186): each vertex's count
of preceding non-neighbours fits in the `d-1 = e` non-`y` columns of its matrix `F`. -/
theorem phiσ_isOR_poly (e : ℕ) {u v : Fin n} (huv : u ≠ v) (hadj : ¬ G.Adj v u)
    (hadj' : ¬ G.Adj u v)
    (hcardv : (precNonNbrσ G σ v).card ≤ e) (hcardu : (precNonNbrσ G σ u).card ≤ e) :
    ∑ i, (phiσ G σ e u i) * (phiσ G σ e v i) = 0 := by
  -- WLOG `u` precedes `v` in `σ`. Since `σ.symm` is injective and `u ≠ v`, the positions differ.
  rcases lt_or_gt_of_ne
      (show (σ.symm u).val ≠ (σ.symm v).val from fun h => huv (by
        have := Fin.eq_of_val_eq h; exact σ.symm.injective this)) with hlt | hgt
  · -- `u` precedes `v`: `u ∈ P_v`.
    have huP : u ∈ precNonNbrσ G σ v := (mem_precNonNbrσ G σ).2 ⟨hlt, hadj⟩
    exact phiσ_dot_zero_of_prec G σ e huP hcardv
  · -- `v` precedes `u`: symmetric.
    have hvP : v ∈ precNonNbrσ G σ u := (mem_precNonNbrσ G σ).2 ⟨hgt, hadj'⟩
    have := phiσ_dot_zero_of_prec G σ e hvP hcardu
    -- `∑ i, φσ v i * φσ u i = 0`; commute the product.
    simpa [mul_comm] using this

end LSS
