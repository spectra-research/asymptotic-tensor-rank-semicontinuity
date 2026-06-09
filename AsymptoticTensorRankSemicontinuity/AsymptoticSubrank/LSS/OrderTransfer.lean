/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# LSS order-transfer infrastructure

This file formalizes the order-transfer infrastructure in the
Lovász–Saks–Schrijver / Gortler–Theran argument. The goal of order-transfer is to show that
`det_I(φσ) ≢ 0` is INDEPENDENT of the construction ordering `σ`. We formalize this
via an equivalence relation `Transfers` on orderings — "the pullback kernels of the
two constructions agree" — and prove its **edge-swap base case** (`lem:edgeCon`).

# Sources

* **Gortler–Theran**, `GOR-LSS-2310.11565-gorProof.tex` lines 365-380 (`lem:edgeCon`,
  "Base Case 2"):

  > "Suppose that `σ` and `τ` are two orderings on `[n]` so that `σ_j = τ_j` for all
  >  `j ∈ [n] ∖ {i, i+1}`, `σ_{i+1} = τ_i`, `σ_i = τ_{i+1}`, and that `{σ_i, σ_{i+1}}`
  >  is an edge of `G`. Then `GOR⁺_σ = GOR⁺_τ`." (gorProof tex:365-380)

  (Proof idea: when `{σ_i, σ_{i+1}}` is an edge, the placement constraints on the
  `i`-th and `(i+1)`-st vertices are independent of each other, and the rest of the
  ordering is shared, so both runs produce the same `GOR⁺`.)

  The EDGE hypothesis is essential: when `{σ_i, σ_{i+1}}` is an edge, neither swapped
  vertex is a *preceding non-neighbour* of the other (they are ADJACENT, hence excluded
  from each other's `precNonNbrσ`), so swapping their two positions leaves every
  vertex's preceding-non-neighbour SET unchanged. The non-adjacent case is the harder
  `lem:later` (gorProof tex:396-…), which is NOT this brick.

# Contents

* `Transfers G e σ τ` — the transfer relation: the pullback kernels of the two
  constructions `phiσ G σ` and `phiσ G τ` agree (same vanishing ideal of the image =
  same Zariski closure). Reflexive / symmetric / transitive (`Transfers.refl/symm/trans`).
* `Transfers.detI_ne_zero` — the key consequence: if
  `Transfers G e σ τ` and the ambient `D × D` determinant pulls back nonzero under `τ`,
  then it pulls back nonzero under `σ`.
* `transfers_of_phiσ_eq` — pointwise construction-equality ⟹ `Transfers` (trivial bridge).
* `transfers_of_rename` — an ambient variable relabeling intertwining the two
  constructions ⟹ `Transfers` (via `MvPolynomial.aeval_rename`).
* `transfers_of_edge_swap` — `lem:edgeCon`: an edge swap of two adjacent vertices at
  positions `i, i+1` gives `Transfers`.
-/
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.LSS.Construction
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Analysis.InnerProductSpace.Basic

namespace LSS

open MvPolynomial

variable {n : ℕ}

/-! ## The ambient `(vertex, coord)`-indexed polynomial ring and the construction pullback.

The construction `phiσ G σ e v : Fin (e+1) → Poly n` assigns each vertex `v` a `D = e+1`
vector of polynomials in `Poly n = MvPolynomial (Fin n × ℕ) ℝ` (the FRESH-variable ring).

The **ambient** ring is `MvPolynomial (Fin n × Fin (e+1)) ℝ`: one variable `X (v, c)` per
*output coordinate* `(vertex v, coord c)`. The construction induces an `ℝ`-algebra hom
(the pullback) `ambPull G σ e : MvPolynomial (Fin n × Fin (e+1)) ℝ →ₐ[ℝ] Poly n` sending
`X (v, c) ↦ phiσ G σ e v c`. Its KERNEL is the vanishing ideal of the image `GOR⁺_σ(G)`;
equality of kernels = equality of Zariski closures of the two images. -/

/-- The pullback substitution underlying the construction `phiσ G σ`: substitute the
ambient output-coordinate variable `X (v, c)` by the polynomial `phiσ G σ e v c`. -/
noncomputable def ambSub (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Equiv.Perm (Fin n)) (e : ℕ) : (Fin n × Fin (e + 1)) → Poly n :=
  fun q => phiσ G σ e q.1 q.2

/-- **The transfer relation.** Two orderings `σ`, `τ` *transfer* (for the
graph `G` and dimension `D = e+1`) when the pullback kernels of their constructions agree:
for every ambient polynomial `p : MvPolynomial (Fin n × Fin (e+1)) ℝ`,
`aeval (ambSub G σ e) p = 0 ↔ aeval (ambSub G τ e) p = 0`.

Equivalently the two images `GOR⁺_σ(G)`, `GOR⁺_τ(G)` have the same vanishing ideal, hence
the same Zariski closure. This is exactly what `lem:edgeCon` (gorProof tex:365-380) asserts
in the form `GOR⁺_σ = GOR⁺_τ`, transported to the kernel level. -/
def Transfers (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (e : ℕ)
    (σ τ : Equiv.Perm (Fin n)) : Prop :=
  ∀ p : MvPolynomial (Fin n × Fin (e + 1)) ℝ,
    (MvPolynomial.aeval (ambSub G σ e) p = 0) ↔ (MvPolynomial.aeval (ambSub G τ e) p = 0)

namespace Transfers

variable {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {e : ℕ}

/-- `Transfers` is reflexive (it is a `∀ p, Iff` of a statement with itself). -/
@[refl] theorem refl (σ : Equiv.Perm (Fin n)) : Transfers G e σ σ :=
  fun _ => Iff.rfl

/-- `Transfers` is symmetric. -/
@[symm] theorem symm {σ τ : Equiv.Perm (Fin n)} (h : Transfers G e σ τ) :
    Transfers G e τ σ :=
  fun p => (h p).symm

/-- `Transfers` is transitive. -/
theorem trans {σ τ ρ : Equiv.Perm (Fin n)} (h₁ : Transfers G e σ τ)
    (h₂ : Transfers G e τ ρ) : Transfers G e σ ρ :=
  fun p => (h₁ p).trans (h₂ p)

end Transfers

/-- `Transfers` is an equivalence relation (bundled form, for `Setoid`/`Quotient` use). -/
theorem transfers_equivalence (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (e : ℕ) :
    Equivalence (Transfers G e) :=
  ⟨Transfers.refl, Transfers.symm, Transfers.trans⟩

/-! ## The key consequence: nonvanishing transfers across `Transfers`.

`Transfers.detI_ne_zero` is the instance of the relation at `p = `(the ambient determinant
polynomial). It is what consumes `NonEmpty.detI_phiσ_ne_zero_of_first`: if the construction
that places `I` first (the ordering `τ`) has nonzero pullback determinant, then so does any
ordering `σ` related to `τ` by a chain of edge-swaps. -/

/-- **Key consequence (the `Transfers` payload).** If `Transfers G e σ τ` and an ambient
polynomial `p` pulls back NONZERO under `τ`, then it pulls back nonzero under `σ`.

The intended `p` is the ambient `D × D` general-position determinant of the `I`-vertices
(`detI` lifted to the ambient `(vertex, coord)` ring); the τ-side nonvanishing is supplied by
`NonEmpty.detI_phiσ_ne_zero_of_first`. -/
theorem Transfers.pullback_ne_zero {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {e : ℕ}
    {σ τ : Equiv.Perm (Fin n)} (h : Transfers G e σ τ)
    {p : MvPolynomial (Fin n × Fin (e + 1)) ℝ}
    (hτ : MvPolynomial.aeval (ambSub G τ e) p ≠ 0) :
    MvPolynomial.aeval (ambSub G σ e) p ≠ 0 :=
  fun hσ => hτ ((h p).1 hσ)

/-- **The ambient general-position determinant polynomial.** Its variable `X (Iv a, b)` is the
`b`-th output coordinate of the `a`-th `I`-vertex `Iv a`; the determinant of this matrix is the
ambient lift of `NonEmpty.detI`. `aeval (ambSub G σ e)` sends it to the concrete `detI G σ e`. -/
noncomputable def ambDetI (e : ℕ) (Iv : Fin (e + 1) → Fin n) :
    MvPolynomial (Fin n × Fin (e + 1)) ℝ :=
  Matrix.det (Matrix.of fun (a b : Fin (e + 1)) => MvPolynomial.X (Iv a, b))

/-- The pullback of the ambient determinant `ambDetI` under the construction `phiσ G σ` is the
concrete construction determinant `det (φσ(Iv a) b)`. (`aeval` is a ring hom, so it commutes
with `Matrix.det`; `aeval_X` evaluates each variable.) -/
theorem aeval_ambDetI {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {e : ℕ}
    (σ : Equiv.Perm (Fin n)) (Iv : Fin (e + 1) → Fin n) :
    MvPolynomial.aeval (ambSub G σ e) (ambDetI e Iv)
      = Matrix.det (Matrix.of fun (a b : Fin (e + 1)) => phiσ G σ e (Iv a) b) := by
  rw [ambDetI, AlgHom.map_det]
  congr 1
  ext a b
  simp [ambSub]

/-- **`Transfers.detI_ne_zero` (the named payload).** If `Transfers G e σ τ` and the concrete
construction determinant of the `I`-vertices is nonzero under `τ`, then it is nonzero under `σ`.

This is `Transfers.pullback_ne_zero` specialized to `p = ambDetI e Iv`, with the pullbacks
rewritten through `aeval_ambDetI` into the concrete `Matrix.det (φ·(Iv a) b)` form used by
`NonEmpty.detI`. -/
theorem Transfers.detI_ne_zero {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {e : ℕ}
    {σ τ : Equiv.Perm (Fin n)} (h : Transfers G e σ τ) (Iv : Fin (e + 1) → Fin n)
    (hτ : Matrix.det (Matrix.of fun (a b : Fin (e + 1)) => phiσ G τ e (Iv a) b) ≠ 0) :
    Matrix.det (Matrix.of fun (a b : Fin (e + 1)) => phiσ G σ e (Iv a) b) ≠ 0 := by
  have hτ' : MvPolynomial.aeval (ambSub G τ e) (ambDetI e Iv) ≠ 0 := by
    rw [aeval_ambDetI]; exact hτ
  have hσ' := h.pullback_ne_zero hτ'
  rwa [aeval_ambDetI] at hσ'

/-! ## Bridges into `Transfers`.

Two general routes to establish `Transfers G e σ τ`:
* `transfers_of_phiσ_eq` — the two constructions are pointwise EQUAL (`ambSub` functions
  coincide), so the two `aeval` algebra-homs are literally the same map: `Transfers` is
  reflexivity-up-to-`congr`. This is the form `lem:edgeCon` actually needs (the constructions
  agree on the nose when the swapped pair is an edge).
* `transfers_of_rename` — the constructions are related by an ambient variable RELABELING `ρ`
  intertwining the substitutions; `MvPolynomial.aeval_rename` then gives kernel equality. This
  is the heavier bridge kept for `lem:later`, where the swap permutes free-variable columns. -/

/-- **Bridge 1 — pointwise equality.** If the two constructions agree pointwise
(`ambSub G σ e = ambSub G τ e`, i.e. `phiσ G σ e v c = phiσ G τ e v c` for all `v, c`),
then `Transfers G e σ τ`. The two pullback algebra homs are literally equal. -/
theorem transfers_of_phiσ_eq {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {e : ℕ}
    {σ τ : Equiv.Perm (Fin n)}
    (h : ∀ v c, phiσ G σ e v c = phiσ G τ e v c) :
    Transfers G e σ τ := by
  have hsub : ambSub G σ e = ambSub G τ e := by
    funext q; exact h q.1 q.2
  intro p
  rw [hsub]

/-- **Bridge 2 — FRESH-variable relabeling.** Suppose the σ-construction is the
τ-construction post-composed with a bijective relabeling `ρ` of the FRESH variables
`(Fin n × ℕ)`, i.e. `phiσ G σ e v c = rename ρ (phiσ G τ e v c)` for all `v, c`. Then
`Transfers G e σ τ`.

Proof: `rename ρ : Poly n →ₐ[ℝ] Poly n` is an algebra hom that, by `aeval_rename`-style
commutation, intertwines the two pullbacks:
`aeval (ambSub G σ e) p = rename ρ (aeval (ambSub G τ e) p)`
(both are algebra homs out of the ambient ring agreeing on generators `X (v,c)`). Since `ρ`
is injective, `rename ρ` is injective, so `rename ρ x = 0 ↔ x = 0`; applying this to
`x = aeval (ambSub G τ e) p` yields the kernel iff. (The general `ker(σ) = ρ⁻¹ ker(τ)` of an
*ambient* rename does NOT give kernel equality — it must be a fresh-variable AUTOMORPHISM, as
here, to preserve the kernel; this matches `lem:later`, where the swap permutes free columns of
the construction rather than relabeling ambient output coordinates.) -/
theorem transfers_of_rename {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {e : ℕ}
    {σ τ : Equiv.Perm (Fin n)}
    (ρ : (Fin n × ℕ) ≃ (Fin n × ℕ))
    (h : ∀ v c, phiσ G σ e v c = MvPolynomial.rename (⇑ρ) (phiσ G τ e v c)) :
    Transfers G e σ τ := by
  -- The two ambient pullbacks agree as `aeval (ambSub G σ) = (rename ρ) ∘ aeval (ambSub G τ)`,
  -- because both are algebra homs sending the generator `X (v,c)` to `rename ρ (phiσ G τ e v c)`.
  have hcomp : (MvPolynomial.aeval (ambSub G σ e) :
        MvPolynomial (Fin n × Fin (e + 1)) ℝ →ₐ[ℝ] Poly n)
      = (MvPolynomial.rename (⇑ρ)).comp (MvPolynomial.aeval (ambSub G τ e)) := by
    apply MvPolynomial.algHom_ext
    intro q
    simp only [AlgHom.coe_comp, Function.comp_apply, MvPolynomial.aeval_X]
    exact h q.1 q.2
  have hinj : Function.Injective (MvPolynomial.rename (⇑ρ) : Poly n → Poly n) :=
    MvPolynomial.rename_injective (R := ℝ) (⇑ρ) ρ.injective
  intro p
  have hpσ : MvPolynomial.aeval (ambSub G σ e) p
      = MvPolynomial.rename (⇑ρ) (MvPolynomial.aeval (ambSub G τ e) p) := by
    have := AlgHom.congr_fun hcomp p
    simpa [AlgHom.coe_comp, Function.comp_apply] using this
  rw [hpσ]
  constructor
  · intro hz
    have : MvPolynomial.rename (⇑ρ) (MvPolynomial.aeval (ambSub G τ e) p)
        = MvPolynomial.rename (⇑ρ) (0 : Poly n) := by rw [hz]; simp
    exact hinj this
  · intro hz; rw [hz]; simp

/-! ## `crossMinors` under column permutation and column scaling.

These two algebraic facts are the bookkeeping engine of `lem:edgeCon`. The matrix `F_v`
of vertex `v` for the ordering `τ` is the matrix for `σ` with its preceding-non-neighbour
columns (a) PERMUTED (the two swapped vertices appear in opposite order when both precede `v`)
and (b) each SCALED by the per-column sign `ε_u` carried up the recursion. `crossMinors`
(a vector of signed maximal minors = a `det`) is alternating multilinear in the columns, so a
column permutation multiplies it by `sign π` and a column scaling by `∏ λ_c`. -/

/-- **`crossMinors` is alternating in columns.** Permuting the columns of `F` by `π`
multiplies every coordinate of `crossMinors F` by `sign π`. (`Matrix.det_permute'` on the
row-dropped `d × d` minor, whose column index is untouched by `submatrix _ id`.) -/
theorem crossMinors_col_perm {d : ℕ} (F : Matrix (Fin (d + 1)) (Fin d) (Poly n))
    (π : Equiv.Perm (Fin d)) (j : Fin (d + 1)) :
    crossMinors (F.submatrix id π) j = (Equiv.Perm.sign π : ℝ) • crossMinors F j := by
  simp only [crossMinors]
  have h1 : (F.submatrix id ⇑π).submatrix j.succAbove id
      = (F.submatrix j.succAbove id).submatrix id ⇑π := by
    ext a b; simp [Matrix.submatrix_apply]
  rw [h1, Matrix.det_permute', smul_eq_C_mul, map_intCast]
  ring

/-- **`crossMinors` is multilinear in columns.** Scaling each column `c` of `F` by `lam c`
multiplies every coordinate of `crossMinors F` by `∏ c, lam c`. (`Matrix.det_mul_row` on the
row-dropped minor; the column index survives `submatrix _ id`.) -/
theorem crossMinors_col_scale {d : ℕ} (F : Matrix (Fin (d + 1)) (Fin d) (Poly n))
    (lam : Fin d → ℝ) (j : Fin (d + 1)) :
    crossMinors (Matrix.of fun i c => lam c • F i c) j = (∏ c, lam c) • crossMinors F j := by
  simp only [crossMinors]
  have h1 : (Matrix.of (fun i c => lam c • F i c)).submatrix j.succAbove id
      = Matrix.of (fun a c => MvPolynomial.C (lam c) * (F.submatrix j.succAbove id) a c) := by
    ext a b; simp [Matrix.submatrix_apply, smul_eq_C_mul]
  rw [h1, Matrix.det_mul_row, smul_eq_C_mul, map_prod]
  ring

/-- **`crossMinors` commutes with an algebra hom applied entrywise.** Since `crossMinors`
is built from a `det` and an integer sign, any `ℝ`-algebra hom `M : Poly n →ₐ[ℝ] Poly n`
commutes with it (`AlgHom.map_det`). -/
theorem crossMinors_algHom {d : ℕ} (M : Poly n →ₐ[ℝ] Poly n)
    (F : Matrix (Fin (d + 1)) (Fin d) (Poly n)) (j : Fin (d + 1)) :
    M (crossMinors F j) = crossMinors (Matrix.of fun i c => M (F i c)) j := by
  simp only [crossMinors]
  rw [map_mul, map_pow, map_neg, map_one, AlgHom.map_det]
  congr 1

/-! ## The `y`-rescaling fresh-variable automorphism and the sign-scale bridge.

The edge swap flips the sign of `φσ_τ(v)` relative to `φσ_σ(v)` for vertices `v` whose two
swapped predecessors appear as columns of `F_v` (a `det`-column transposition). A bare
`MvPolynomial.rename` (a *permutation* of variables) cannot realize this sign, so Bridge 2
(`transfers_of_rename`) does not apply directly. Instead we use the per-vertex `y`-rescaling
algebra hom `yScale δ : X(v,0) ↦ δ_v · X(v,0)` (fixing every non-`y` variable). Because each
`φσ(v) = y_v · crossMinors F_v` is *homogeneous of degree 1 in its own* `y_v = X(v,0)` and the
crossMinors factor contains only the OTHER vertices' variables, `yScale δ` rescales `φσ(v)` by
`δ_v` times the product of the rescalings of its column predecessors — i.e. it intertwines the
two constructions when `δ` is chosen as the column-permutation sign at each vertex. As an
involution (`δ_v = ±1`) `yScale δ` is injective, so it transfers kernels
(`transfers_of_algHom_inj`).
-/

/-- The `y`-rescaling algebra hom: multiply each scalar variable `X(v,0)` by `δ_v` and fix every
fresh column variable `X(v, slot)` (`slot ≥ 1`). -/
noncomputable def yScale (delta : Fin n → ℝ) : Poly n →ₐ[ℝ] Poly n :=
  MvPolynomial.aeval
    (fun q : Fin n × ℕ => if q.2 = 0 then (delta q.1) • MvPolynomial.X q else MvPolynomial.X q)

@[simp] theorem yScale_yVar (delta : Fin n → ℝ) (v : Fin n) :
    yScale delta (yVar v) = (delta v) • yVar v := by
  simp [yScale, yVar]

@[simp] theorem yScale_freshVar (delta : Fin n → ℝ) (d : ℕ) (v : Fin n) (k : ℕ) (r : Fin d) :
    yScale delta (freshVar d v k r) = freshVar d v k r := by
  simp only [yScale, freshVar, MvPolynomial.aeval_X]
  rw [if_neg]; omega

/-- `yScale δ` is injective when every `δ_v = ±1` (it is then an involution). -/
theorem yScale_injective (delta : Fin n → ℝ) (hd : ∀ v, delta v = 1 ∨ delta v = -1) :
    Function.Injective (yScale delta) := by
  have hcomp : (yScale delta).comp (yScale delta) = AlgHom.id ℝ (Poly n) := by
    apply MvPolynomial.algHom_ext
    intro q
    simp only [yScale, AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply, MvPolynomial.aeval_X]
    by_cases h : q.2 = 0
    · rw [if_pos h, map_smul, MvPolynomial.aeval_X, if_pos h, smul_smul]
      rcases hd q.1 with h1 | h1 <;> simp [h1]
    · rw [if_neg h, MvPolynomial.aeval_X, if_neg h]
  intro x y hxy
  have := congrArg (yScale delta) hxy
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, hcomp] at this
  simpa using this

/-- **Bridge 3 — injective algebra-hom intertwiner.** If an injective `ℝ`-algebra hom `M` on
`Poly n` intertwines the two constructions (`phiσ G σ e v c = M (phiσ G τ e v c)` for all `v,c`)
then `Transfers G e σ τ`. Same kernel-equality argument as `transfers_of_rename`, but for an
arbitrary injective `M` (here `M = yScale δ`, which—unlike `rename`—can carry the `±1` sign). -/
theorem transfers_of_algHom_inj {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {e : ℕ}
    {σ τ : Equiv.Perm (Fin n)} (M : Poly n →ₐ[ℝ] Poly n) (hM : Function.Injective M)
    (h : ∀ v c, phiσ G σ e v c = M (phiσ G τ e v c)) :
    Transfers G e σ τ := by
  have hcomp : (MvPolynomial.aeval (ambSub G σ e) :
        MvPolynomial (Fin n × Fin (e + 1)) ℝ →ₐ[ℝ] Poly n)
      = M.comp (MvPolynomial.aeval (ambSub G τ e)) := by
    apply MvPolynomial.algHom_ext
    intro q
    simp only [AlgHom.coe_comp, Function.comp_apply, MvPolynomial.aeval_X]
    exact h q.1 q.2
  intro p
  have hpσ : MvPolynomial.aeval (ambSub G σ e) p = M (MvPolynomial.aeval (ambSub G τ e) p) := by
    have := AlgHom.congr_fun hcomp p
    simpa [AlgHom.coe_comp, Function.comp_apply] using this
  rw [hpσ]
  constructor
  · intro hz
    have : M (MvPolynomial.aeval (ambSub G τ e) p) = M (0 : Poly n) := by rw [hz]; simp
    exact hM this
  · intro hz; rw [hz]; simp

/-! ## `lem:edgeCon` — the edge-swap base case (gorProof tex:365-380).

`σ` and `τ` differ only by swapping the two POSITIONS `i, i+1`, exchanging the vertices
`σ_i ↔ σ_{i+1}`, and `{σ_i, σ_{i+1}}` is an EDGE of `G`. We model the swap as
`τ = (Equiv.swap i j).trans σ` with `j = ⟨i.val+1, hi'⟩`, so `τ k = σ (swap i j k)`:
`τ_i = σ_{i+1}`, `τ_{i+1} = σ_i`, and `τ_k = σ_k` elsewhere — exactly gorProof's display
(tex:369). The conclusion `GOR⁺_σ = GOR⁺_τ` is delivered as `Transfers G e σ τ`. -/

/-- Order preservation of the position-swap `Equiv.swap i j` (with `j = i+1`) on `Fin n`-values,
away from the swapped pair: for `a ≠ b` not forming the pair `{i, j}`, the swap does not change
the `<`-comparison of their values. (Inside `precNonNbrσ` this is applied with `a = σ.symm u`,
`b = σ.symm v`; the excluded pair `{i, j}` is exactly the adjacent vertices, ruled out by the
edge hypothesis via `¬ G.Adj`.) -/
private theorem swap_val_lt_iff {i j a b : Fin n} (hj : j.val = i.val + 1)
    (hnotpair : ¬ (a = i ∧ b = j) ∧ ¬ (a = j ∧ b = i)) (hab : a ≠ b) :
    ((Equiv.swap i j a).val < (Equiv.swap i j b).val ↔ a.val < b.val) := by
  by_cases ha : a = i <;> by_cases hb : b = i <;>
    by_cases ha' : a = j <;> by_cases hb' : b = j <;>
    subst_vars <;>
    simp_all [Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne] <;>
    omega

/-- **The edge-hypothesis content of `lem:edgeCon`.** When `{σ_i, σ_{i+1}}` is an edge, swapping
positions `i, i+1` leaves every vertex's preceding-non-neighbour SET unchanged:
`precNonNbrσ G ((Equiv.swap i j).trans σ) v = precNonNbrσ G σ v` for all `v`.

The only vertex pair whose `σ`-order flips under the position-swap is `(σ_i, σ_{i+1})`. But that
pair is an edge, so it never satisfies the `¬ G.Adj` membership clause; hence on the set level
nothing moves. This is "the rest of the vertex ordering is shared by `σ` and `τ`"
(gorProof tex:379). -/
theorem precNonNbrσ_edge_swap (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Equiv.Perm (Fin n)) {i : Fin n} (j : Fin n) (hj : j.val = i.val + 1)
    (hedge : G.Adj (σ i) (σ j)) (v : Fin n) :
    precNonNbrσ G ((Equiv.swap i j).trans σ) v = precNonNbrσ G σ v := by
  set τ : Equiv.Perm (Fin n) := (Equiv.swap i j).trans σ with hτdef
  -- `τ.symm u = swap i j (σ.symm u)`.
  have hsymm : ∀ u, τ.symm u = (Equiv.swap i j) (σ.symm u) := by
    intro u; simp [hτdef]
  ext u
  simp only [mem_precNonNbrσ]
  -- The `¬ Adj` clause is identical; reduce to the order clause.
  constructor
  · rintro ⟨hlt, hadj⟩
    refine ⟨?_, hadj⟩
    -- Need `(σ.symm u).val < (σ.symm v).val`, given the τ-order and the edge hyp.
    rw [hsymm, hsymm] at hlt
    by_cases hpair : ((σ.symm u = i ∧ σ.symm v = j)) ∨ (σ.symm u = j ∧ σ.symm v = i)
    · -- Then {u,v} = {σ_i, σ_{i+1}} (an edge), contradicting `¬ G.Adj v u`.
      exfalso
      rcases hpair with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · have hu' : u = σ i := by rw [← hu]; simp
        have hv' : v = σ j := by rw [← hv]; simp
        rw [hu', hv'] at hadj; exact hadj hedge.symm
      · have hu' : u = σ j := by rw [← hu]; simp
        have hv' : v = σ i := by rw [← hv]; simp
        rw [hu', hv'] at hadj; exact hadj hedge
    · have hnotpair : ¬ (σ.symm u = i ∧ σ.symm v = j) ∧ ¬ (σ.symm u = j ∧ σ.symm v = i) :=
        ⟨fun h => hpair (Or.inl h), fun h => hpair (Or.inr h)⟩
      have hne : σ.symm u ≠ σ.symm v := by
        intro h
        have : u = v := σ.symm.injective h
        subst this; exact absurd hlt (lt_irrefl _)
      exact (swap_val_lt_iff hj hnotpair hne).1 hlt
  · rintro ⟨hlt, hadj⟩
    refine ⟨?_, hadj⟩
    rw [hsymm, hsymm]
    by_cases hpair : ((σ.symm u = i ∧ σ.symm v = j)) ∨ (σ.symm u = j ∧ σ.symm v = i)
    · exfalso
      rcases hpair with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · have hu' : u = σ i := by rw [← hu]; simp
        have hv' : v = σ j := by rw [← hv]; simp
        rw [hu', hv'] at hadj; exact hadj hedge.symm
      · have hu' : u = σ j := by rw [← hu]; simp
        have hv' : v = σ i := by rw [← hv]; simp
        rw [hu', hv'] at hadj; exact hadj hedge
    · have hnotpair : ¬ (σ.symm u = i ∧ σ.symm v = j) ∧ ¬ (σ.symm u = j ∧ σ.symm v = i) :=
        ⟨fun h => hpair (Or.inl h), fun h => hpair (Or.inr h)⟩
      have hne : σ.symm u ≠ σ.symm v := by
        intro h
        have : u = v := σ.symm.injective h
        subst this; exact absurd hlt (lt_irrefl _)
      exact (swap_val_lt_iff hj hnotpair hne).2 hlt

/-! ## The precList-reorder permutation `π_v`.

For the edge swap the preceding-non-neighbour SETs of `v` agree under `σ` and `τ`
(`precNonNbrσ_edge_swap`), so `precList G σ v` and `precList G τ v` are two `Nodup` sortings
of the SAME finset — hence list-permutations of each other. The function `reorderPerm`
turns this into an honest `Equiv.Perm (Fin e)`: on the precList block (`c < len`) it sends
`c ↦ idxOf (l₂[c]) l₁` (the σ-rank of the τ-`c`-th vertex), identity on the fresh block
(`c ≥ len`). Injectivity (hence bijectivity, since `Fin e` is finite) follows from the two
lists being `Nodup` with the same membership. -/

section ReorderPerm

variable (l₁ l₂ : List (Fin n)) (e : ℕ)
  (hlen : l₁.length = l₂.length) (hle : l₂.length ≤ e)
  (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂)

/-- The index reordering between two lists `l₁, l₂` of equal length `≤ e` with the same
membership, extended by the identity on the `[len, e)` fresh block: `reorderMap c` is the
`l₁`-index of `l₂[c]` when `c < l₂.length`, and `c` otherwise. The precList branch lands
below `l₂.length ≤ e` because `l₂[c] ∈ l₂ = l₁`, so `idxOf … l₁ < l₁.length = l₂.length`. -/
noncomputable def reorderMap (c : Fin e) : Fin e :=
  if h : c.val < l₂.length then
    ⟨l₁.idxOf l₂[c.val], by
      have hmemx : l₂[c.val] ∈ l₁ := (hmem _).2 (List.getElem_mem h)
      have := List.idxOf_lt_length_of_mem hmemx
      omega⟩
  else c

/-- `reorderMap` lands in the precList block when its argument does. -/
theorem reorderMap_lt {c : Fin e} (hc : c.val < l₂.length) :
    (reorderMap l₁ l₂ e hlen hle hmem c).val < l₂.length := by
  have hmemx : l₂[c.val] ∈ l₁ := (hmem _).2 (List.getElem_mem hc)
  have := List.idxOf_lt_length_of_mem hmemx
  simp only [reorderMap, hc, dif_pos]
  omega

/-- The defining `getElem` property on the precList block: `l₁[reorderMap c] = l₂[c]`. -/
theorem reorderMap_getElem {c : Fin e} (hc : c.val < l₂.length) :
    l₁[(reorderMap l₁ l₂ e hlen hle hmem c).val]'(by
      have := reorderMap_lt l₁ l₂ e hlen hle hmem hc; omega) = l₂[c.val] := by
  have hmemx : l₂[c.val] ∈ l₁ := (hmem _).2 (List.getElem_mem hc)
  have hidx : l₁.idxOf l₂[c.val] < l₁.length := List.idxOf_lt_length_of_mem hmemx
  simp only [reorderMap, hc, dif_pos]
  exact List.getElem_idxOf hidx

/-- `reorderMap` is identity on the fresh block. -/
theorem reorderMap_ge {c : Fin e} (hc : ¬ c.val < l₂.length) :
    reorderMap l₁ l₂ e hlen hle hmem c = c := by
  simp only [reorderMap, hc, dif_neg, not_false_eq_true]

/-- `reorderMap` is injective: it bijects the precList block onto itself (`Nodup` + same
membership) and is the identity on the fresh block. -/
theorem reorderMap_injective (hnd₂ : l₂.Nodup) :
    Function.Injective (reorderMap l₁ l₂ e hlen hle hmem) := by
  intro a b hab
  by_cases ha : a.val < l₂.length <;> by_cases hb : b.val < l₂.length
  · -- both in precList block: `idxOf` equal ⟹ `l₂[a] = l₂[b]` ⟹ (l₂ Nodup) a = b.
    have hidxeq : l₁.idxOf l₂[a.val] = l₁.idxOf l₂[b.val] := by
      have hv : (reorderMap l₁ l₂ e hlen hle hmem a).val
          = (reorderMap l₁ l₂ e hlen hle hmem b).val := by rw [hab]
      simpa only [reorderMap, ha, hb, dif_pos] using hv
    have hmemA : l₂[a.val] ∈ l₁ := (hmem _).2 (List.getElem_mem ha)
    have hmemB : l₂[b.val] ∈ l₁ := (hmem _).2 (List.getElem_mem hb)
    have heq : l₂[a.val] = l₂[b.val] := by
      have eA : l₁[l₁.idxOf l₂[a.val]]'(List.idxOf_lt_length_of_mem hmemA) = l₂[a.val] :=
        List.getElem_idxOf _
      have eB : l₁[l₁.idxOf l₂[b.val]]'(List.idxOf_lt_length_of_mem hmemB) = l₂[b.val] :=
        List.getElem_idxOf _
      rw [← eA, ← eB]
      simp only [hidxeq]
    have := (List.Nodup.getElem_inj_iff hnd₂ (i := a.val) (hi := ha) (j := b.val) (hj := hb)).1 heq
    exact Fin.ext this
  · exfalso
    have hla := reorderMap_lt l₁ l₂ e hlen hle hmem ha
    rw [hab, reorderMap_ge l₁ l₂ e hlen hle hmem hb] at hla
    exact hb hla
  · exfalso
    have hlb := reorderMap_lt l₁ l₂ e hlen hle hmem hb
    rw [← hab, reorderMap_ge l₁ l₂ e hlen hle hmem ha] at hlb
    exact ha hlb
  · rw [reorderMap_ge l₁ l₂ e hlen hle hmem ha, reorderMap_ge l₁ l₂ e hlen hle hmem hb] at hab
    exact hab

/-- **The precList-reorder permutation.** `reorderMap` packaged as an `Equiv.Perm (Fin e)`
(injective on a finite type ⟹ bijective). -/
noncomputable def reorderPerm (hnd₂ : l₂.Nodup) : Equiv.Perm (Fin e) :=
  Equiv.ofBijective (reorderMap l₁ l₂ e hlen hle hmem)
    ((Finite.injective_iff_bijective).1 (reorderMap_injective l₁ l₂ e hlen hle hmem hnd₂))

@[simp] theorem reorderPerm_apply (hnd₂ : l₂.Nodup) (c : Fin e) :
    reorderPerm l₁ l₂ e hlen hle hmem hnd₂ c = reorderMap l₁ l₂ e hlen hle hmem c := rfl

end ReorderPerm

/-- **`lem:edgeCon`** (gorProof tex:365-380, "Base Case 2"). If `σ` and `τ` differ exactly by
exchanging the two vertices at positions `i, i+1` (`τ = (Equiv.swap i j).trans σ`, `j = i+1`,
giving `τ_i = σ_{i+1}`, `τ_{i+1} = σ_i`, `τ_k = σ_k` else) and `{σ_i, σ_{i+1}}` is an EDGE of
`G`, then `Transfers G e σ τ` — the order-transfer equivalence of the two constructions.

The edge hypothesis is ESSENTIAL: it is what makes neither swapped vertex a preceding
non-neighbour of the other, so the preceding-non-neighbour SET of every vertex is unchanged
(`precNonNbrσ_edge_swap`). The non-adjacent swap is the *harder* `lem:later` (gorProof tex:396-…),
NOT this base case. -/
theorem transfers_of_edge_swap (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (e : ℕ)
    (σ : Equiv.Perm (Fin n)) {i : Fin n} (j : Fin n) (hj : j.val = i.val + 1)
    (hedge : G.Adj (σ i) (σ j))
    (hcard : ∀ v, (precNonNbrσ G σ v).card ≤ e) :
    Transfers G e σ ((Equiv.swap i j).trans σ) := by
  -- The preceding-non-neighbour SET of every vertex is identical for `σ` and `τ`
  -- (`precNonNbrσ_edge_swap`). We build a per-vertex column permutation `π_v` reordering the
  -- shared finset from `σ`-sort to `τ`-sort, set `δ v := sign π_v`, and intertwine the two
  -- constructions through the involution `yScale δ`, closing via `transfers_of_algHom_inj`.
  set τ : Equiv.Perm (Fin n) := (Equiv.swap i j).trans σ with hτdef
  have hset : ∀ v, precNonNbrσ G τ v = precNonNbrσ G σ v :=
    fun v => precNonNbrσ_edge_swap G σ j hj hedge v
  -- Per-vertex precList data: equal length (= card), same membership, both `Nodup`.
  -- We work with `l₁ = precList G σ v`, `l₂ = precList G τ v`.
  have hlenσ : ∀ v, (precList G σ v).length = (precNonNbrσ G σ v).card := fun v => by
    unfold precList; rw [Finset.length_sort]
  have hlenτ : ∀ v, (precList G τ v).length = (precNonNbrσ G τ v).card := fun v => by
    unfold precList; rw [Finset.length_sort]
  have hmemσ : ∀ v u, u ∈ precList G σ v ↔ u ∈ precNonNbrσ G σ v := fun v u => by
    unfold precList; rw [Finset.mem_sort]
  have hmemτ : ∀ v u, u ∈ precList G τ v ↔ u ∈ precNonNbrσ G τ v := fun v u => by
    unfold precList; rw [Finset.mem_sort]
  have hnodσ : ∀ v, (precList G σ v).Nodup := fun v => by
    unfold precList; exact Finset.sort_nodup _ _
  have hnodτ : ∀ v, (precList G τ v).Nodup := fun v => by
    unfold precList; exact Finset.sort_nodup _ _
  -- length equality `σ`/`τ` and `≤ e`.
  have hlen : ∀ v, (precList G σ v).length = (precList G τ v).length := fun v => by
    rw [hlenσ, hlenτ, hset]
  have hle : ∀ v, (precList G τ v).length ≤ e := fun v => by
    rw [hlenτ, hset]; exact hcard v
  -- same membership of the two precLists (via the shared finset).
  have hmem : ∀ v u, u ∈ precList G σ v ↔ u ∈ precList G τ v := fun v u => by
    rw [hmemσ, hmemτ, hset]
  -- The per-vertex reorder permutation `π v : Equiv.Perm (Fin e)`.
  set π : Fin n → Equiv.Perm (Fin e) := fun v =>
    reorderPerm (precList G σ v) (precList G τ v) e (hlen v) (hle v) (hmem v) (hnodτ v)
    with hπdef
  -- The global sign function `δ v := sign (π v) : ℝ` (always `±1`).
  set δ : Fin n → ℝ := fun v => (Equiv.Perm.sign (π v) : ℝ) with hδdef
  have hδpm : ∀ v, δ v = 1 ∨ δ v = -1 := fun v => by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (π v)) with h | h <;>
      simp only [hδdef, h] <;> [left; right] <;> norm_num
  -- The KEY intertwining identity, by strong recursion on `σ`-position `(σ.symm v).val`.
  have key : ∀ N : ℕ, ∀ v : Fin n, (σ.symm v).val = N →
      ∀ c, phiσ G σ e v c = yScale δ (phiσ G τ e v c) := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N IH =>
      intro v hvN c
      -- IH in usable form: for `u` strictly earlier than `v` in `σ`, the identity holds.
      have IH' : ∀ u, (σ.symm u).val < (σ.symm v).val →
          ∀ c, phiσ G σ e u c = yScale δ (phiσ G τ e u c) := by
        intro u hu cc
        exact IH (σ.symm u).val (by omega) u rfl cc
      -- The two previously-assigned families inside `phiσ v`.
      set φσf : Fin n → Fin (e + 1) → Poly n :=
        (fun u => if (σ.symm u).val < (σ.symm v).val then phiσ G σ e u else fun _ => 0)
        with hφσf
      set φτf : Fin n → Fin (e + 1) → Poly n :=
        (fun u => if (τ.symm u).val < (τ.symm v).val then phiσ G τ e u else fun _ => 0)
        with hφτf
      -- The column identity (the heart): the `yScale`-mapped τ-matrix is the σ-matrix with
      -- columns permuted by `π v`.
      have hcol : (Matrix.of fun rowi colc =>
            yScale δ (phiMat G τ e φτf v rowi colc))
          = (phiMat G σ e φσf v).submatrix id (π v) := by
        refine Matrix.ext fun rowi colc => ?_
        simp only [Matrix.submatrix_apply, Matrix.of_apply, id_eq]
        -- unfold both `phiMat` entries
        simp only [phiMat, Matrix.of_apply]
        by_cases hlt : colc.val < (precList G τ v).length
        · -- precList block
          -- τ-side: read vertex `u₂ = (precList G τ v)[colc]`.
          have hu₂ : (precList G τ v)[colc.val]? = some ((precList G τ v)[colc.val]'hlt) :=
            List.getElem?_eq_getElem hlt
          set u₂ : Fin n := (precList G τ v)[colc.val]'hlt with hu₂def
          -- membership in the shared finset, and the recursion guards fire.
          have hu₂memτ : u₂ ∈ precNonNbrσ G τ v := by
            rw [← hmemτ v u₂]; exact List.getElem_mem hlt
          have hu₂memσ : u₂ ∈ precNonNbrσ G σ v := by rw [← hset v]; exact hu₂memτ
          have hguardτ : (τ.symm u₂).val < (τ.symm v).val := precNonNbrσ_lt G τ hu₂memτ
          have hguardσ : (σ.symm u₂).val < (σ.symm v).val := precNonNbrσ_lt G σ hu₂memσ
          -- σ-side column index `(π v colc).val`, lands in precList block and reads the same `u₂`.
          have hπlt : (π v colc).val < (precList G τ v).length := by
            simp only [hπdef, reorderPerm_apply]
            exact reorderMap_lt _ _ _ _ _ _ hlt
          have hπltσ : (π v colc).val < (precList G σ v).length := by
            rw [hlen v]; exact hπlt
          have hgetσ : (precList G σ v)[(π v colc).val]'hπltσ = u₂ := by
            simp only [hπdef, reorderPerm_apply]
            exact reorderMap_getElem _ _ _ _ _ _ hlt
          have hu₂' : (precList G σ v)[(π v colc).val]? = some u₂ := by
            rw [List.getElem?_eq_getElem hπltσ, hgetσ]
          -- rewrite both matches, then reduce `match some u₂ with …` to the `some` branch.
          rw [hu₂, hu₂']
          dsimp only
          -- τ-side value: `yScale δ (φτf u₂ rowi)` with guard firing.
          have hφτval : φτf u₂ rowi = phiσ G τ e u₂ rowi := by
            simp only [hφτf, hguardτ, if_true]
          -- σ-side value: `φσf u₂ rowi` with guard firing.
          have hφσval : φσf u₂ rowi = phiσ G σ e u₂ rowi := by
            simp only [hφσf, hguardσ, if_true]
          rw [hφτval, hφσval]
          -- IH closes it: `phiσ G σ e u₂ rowi = yScale δ (phiσ G τ e u₂ rowi)`.
          exact (IH' u₂ hguardσ rowi).symm
        · -- fresh block: both sides are the same `freshVar`.
          have hnoneτ : (precList G τ v)[colc.val]? = none := List.getElem?_eq_none (by omega)
          have hπge : (π v colc) = colc := by
            simp only [hπdef, reorderPerm_apply]
            exact reorderMap_ge _ _ _ _ _ _ hlt
          have hnoneσ : (precList G σ v)[(π v colc).val]? = none := by
            rw [hπge]; exact List.getElem?_eq_none (by rw [hlen v]; omega)
          rw [hnoneτ, hnoneσ, hπge]
          dsimp only
          -- both fresh columns use the same offset `colc - length`, which coincide via `hlen`.
          rw [hlen v]
          exact yScale_freshVar δ (e + 1) v _ rowi
      -- Now assemble: unfold `phiσ` one step on both sides and apply the column identity.
      rw [phiσ_eq G σ e v, phiσ_eq G τ e v]
      simp only [phiStep]
      -- RHS: push `yScale δ` through `yVar v * crossMinors …`.
      rw [map_mul, yScale_yVar, crossMinors_algHom]
      -- The mapped matrix equals the permuted σ-matrix (hcol), then apply `crossMinors_col_perm`.
      rw [show (Matrix.of fun rowi colc => yScale δ (phiMat G τ e φτf v rowi colc))
            = (phiMat G σ e φσf v).submatrix id (π v) from hcol,
          crossMinors_col_perm]
      -- LHS = yVar v * crossMinors (phiMat G σ e φσf v) c.
      -- RHS = (δ v • yVar v) * (sign (π v) • crossMinors (phiMat G σ e φσf v) c).
      -- δ v = sign (π v) and δ v * δ v = 1 (sign is ±1), so the two factors cancel.
      have hsign : ((Equiv.Perm.sign (π v) : ℤ) : ℝ) = δ v := by simp only [hδdef]
      rw [hsign, ← hφσf]
      have hδsq : δ v * δ v = 1 := by
        rcases hδpm v with h1 | h1 <;> simp [h1]
      rw [smul_mul_smul_comm, hδsq, one_smul]
  -- Close via the injective intertwiner `yScale δ`.
  have key' : ∀ v, ∀ c, phiσ G σ e v c = yScale δ (phiσ G τ e v c) :=
    fun v c => key (σ.symm v).val v rfl c
  exact transfers_of_algHom_inj (yScale δ) (yScale_injective δ hδpm) key'

end LSS
