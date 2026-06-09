/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Order.BourbakiWitt
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# §3.1 Tensor-to-matrix transformations: the `Q_{i,j}` bound

Source: the semicontinuity manuscript,
lines 840–1002.

For a `k`-tensor `T ∈ V_1 ⊗ ⋯ ⊗ V_k`:

* `subrankPair_{i,j}(T)` (tex:836): the largest `r` with `T ≥ ⟨r⟩_{i,j}`.
* `flatRank_I(T)` (tex:378-380): matrix rank of the `I`-flattening.

This file formalizes:

* `flush_lemma` — **Lemma 3.4** (tex:858-866, `\label{lem:flush}`).
* `subrankPair_prod_ge_flatRank` — **Theorem 3.2** (tex:840-845, `\label{th:Qij}`).
* `exists_large_subrankPair` — **Corollary 3.3** (tex:849-854, `\label{cor:Qij}`).
* **Corollary 3.5** (tex:976-996, unlabeled) — PROVEN downstream as
  `AsymptoticSubrank.Main.minCut_flatRank_le_asympSubrank_of_infinite` (its proof needs the weighted
  Vrana–Christandl formula + field invariance, formalized in `AsymptoticSubrank/`).
-/

namespace Semicontinuity

open scoped TensorProduct

universe u

variable {F : Type u} [Field F]

private lemma mvPolynomial_exists_eval_ne_zero_of_totalDegree_lt_card
    {σ : Type*} [Finite σ] {p : MvPolynomial σ F}
    (hp : p ≠ 0) (hdeg : (p.totalDegree : Cardinal) < Cardinal.mk F) :
    ∃ x : σ → F, MvPolynomial.eval x p ≠ 0 := by
  classical
  by_cases hfin : Nonempty (Fintype F)
  · letI : Fintype F := hfin.some
    have hdeg_nat : p.totalDegree < Fintype.card F := by
      have hdeg' : (p.totalDegree : Cardinal.{u}) < (Fintype.card F : Cardinal.{u}) := by
        simpa [Cardinal.mk_fintype] using hdeg
      exact_mod_cast hdeg'
    by_contra h
    push_neg at h
    apply hp
    refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset p (fun _ : σ => Finset.univ) ?_ ?_
    · intro i
      exact lt_of_le_of_lt (MvPolynomial.degreeOf_le_totalDegree p i) (by simpa using hdeg_nat)
    · intro x _hx
      exact h x
  · haveI : Infinite F := Infinite.of_not_fintype (fun hFintype => hfin ⟨hFintype⟩)
    by_contra h
    push_neg at h
    apply hp
    have h0 : ∀ x : σ → F, MvPolynomial.eval x p = MvPolynomial.eval x 0 := by
      intro x
      simp [h x]
    exact MvPolynomial.funext h0

/-! ## `k`-tensor setup.

We use the `Pi`-style encoding `T : (i : Fin k) → Fin (d i) → F` for a tensor in
`F^{d_0} ⊗ ⋯ ⊗ F^{d_{k-1}}`. The paper requires `d ∈ ℤ_{≥1}^k` (tex:305, 389);
we therefore index format by `Fin k → ℕ+`. -/

/-- A `k`-tensor of format `d : Fin k → ℕ+` over `F`. -/
abbrev KTensor (F : Type u) [Field F] {k : ℕ} (d : Fin k → ℕ+) : Type u :=
  (∀ i : Fin k, Fin (d i)) → F

/-! ## Restriction, Kronecker product, direct sum (tex:391-397). -/

/-- **Restriction** `S ≤ T` (Christandl-Hoeberechts-Nieuwboer-Vrana-Zuiddam tex:398,
    `\label{subsec:prelim}`).

    Verbatim paper definition (tex:392): "For two `k`-tensors `S` and `T` we say
    `S` is a restriction of `T` and write `S ≤ T` if there are linear maps `A_i`
    such that `S = (A_1 ⊗ ⋯ ⊗ A_k) T`."

    Realized via leg-wise matrices `A_i : Matrix (Fin (dS i)) (Fin (dT i)) F`
    (each `A_i` encodes a linear map `F^{dT i} → F^{dS i}`). The Kronecker-product
    formula `((A_1 ⊗ ⋯ ⊗ A_k) T) jdx = ∑ idx, (∏ i, A_i (jdx i) (idx i)) * T idx`
    expresses leg-wise application of the matrices to `T`. -/
def Restricts {k : ℕ} {dS dT : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT) : Prop :=
  ∃ A : ∀ i : Fin k, Matrix (Fin (dS i)) (Fin (dT i)) F,
    ∀ jdx : (∀ i : Fin k, Fin (dS i)),
      S jdx = ∑ idx : (∀ i : Fin k, Fin (dT i)),
        (∏ i, A i (jdx i) (idx i)) * T idx

@[inherit_doc] scoped infix:50 " ≤ₜ " => Restricts

/-- **Reflexivity** of restriction (tex:392).

    Every `k`-tensor `T` is a restriction of itself, using the identity matrix
    on each leg. -/
lemma Restricts.refl {k : ℕ} {d : Fin k → ℕ+} (T : KTensor F d) :
    Restricts T T := by
  classical
  refine ⟨fun i => (1 : Matrix (Fin (d i)) (Fin (d i)) F), ?_⟩
  intro jdx
  -- ∑ idx, (∏ i, (1 : Matrix _ _ F) (jdx i) (idx i)) * T idx = T jdx
  -- The product (∏ i, δ(jdx i, idx i)) = 1 iff jdx = idx, else 0.
  -- Apply `Finset.sum_eq_single` at `jdx`.
  rw [Finset.sum_eq_single jdx]
  · -- (∏ i, 1 (jdx i) (jdx i)) * T jdx = 1 * T jdx = T jdx.
    have hprod : (∏ i, (1 : Matrix (Fin (d i)) (Fin (d i)) F) (jdx i) (jdx i)) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      simp [Matrix.one_apply_eq]
    rw [hprod, one_mul]
  · -- For idx ≠ jdx, ∃ i₀ : Fin k, idx i₀ ≠ jdx i₀, so factor at i₀ is 0.
    intro idx _ hne
    have hex : ∃ i₀, jdx i₀ ≠ idx i₀ := by
      by_contra hall
      push_neg at hall
      exact hne (funext fun i => (hall i).symm)
    obtain ⟨i₀, hi₀⟩ := hex
    have hzero : (1 : Matrix (Fin (d i₀)) (Fin (d i₀)) F) (jdx i₀) (idx i₀) = 0 :=
      Matrix.one_apply_ne hi₀
    have hprod_zero :
        (∏ i, (1 : Matrix (Fin (d i)) (Fin (d i)) F) (jdx i) (idx i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i₀) hzero
    rw [hprod_zero, zero_mul]
  · intro hne; exact absurd (Finset.mem_univ _) hne

/-- **Transitivity** of restriction (tex:392).

    If `S ≤ T` (via leg-wise matrices `A`) and `T ≤ U` (via leg-wise matrices
    `B`), then `S ≤ U` via the leg-wise matrix products `A i * B i`. This is the
    composition `(A_1 ⊗ ⋯ ⊗ A_k) (B_1 ⊗ ⋯ ⊗ B_k) = (A_1 B_1) ⊗ ⋯ ⊗ (A_k B_k)`
    of the underlying linear maps (paper tex:392, restriction is a preorder). -/
lemma Restricts.trans {k : ℕ} {dS dT dU : Fin k → ℕ+}
    {S : KTensor F dS} {T : KTensor F dT} {U : KTensor F dU}
    (hST : Restricts S T) (hTU : Restricts T U) :
    Restricts S U := by
  classical
  obtain ⟨A, hA⟩ := hST
  obtain ⟨B, hB⟩ := hTU
  -- Composite leg-wise matrices: `(A i) * (B i)`.
  refine ⟨fun i => A i * B i, ?_⟩
  intro jdx
  -- Expand `S` via `A`, then `T` via `B`, then reassemble.
  rw [hA jdx]
  -- `S jdx = ∑ idx, (∏ i, A i (jdx i) (idx i)) * T idx`.
  -- Substitute `T idx = ∑ kdx, (∏ i, B i (idx i) (kdx i)) * U kdx`.
  simp_rw [hB]
  -- LHS now: `∑ idx, (∏ i, A i (jdx i) (idx i)) * (∑ kdx, (∏ i, B i (idx i) (kdx i)) * U kdx)`.
  -- RHS: `∑ kdx, (∏ i, (A i * B i) (jdx i) (kdx i)) * U kdx`.
  -- Pull the `A`-product into the inner sum on the LHS.
  simp_rw [Finset.mul_sum]
  -- Swap the order of summation: `∑ idx ∑ kdx` → `∑ kdx ∑ idx`.
  rw [Finset.sum_comm]
  -- Now match termwise over `kdx`.
  refine Finset.sum_congr rfl ?_
  intro kdx _
  -- Goal: `∑ idx, (∏ i, A i (jdx i) (idx i)) * ((∏ i, B i (idx i) (kdx i)) * U kdx)`
  --        = (∏ i, (A i * B i) (jdx i) (kdx i)) * U kdx.
  -- Factor `U kdx` out of the LHS sum.
  have hfactor :
      ∀ idx : (∀ i : Fin k, Fin (dT i)),
        (∏ i, A i (jdx i) (idx i)) * ((∏ i, B i (idx i) (kdx i)) * U kdx)
          = (∏ i, A i (jdx i) (idx i) * B i (idx i) (kdx i)) * U kdx := by
    intro idx
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [hfactor]
  rw [← Finset.sum_mul]
  congr 1
  -- `∑ idx, ∏ i, A i (jdx i) (idx i) * B i (idx i) (kdx i)
  --    = ∏ i, (A i * B i) (jdx i) (kdx i)`.
  -- Unfold the matrix product on the RHS into a sum over the bridging index.
  have hmulapply :
      (∏ i, (A i * B i) (jdx i) (kdx i))
        = ∏ i, ∑ m : Fin (dT i), A i (jdx i) m * B i m (kdx i) := by
    refine Finset.prod_congr rfl ?_
    intro i _
    rw [Matrix.mul_apply]
  rw [hmulapply]
  -- `∏ i, ∑ m, f i m = ∑ tuple ∈ piFinset, ∏ i, f i (tuple i)`.
  rw [Finset.prod_univ_sum
        (t := fun _ : Fin k => (Finset.univ : Finset (Fin (dT _))))
        (f := fun (i : Fin k) (m : Fin (dT i)) => A i (jdx i) m * B i m (kdx i))]
  -- `piFinset (fun _ => univ) = univ`, then match termwise.
  rw [show
      Fintype.piFinset (fun i : Fin k => (Finset.univ : Finset (Fin (dT i))))
        = (Finset.univ : Finset (∀ i : Fin k, Fin (dT i))) from by
    ext _; simp]

def kronLeftIndex {k : ℕ} {dS dT : Fin k → ℕ+}
    (idx : ∀ i : Fin k, Fin (dS i * dT i)) (i : Fin k) : Fin (dS i) :=
  (finProdFinEquiv.symm (by simpa [PNat.mul_coe] using idx i)).1

/-- Right leg-index projection for the grouped Kronecker-product format. -/
def kronRightIndex {k : ℕ} {dS dT : Fin k → ℕ+}
    (idx : ∀ i : Fin k, Fin (dS i * dT i)) (i : Fin k) : Fin (dT i) :=
  (finProdFinEquiv.symm (by simpa [PNat.mul_coe] using idx i)).2

/-- **Kronecker product** `S ⊠ T` (tex:393): "grouped" tensor product of two
    `k`-tensors of formats `dS, dT`, to a `k`-tensor of format `i ↦ dS i * dT i`. -/
noncomputable def kroneckerTensor {k : ℕ} {dS dT : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT) :
    KTensor F (fun i => dS i * dT i) :=
  fun idx => S (kronLeftIndex idx) * T (kronRightIndex idx)

@[inherit_doc] scoped infix:70 " ⊠ " => kroneckerTensor

/-- **Direct sum** `S ⊕ T` of two `k`-tensors of formats `dS, dT`,
    block-diagonal in each leg, format `i ↦ dS i + dT i`.

    Convention from `\oplus`-additivity in the asymptotic spectrum (tex:781);
    not given an explicit definition in the paper but used throughout.

    Realized via `.val` decomposition of each leg: at multi-index `idx`, every
    leg-coordinate `idx i ∈ Fin (dS i + dT i)` is either entirely in the
    `[0, dS i)` block (use `S`) or entirely in the `[dS i, dS i + dT i)` block
    (use `T`, with shifted index `(idx i).val - (dS i)`). Mixed indices land
    off the block diagonal and contribute `0`. -/
noncomputable def directSumTensor {k : ℕ} {dS dT : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT) :
    KTensor F (fun i => dS i + dT i) := by
  classical
  intro idx
  by_cases hS_all : ∀ i, (idx i).val < (dS i : ℕ)
  · -- All legs in the dS-block: use S.
    exact S (fun i => ⟨(idx i).val, hS_all i⟩)
  · by_cases hT_all : ∀ i, (dS i : ℕ) ≤ (idx i).val
    · -- All legs in the dT-block: use T with shifted index.
      refine T (fun i => ⟨(idx i).val - (dS i : ℕ), ?_⟩)
      have h1 : (idx i).val < ((dS i + dT i : ℕ+) : ℕ) := (idx i).isLt
      have h2 : ((dS i + dT i : ℕ+) : ℕ) = (dS i : ℕ) + (dT i : ℕ) :=
        PNat.add_coe _ _
      have hT_i : (dS i : ℕ) ≤ (idx i).val := hT_all i
      omega
    · -- Off block-diagonal: 0.
      exact 0

@[inherit_doc] scoped infix:65 " ⊕ₜ " => directSumTensor

/-! ## Unit tensors (tex:396, 836). -/

/-- **Rank-`r` unit `k`-tensor** `⟨r⟩` (tex:396): `Σ_{ℓ=1}^r e_ℓ ⊗ ⋯ ⊗ e_ℓ`
    in `F^r ⊗ ⋯ ⊗ F^r`. As an array, the entry at multi-index `idx` is `1` iff
    all legs share the same coordinate, else `0`. -/
noncomputable def unitTensor (F : Type u) [Field F] {k : ℕ} (r : ℕ+) :
    KTensor F (fun (_ : Fin k) => r) :=
  fun idx => if ∀ i j : Fin k, idx i = idx j then 1 else 0

/-- **Natural pair-unit format** (tex:836): `d_i = d_j = r`, other legs `= 1`.

This is the canonical format on which the paper's `⟨r⟩_{i,j}` lives. -/
def naturalPairFormat {k : ℕ} (r : ℕ+) (i j : Fin k) : Fin k → ℕ+ :=
  fun ℓ => if ℓ = i ∨ ℓ = j then r else 1

/-- **`⟨r⟩_{i,j}` pair-unit tensor** (tex:836):
    `Σ_{ℓ=1}^r e_ℓ ⊗ e_ℓ ⊗ e_1 ⊗ ⋯ ⊗ e_1`, with `e_ℓ`-pair on legs `i ≠ j`
    and `e_1` on the remaining legs. The format is the natural one
    (`d_i = d_j = r`, other legs `= 1`).

    As an array, the entry at `idx` is `1` iff the leg-`i` and leg-`j`
    coordinates agree (as natural numbers); all other legs are
    `Fin 1`-valued so contribute no constraint. -/
noncomputable def unitPairTensor {k : ℕ} (r : ℕ+) (i j : Fin k) (_hij : i ≠ j) :
    KTensor F (naturalPairFormat r i j) :=
  fun idx => if (idx i).val = (idx j).val then 1 else 0

/-! ## Subranks (tex:836) and flattening ranks (tex:380, 838).

`subrankPair T i j` is the paper's `subrank_{i,j}(T)`. For `i = j` we use a
default value of `0` (the paper's product over `(i,j) ∈ I × ([k]\I)` never sees
`i = j` since `I ∩ ([k]\I) = ∅`). -/

/-- **Pair-subrank** `subrankPair_{i,j}(T)` (tex:836): largest `r` with
    `T ≥ ⟨r⟩_{i,j}` when `i ≠ j`; `0` when `i = j` (the paper does not define
    the diagonal case but never uses it).

    Realized as the `sSup` (over `ℕ`) of the set of positive `r` for which
    `⟨r⟩_{i,j}` restricts to `T`. The set is bounded above (by `min (d i) (d j)`,
    since a rank-`r` pair-unit must embed into the flattening), so `sSup`
    coincides with the actual maximum. -/
noncomputable def subrankPair {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (i j : Fin k) : ℕ := by
  classical
  by_cases hij : i = j
  · exact 0
  · exact sSup { r : ℕ | ∃ hr : 0 < r,
      Restricts (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) T }

/-- The "flattening matrix" of a `k`-tensor `T` along `I ⊆ [k]`: rows indexed by
    `(∀ i ∈ I, Fin (d i))`, columns by `(∀ j ∉ I, Fin (d j))`. Entries are the
    corresponding entries of `T`, obtained by recombining the row/column indices
    into a full multi-index via `if h : i ∈ I then row ⟨i, h⟩ else col ⟨i, h⟩`.

    This is exactly the matrix from paper tex:378-380, 838: "the matrix obtained
    from `T` by grouping legs in `I` together and grouping legs in `[k]\I`
    together." -/
noncomputable def flattenMatrix {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (I : Finset (Fin k)) :
    Matrix
      (∀ i : {i : Fin k // i ∈ I}, Fin (d i.val))
      (∀ j : {j : Fin k // j ∉ I}, Fin (d j.val))
      F :=
  fun row col =>
    T (fun i => if h : i ∈ I then row ⟨i, h⟩ else col ⟨i, h⟩)

/-- **`I`-flattening rank** `flatRank_I(T)` (tex:378-380, 838): the matrix rank of
    the matrix obtained from `T` by grouping legs in `I` together and legs in
    `[k]\\I` together.

    Realized as `Matrix.rank` of `flattenMatrix T I`. -/
noncomputable def flatRank {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (I : Finset (Fin k)) : ℕ :=
  (flattenMatrix T I).rank

/-- **Restriction-monotonicity of the flattening matrix (tex:392, 378-380).**
    If `S ≤ₜ T` via leg-matrices `A`, then for any leg set `I` the `I`-flattening
    of `S` factors as `P · (flattenMatrix T I) · Q`, where `P` is the Kronecker
    product of the `A`-blocks on the legs in `I` (rows) and `Q` the Kronecker
    product of the `A`-blocks on the complement legs (columns).

    This is the matrix form of `S = (A_1 ⊗ ⋯ ⊗ A_k) T` flattened along `I`. -/
lemma Restricts.flattenMatrix_factor {k : ℕ} {dS dT : Fin k → ℕ+}
    {S : KTensor F dS} {T : KTensor F dT} (I : Finset (Fin k))
    {A : ∀ i : Fin k, Matrix (Fin (dS i)) (Fin (dT i)) F}
    (hA : ∀ jdx : (∀ i : Fin k, Fin (dS i)),
      S jdx = ∑ idx : (∀ i : Fin k, Fin (dT i)),
        (∏ i, A i (jdx i) (idx i)) * T idx) :
    flattenMatrix S I
      = (Matrix.of (fun (rowS : ∀ i : {i // i ∈ I}, Fin (dS i.val))
            (rowT : ∀ i : {i // i ∈ I}, Fin (dT i.val)) =>
            ∏ i : {i // i ∈ I}, A i.val (rowS i) (rowT i)))
        * (flattenMatrix T I)
        * (Matrix.of (fun (colT : ∀ j : {j // j ∉ I}, Fin (dT j.val))
            (colS : ∀ j : {j // j ∉ I}, Fin (dS j.val)) =>
            ∏ j : {j // j ∉ I}, A j.val (colS j) (colT j))) := by
  classical
  ext rowS colS
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply]
  change S (fun x => if h : x ∈ I then rowS ⟨x, h⟩ else colS ⟨x, h⟩) = _
  rw [hA]
  -- Reindex the sum over `idx` by the row/col split of `I`.
  rw [← Equiv.sum_comp (Equiv.piEquivPiSubtypeProd (· ∈ I)
          (fun x => Fin (dT x))).symm
        (fun idx : (∀ x : Fin k, Fin (dT x)) =>
          (∏ i_1, A i_1 (if h : i_1 ∈ I then rowS ⟨i_1, h⟩ else colS ⟨i_1, h⟩)
            (idx i_1)) * T idx)]
  rw [Fintype.sum_prod_type]
  simp only [Matrix.of_apply]
  -- RHS: `∑ colT, (∑ rowT, P rowS rowT * (flatten T) rowT colT) * Q colT colS`.
  rw [show (∑ colT, (∑ rowT,
        (∏ i : {i // i ∈ I}, A i.val (rowS i) (rowT i)) * flattenMatrix T I rowT colT)
          * (∏ j : {j // j ∉ I}, A j.val (colS j) (colT j)))
        = ∑ rowT, ∑ colT,
          (∏ i : {i // i ∈ I}, A i.val (rowS i) (rowT i)) * flattenMatrix T I rowT colT
            * (∏ j : {j // j ∉ I}, A j.val (colS j) (colT j)) from by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro colT _
      rw [Finset.sum_mul]]
  refine Finset.sum_congr rfl ?_
  intro rowT _
  refine Finset.sum_congr rfl ?_
  intro colT _
  -- Reassemble `T (combine rowT colT) = flattenMatrix T I rowT colT`.
  have hTval : T ((Equiv.piEquivPiSubtypeProd (· ∈ I) (fun x => Fin (dT x))).symm
      (rowT, colT)) = flattenMatrix T I rowT colT := by
    rw [flattenMatrix]; congr 1
  -- The leg-product `∏_ℓ` splits into the `I`-block and complement-block products.
  have hsplit : (∏ i_1, A i_1
        (if h : i_1 ∈ I then rowS ⟨i_1, h⟩ else colS ⟨i_1, h⟩)
        (((Equiv.piEquivPiSubtypeProd (· ∈ I) (fun x => Fin (dT x))).symm
          (rowT, colT)) i_1))
      = (∏ i : {i // i ∈ I}, A i.val (rowS i) (rowT i))
        * (∏ j : {j // j ∉ I}, A j.val (colS j) (colT j)) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (· ∈ I)
        (fun ℓ => A ℓ (if h : ℓ ∈ I then rowS ⟨ℓ, h⟩ else colS ⟨ℓ, h⟩)
          (((Equiv.piEquivPiSubtypeProd (· ∈ I) (fun x => Fin (dT x))).symm
            (rowT, colT)) ℓ))]
    congr 1
    · convert Finset.prod_congr rfl ?_ using 2
      · ext x; simp
      · rintro ⟨i, hi⟩ _
        rw [dif_pos hi]
        congr 1
        rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos hi]
    · convert Finset.prod_congr rfl ?_ using 2
      rintro ⟨j, hj⟩ _
      rw [dif_neg hj]
      congr 1
      rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg hj]
  rw [hsplit, hTval]
  ring

/-- **Restriction-monotonicity of the flattening rank (tex:392, 378-380).**
    If `S ≤ₜ T` then `flatRank S I ≤ flatRank T I` for every leg set `I`: the
    `I`-flattening of `S` is a two-sided matrix product with `flattenMatrix T I`,
    so `Matrix.rank_mul_le` bounds its rank. -/
lemma Restricts.flatRank_le {k : ℕ} {dS dT : Fin k → ℕ+}
    {S : KTensor F dS} {T : KTensor F dT} (hST : Restricts S T)
    (I : Finset (Fin k)) :
    flatRank S I ≤ flatRank T I := by
  classical
  obtain ⟨A, hA⟩ := hST
  rw [flatRank, flatRank, Restricts.flattenMatrix_factor I hA]
  calc ((_ * flattenMatrix T I) * _).rank
      ≤ (_ * flattenMatrix T I).rank :=
        (Matrix.rank_mul_le _ _).trans (min_le_left _ _)
    _ ≤ (flattenMatrix T I).rank := (Matrix.rank_mul_le _ _).trans (min_le_right _ _)

/-- **General-arity pair-unit flattening bound (tex:836, 880-899).** For distinct
    legs `i ≠ j` of any `k`-tensor `T`, a rank-`r` pair-unit `⟨r⟩_{i,j}` that
    restricts to `T` forces `r ≤ flatRank T {i}`. The pair-unit's `{i}`-flattening
    is the rank-`r` identity (legs other than `i` are columns; only `j` carries a
    nontrivial dimension `r` and the entry is `1` iff leg `i` and leg `j` agree),
    and `flatRank` is monotone under restriction (`Restricts.flatRank_le`). -/
private lemma pairUnit_restricts_le_flatRank {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (i j : Fin k) (hij : i ≠ j) {r : ℕ} (hr : 0 < r)
    (hres : Restricts (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) T) :
    r ≤ flatRank T {i} := by
  classical
  -- `flatRank (⟨r⟩_{i,j}) {i} ≤ flatRank T {i}` by restriction-monotonicity.
  have hmono := hres.flatRank_le {i}
  -- The pair-unit's `{i}`-flattening has rank exactly `r`.
  have hrank_eq : flatRank (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) {i} = r := by
    -- Row index type `{x // x ∈ {i}}` is `Fin (npf i) = Fin r`; columns carry leg `j`.
    have memi : i ∈ ({i} : Finset (Fin k)) := Finset.mem_singleton_self i
    have memj : j ∉ ({i} : Finset (Fin k)) := by
      rw [Finset.mem_singleton]; exact hij.symm
    have hrowval : ∀ x : { x // x ∈ ({i} : Finset (Fin k)) }, x.val = i :=
      fun x => Finset.mem_singleton.mp x.2
    have hnpf_i : ((naturalPairFormat (⟨r, hr⟩ : ℕ+) i j i : ℕ+) : ℕ) = r := by
      unfold naturalPairFormat; rw [if_pos (Or.inl rfl)]; rfl
    have hnpf_j : ((naturalPairFormat (⟨r, hr⟩ : ℕ+) i j j : ℕ+) : ℕ) = r := by
      unfold naturalPairFormat; rw [if_pos (Or.inr rfl)]; rfl
    -- Row reindex `Fin r ≃ Row`.
    let eRow : Fin r ≃ ((x : { x // x ∈ ({i} : Finset (Fin k)) })
        → Fin (naturalPairFormat (⟨r, hr⟩ : ℕ+) i j x.val)) :=
      { toFun := fun m x => Fin.cast (by rw [hrowval x, hnpf_i]) m
        invFun := fun row => Fin.cast (by rw [hnpf_i]) (row ⟨i, memi⟩)
        left_inv := by intro m; simp
        right_inv := by
          intro row; funext x
          obtain ⟨x, hx⟩ := x
          have hxi : x = i := Finset.mem_singleton.mp hx; subst hxi; simp }
    -- Column reindex `Fin r ≃ Col`: only leg `j` is nontrivial (others are `Fin 1`).
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
            simp only at hxj; subst hxj
            simp
          · simp only [dif_neg hxj]
            -- Both sides land in `Fin 1`.
            have hone : ((naturalPairFormat (⟨r, hr⟩ : ℕ+) i j x.val : ℕ+) : ℕ) = 1 := by
              unfold naturalPairFormat
              rw [if_neg]
              · rfl
              · rintro (h | h)
                · exact x.2 (by rw [Finset.mem_singleton]; exact h)
                · exact hxj h
            apply Fin.ext
            have h1 := (col x).isLt
            have h2 : (⟨0, by omega⟩ : Fin (naturalPairFormat (⟨r, hr⟩ : ℕ+) i j x.val)).val = 0 :=
              rfl
            omega }
    -- The flattening equals the reindexed identity matrix.
    have hid : flattenMatrix (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) {i}
        = Matrix.reindex eRow eCol (1 : Matrix (Fin r) (Fin r) F) := by
      ext rowS colS
      rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]
      change (unitPairTensor (F := F) ⟨r, hr⟩ i j hij)
          (fun x => if h : x ∈ ({i} : Finset (Fin k)) then rowS ⟨x, h⟩
            else colS ⟨x, h⟩) = _
      rw [unitPairTensor]
      rw [dif_pos memi, dif_neg memj]
      -- The leg-`i` coordinate is `rowS ⟨i,memi⟩`, the leg-`j` coordinate is
      -- `colS ⟨j,memj⟩`; the entry is `1` iff their values agree.
      by_cases heq : eRow.symm rowS = eCol.symm colS
      · rw [if_pos heq]
        have : (rowS ⟨i, memi⟩).val = (colS ⟨j, memj⟩).val := by
          have hr' : (eRow.symm rowS).val = (rowS ⟨i, memi⟩).val := by
            change (Fin.cast (by rw [hnpf_i]) (rowS ⟨i, memi⟩)).val = _; rfl
          have hc' : (eCol.symm colS).val = (colS ⟨j, memj⟩).val := by
            change (Fin.cast (by rw [hnpf_j]) (colS ⟨j, memj⟩)).val = _; rfl
          rw [← hr', ← hc', heq]
        rw [if_pos this]
      · rw [if_neg heq]
        rw [if_neg]
        intro hcontra
        apply heq
        apply Fin.ext
        have hr' : (eRow.symm rowS).val = (rowS ⟨i, memi⟩).val := by
          change (Fin.cast (by rw [hnpf_i]) (rowS ⟨i, memi⟩)).val = _; rfl
        have hc' : (eCol.symm colS).val = (colS ⟨j, memj⟩).val := by
          change (Fin.cast (by rw [hnpf_j]) (colS ⟨j, memj⟩)).val = _; rfl
        rw [hr', hc', hcontra]
    rw [flatRank, hid, Matrix.rank_reindex, Matrix.rank_one, Fintype.card_fin]
  rw [hrank_eq] at hmono
  exact hmono

/-- For distinct legs `i ≠ j` of a `2`-tensor, any rank-`r` pair-unit that
    restricts to `T` forces `r ≤ flatRank T {i}`. This is the upper bound that
    makes the `subrankPair` supremum set bounded above (paper tex:880-899): the
    pair-unit's `{i}`-flattening is the rank-`r` identity, and restriction
    factors that flattening through `flattenMatrix T {i}`, so by
    `Matrix.rank_mul_le` its rank `r` is at most `flatRank T {i}`. -/
private lemma pairUnit_restricts_le_flatRank_k2 {d : Fin 2 → ℕ+}
    (T : KTensor F d) (i j : Fin 2) (hij : i ≠ j) {r : ℕ} (hr : 0 < r)
    (hres : Restricts (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) T) :
    r ≤ flatRank T {i} := by
  classical
  obtain ⟨A, hA⟩ := hres
  -- Product over `Fin 2 = {i, j}` splits into the two legs.
  have hprod2 : ∀ (g : Fin 2 → F), (∏ ℓ, g ℓ) = g i * g j := by
    intro g; rw [Fin.prod_univ_two]
    fin_cases i <;> fin_cases j <;>
      [exact absurd rfl hij; rfl; (rw [mul_comm]; rfl); exact absurd rfl hij]
  have memi : i ∈ ({i} : Finset (Fin 2)) := Finset.mem_singleton_self i
  have memj : j ∉ ({i} : Finset (Fin 2)) := by rw [Finset.mem_singleton]; exact hij.symm
  set MT : Matrix _ _ F := flattenMatrix T {i} with hMT_def
  -- Leg matrices transported onto the flattening index types.
  set Pmat : Matrix
      ((x : { x // x ∈ ({i} : Finset (Fin 2)) }) → Fin (naturalPairFormat (⟨r, hr⟩ : ℕ+) i j x.val))
      ((x : { x // x ∈ ({i} : Finset (Fin 2)) }) → Fin (d x.val)) F :=
    fun rowS rowT => A i (rowS ⟨i, memi⟩) (rowT ⟨i, memi⟩) with hPmat_def
  set Qmat : Matrix
      ((x : { x // x ∉ ({i} : Finset (Fin 2)) }) → Fin (d x.val))
      ((x : { x // x ∉ ({i} : Finset (Fin 2)) }) → Fin (naturalPairFormat (⟨r, hr⟩ : ℕ+) i j x.val))
      F :=
    fun colT colS => A j (colS ⟨j, memj⟩) (colT ⟨j, memj⟩) with hQmat_def
  -- The pair-unit's `{i}`-flattening factors as `Pmat * MT * Qmat`.
  have hfactor : flattenMatrix (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) {i}
      = Pmat * MT * Qmat := by
    ext rowS colS
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply]
    -- LHS: unfold flattenMatrix + the Restricts equation.
    change (unitPairTensor (F := F) ⟨r, hr⟩ i j hij)
        (fun x => if h : x ∈ ({i} : Finset (Fin 2)) then rowS ⟨x, h⟩ else colS ⟨x, h⟩) = _
    rw [hA]
    -- Reindex the sum over `idx` by the row/col split.
    rw [← Equiv.sum_comp (Equiv.piEquivPiSubtypeProd (· ∈ ({i} : Finset (Fin 2)))
            (fun x => Fin (d x))).symm
          (fun idx : (∀ x : Fin 2, Fin (d x)) =>
            (∏ i_1, A i_1 (if h : i_1 ∈ ({i} : Finset (Fin 2))
              then rowS ⟨i_1, h⟩ else colS ⟨i_1, h⟩) (idx i_1)) * T idx)]
    rw [Fintype.sum_prod_type]
    -- Massage the RHS `∑ colT (∑ rowT ...) * Qmat` into `∑ rowT ∑ colT ...`.
    rw [show (∑ colT, (∑ rowT, Pmat rowS rowT * MT rowT colT) * Qmat colT colS)
          = ∑ rowT, ∑ colT, Pmat rowS rowT * MT rowT colT * Qmat colT colS from by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro colT _
        rw [Finset.sum_mul]]
    refine Finset.sum_congr rfl ?_
    intro rowT _
    refine Finset.sum_congr rfl ?_
    intro colT _
    rw [hprod2]
    -- Evaluate the combined indices at legs i, j.
    rw [dif_pos memi, dif_neg memj]
    have hti : ((Equiv.piEquivPiSubtypeProd (· ∈ ({i} : Finset (Fin 2)))
        (fun x => Fin (d x))).symm (rowT, colT)) i = rowT ⟨i, memi⟩ := by
      rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos memi]
    have htj : ((Equiv.piEquivPiSubtypeProd (· ∈ ({i} : Finset (Fin 2)))
        (fun x => Fin (d x))).symm (rowT, colT)) j = colT ⟨j, memj⟩ := by
      rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg memj]
    rw [hti, htj]
    rw [hPmat_def, hQmat_def, hMT_def]
    -- Reassemble `T idx` via flattenMatrix and rearrange the scalar product.
    have hTval : T ((Equiv.piEquivPiSubtypeProd (· ∈ ({i} : Finset (Fin 2)))
        (fun x => Fin (d x))).symm (rowT, colT)) = flattenMatrix T {i} rowT colT := by
      rw [flattenMatrix]
      congr 1
    rw [hTval]
    ring
  -- The pair-unit's flattening has rank `r`.
  have hrank_eq : (flattenMatrix (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) {i}).rank = r := by
    have hrowval : ∀ x : { x // x ∈ ({i} : Finset (Fin 2)) }, x.val = i := by
      intro x; exact Finset.mem_singleton.mp x.2
    have hcolval : ∀ x : { x // x ∉ ({i} : Finset (Fin 2)) }, x.val = j := by
      intro x; obtain ⟨x, hx⟩ := x; rw [Finset.mem_singleton] at hx
      fin_cases i <;> fin_cases j <;> simp_all <;> omega
    have hnpf : ∀ ℓ : Fin 2, ℓ = i ∨ ℓ = j →
        ((naturalPairFormat (⟨r, hr⟩ : ℕ+) i j ℓ : ℕ+) : ℕ) = r := by
      intro ℓ hℓ; unfold naturalPairFormat; rw [if_pos hℓ]; rfl
    -- Row/col index types reindex to `Fin r`.
    let eRow : Fin r ≃
        ((x : { x // x ∈ ({i} : Finset (Fin 2)) })
          → Fin (naturalPairFormat (⟨r, hr⟩ : ℕ+) i j x.val)) :=
      { toFun := fun m x => Fin.cast (hnpf x.val (Or.inl (hrowval x))).symm m
        invFun := fun row => Fin.cast (hnpf i (Or.inl rfl)) (row ⟨i, memi⟩)
        left_inv := by intro m; simp
        right_inv := by
          intro row; funext x; obtain ⟨x, hx⟩ := x
          have hxi : x = i := Finset.mem_singleton.mp hx; subst hxi; simp }
    let eCol : Fin r ≃
        ((x : { x // x ∉ ({i} : Finset (Fin 2)) })
          → Fin (naturalPairFormat (⟨r, hr⟩ : ℕ+) i j x.val)) :=
      { toFun := fun m x => Fin.cast (hnpf x.val (Or.inr (hcolval x))).symm m
        invFun := fun col => Fin.cast (hnpf j (Or.inr rfl)) (col ⟨j, memj⟩)
        left_inv := by intro m; simp
        right_inv := by
          intro col; funext x; obtain ⟨x, hx⟩ := x
          have hxj : x = j := by
            have := hcolval ⟨x, hx⟩; simpa using this
          subst hxj; simp }
    -- The flattening equals the reindexed identity matrix.
    have hid : flattenMatrix (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) {i}
        = Matrix.reindex eRow eCol (1 : Matrix (Fin r) (Fin r) F) := by
      ext rowS colS
      rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]
      change (unitPairTensor (F := F) ⟨r, hr⟩ i j hij)
          (fun x => if h : x ∈ ({i} : Finset (Fin 2)) then rowS ⟨x, h⟩ else colS ⟨x, h⟩) = _
      rw [unitPairTensor]
      rw [dif_pos memi, dif_neg memj]
      by_cases heq : (rowS ⟨i, memi⟩).val = (colS ⟨j, memj⟩).val
      · rw [if_pos heq, if_pos]
        apply Fin.ext; simpa using heq
      · rw [if_neg heq, if_neg]
        intro hcontra; apply heq
        have := congrArg Fin.val hcontra; simpa using this
    rw [hid, Matrix.rank_reindex, Matrix.rank_one, Fintype.card_fin]
  -- Combine: r = rank(flatten S) ≤ rank MT = flatRank T {i}.
  have : (flattenMatrix (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) {i}).rank ≤ MT.rank := by
    rw [hfactor]
    calc (Pmat * MT * Qmat).rank ≤ (Pmat * MT).rank :=
          (Matrix.rank_mul_le _ _).trans (min_le_left _ _)
      _ ≤ MT.rank := (Matrix.rank_mul_le _ _).trans (min_le_right _ _)
  rw [hrank_eq] at this
  exact this

/-- Matrix-rank normal form for the two-leg pair-subrank.

For a `2`-tensor and distinct legs `i,j`, the singleton flattening
`flattenMatrix T {i}` has rank `r = flatRank T {i}`. Choosing `r` independent
columns and the linear left inverse of the induced map gives leg-wise matrices
which send `T` to the rank-`r` pair-unit `⟨r⟩_{i,j}`. Consequently `r` belongs
to the set whose supremum defines `subrankPair T i j`, so the supremum is at
least `r`.

This is the only place where the Smith/rank-factorisation step and the
singleton-index transports between `flattenMatrix` and `Restricts` are used. -/
private lemma flatRank_le_pairUnitRestriction_sSup_k2 {d : Fin 2 → ℕ+}
    (T : KTensor F d) (i j : Fin 2) (hij : i ≠ j) :
    flatRank T {i} ≤ sSup { r : ℕ | ∃ hr : 0 < r,
      Restricts (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) T } := by
  /- Paper tex:880-899 (proof of Theorem 3.2, base case k = 2): in the base
     case `subrank_{1,2}` and `tensorrank_{1}` coincide because both equal the
     matrix rank. Given `r = flatRank T {i}`, we produce a `Restricts` witness
     for the rank-`r` pair-unit via the rank factorisation of
     `M = flattenMatrix T {i}`: get a linear-equivalence with `range φ`, a left
     inverse of the inclusion (`LinearMap.exists_leftInverse_of_injective`) and
     a right inverse of the coordinate map (`LinearMap.exists_rightInverse_of_surjective`),
     producing leg-wise matrices `A_i, A_j` with `A_i M A_j^T = I_r`.

     Below we establish the linear-algebraic core (the matrix identity
     `A * M * B = 1` and the `(Fin r → F) ≃ₗ[F] range φ` equivalence), then
     transport this matrix identity to the `Restricts` equation over the
     singleton-index dependent function types `∀ x ∈ {i}, Fin (d x)` ≃
     `Fin (d i)` (and analogously for `Col` ≃ `Fin (d j)`, using `i ≠ j` and
     `k = 2`). The supremum's boundedness above is supplied by
     `pairUnit_restricts_le_flatRank_k2`. -/
  classical
  -- Trivial case: rank zero.
  by_cases hr0 : flatRank T {i} = 0
  · rw [hr0]; exact Nat.zero_le _
  have hr_pos : 0 < flatRank T {i} := Nat.pos_of_ne_zero hr0
  -- The associated linear map and its range.
  set M : Matrix _ _ F := flattenMatrix T {i} with hM_def
  set r : ℕ := M.rank with hr_def
  set φ : _ →ₗ[F] _ := M.mulVecLin with hφ_def
  have hrange_dim : Module.finrank F (LinearMap.range φ) = r := rfl
  -- Choose a linear equivalence `(Fin r → F) ≃ₗ[F] LinearMap.range φ`.
  obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
      (R := F) (M := Fin r → F) (M' := LinearMap.range φ)
      (by rw [Module.finrank_fin_fun]; exact hrange_dim.symm)
  -- U injective, V surjective; factor φ = U ∘ V.
  set U : (Fin r → F) →ₗ[F] _ :=
    (LinearMap.range φ).subtype ∘ₗ e.toLinearMap with hU_def
  have hU_inj : Function.Injective U := fun x y hxy =>
    e.injective (Subtype.ext hxy)
  set φ' : _ →ₗ[F] LinearMap.range φ :=
    φ.codRestrict (LinearMap.range φ) (fun v => LinearMap.mem_range_self φ v) with hφ'_def
  set V : _ →ₗ[F] (Fin r → F) := e.symm.toLinearMap ∘ₗ φ' with hV_def
  have hV_surj : Function.Surjective V := by
    refine e.symm.surjective.comp ?_
    intro y
    obtain ⟨v, hv⟩ := y.2
    exact ⟨v, Subtype.ext hv⟩
  have hφ_eq : φ = U ∘ₗ V := by
    apply LinearMap.ext
    intro c
    change φ c = (LinearMap.range φ).subtype (e (e.symm (φ' c)))
    rw [e.apply_symm_apply]
    rfl
  -- Left/right inverses give the matrix identity A * M * B = 1.
  obtain ⟨A_lin, hAU⟩ := LinearMap.exists_leftInverse_of_injective U
    (LinearMap.ker_eq_bot_of_injective hU_inj)
  obtain ⟨B_lin, hVB⟩ := LinearMap.exists_rightInverse_of_surjective V
    (LinearMap.range_eq_top.mpr hV_surj)
  have hkey : (A_lin ∘ₗ φ) ∘ₗ B_lin = LinearMap.id := by
    rw [hφ_eq]
    have h1 : (A_lin ∘ₗ (U ∘ₗ V)) ∘ₗ B_lin = (A_lin ∘ₗ U) ∘ₗ (V ∘ₗ B_lin) := by
      apply LinearMap.ext; intro x; rfl
    rw [h1, hAU, hVB]
    apply LinearMap.ext; intro x; rfl
  set A := LinearMap.toMatrix' A_lin with hA_def
  set B := LinearMap.toMatrix' B_lin with hB_def
  have _hAMB : A * M * B = (1 : Matrix (Fin r) (Fin r) F) := by
    have heq : A * M * B = LinearMap.toMatrix' ((A_lin ∘ₗ φ) ∘ₗ B_lin) := by
      rw [hA_def, hB_def]
      rw [show (A_lin ∘ₗ φ) ∘ₗ B_lin = A_lin ∘ₗ (φ ∘ₗ B_lin) by
            apply LinearMap.ext; intro x; rfl]
      rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp]
      rw [show LinearMap.toMatrix' φ = M by
            rw [hφ_def]; exact (LinearMap.toMatrix'_toLin' M)]
      exact Matrix.mul_assoc _ _ _
    rw [heq, hkey, LinearMap.toMatrix'_id]
  /- Transport the matrix identity `A * M * B = 1` into the leg-wise `Restricts`
     equation for `unitPairTensor ⟨r, hr_pos⟩ i j hij` via the singleton-index
     `Row ≃ Fin (d i)` / `Col ≃ Fin (d j)` equivalences (paper tex:880-899). -/
  have hrr : r = flatRank T {i} := by rw [hr_def, hM_def]; rfl
  rw [← hrr]
  -- `r` is a positive member of the supremum set, and the set is bounded above.
  have hpos : 0 < r := hrr ▸ hr_pos
  have memi : i ∈ ({i} : Finset (Fin 2)) := Finset.mem_singleton_self i
  have memj : j ∉ ({i} : Finset (Fin 2)) := by rw [Finset.mem_singleton]; exact hij.symm
  have hprod2 : ∀ (g : Fin 2 → F), (∏ ℓ, g ℓ) = g i * g j := by
    intro g; rw [Fin.prod_univ_two]
    fin_cases i <;> fin_cases j <;>
      [exact absurd rfl hij; rfl; (rw [mul_comm]; rfl); exact absurd rfl hij]
  have hnpf : ∀ ℓ : Fin 2, ℓ = i ∨ ℓ = j →
      ((naturalPairFormat (⟨r, hpos⟩ : ℕ+) i j ℓ : ℕ+) : ℕ) = r := by
    intro ℓ hℓ; unfold naturalPairFormat; rw [if_pos hℓ]; rfl
  have hrowval : ∀ x : { x // x ∈ ({i} : Finset (Fin 2)) }, x.val = i :=
    fun x => Finset.mem_singleton.mp x.2
  have hcolval : ∀ x : { x // x ∉ ({i} : Finset (Fin 2)) }, x.val = j := by
    rintro ⟨x, hx⟩; rw [Finset.mem_singleton] at hx
    change x = j
    have hxi : x.val ≠ i.val := fun h => hx (Fin.ext h)
    have hji : j.val ≠ i.val := fun h => hij (Fin.ext h).symm
    apply Fin.ext
    have hx2 := x.isLt; have hi2 := i.isLt; have hj2 := j.isLt; omega
  -- Singleton row/col builders: `Fin (d i) → Row`, `Fin (d j) → Col`.
  let rowOf : Fin (d i) →
      ((x : { x // x ∈ ({i} : Finset (Fin 2)) }) → Fin (d x.val)) :=
    fun q x => Fin.cast (by rw [hrowval x]) q
  let colOf : Fin (d j) →
      ((x : { x // x ∉ ({i} : Finset (Fin 2)) }) → Fin (d x.val)) :=
    fun q x => Fin.cast (by rw [hcolval x]) q
  have hcase : ∀ ℓ : Fin 2, ℓ = i ∨ ℓ = j := by
    intro ℓ
    have hji : j.val ≠ i.val := fun h => hij (Fin.ext h).symm
    have hl2 := ℓ.isLt; have hi2 := i.isLt; have hj2 := j.isLt
    rcases Nat.lt_or_ge ℓ.val i.val with h | h
    · right; apply Fin.ext; omega
    · rcases Nat.eq_or_lt_of_le h with h' | h'
      · left; exact Fin.ext h'.symm
      · right; apply Fin.ext; omega
  -- Leg matrices: leg `i` from `A`, leg `j` from `B`, transported to `Fin r`.
  set Alegs : ∀ ℓ : Fin 2,
      Matrix (Fin (naturalPairFormat (⟨r, hpos⟩ : ℕ+) i j ℓ)) (Fin (d ℓ)) F :=
    fun ℓ => if hℓ : ℓ = i then
        (fun p q => A (Fin.cast (hnpf ℓ (Or.inl hℓ)) p) (rowOf (hℓ ▸ q)))
      else if hℓ' : ℓ = j then
        (fun p q => B (colOf (hℓ' ▸ q)) (Fin.cast (hnpf ℓ (Or.inr hℓ')) p))
      else 0 with hAlegs_def
  refine le_csSup ?_ ?_
  · -- BddAbove: every member is ≤ flatRank T {i}.
    refine ⟨flatRank T {i}, ?_⟩
    rintro s ⟨hs, hres⟩
    exact pairUnit_restricts_le_flatRank_k2 T i j hij hs hres
  · -- Membership: `r = flatRank T {i}` has the pair-unit restriction witness.
    refine ⟨hpos, Alegs, ?_⟩
    intro jdx
    set a : Fin r := Fin.cast (hnpf i (Or.inl rfl)) (jdx i) with ha_def
    set b : Fin r := Fin.cast (hnpf j (Or.inr rfl)) (jdx j) with hb_def
    -- Evaluate the leg matrices and reduce the RHS to `(A * M * B) a b`.
    have hAlegs_i : ∀ (q : Fin (d i)), Alegs i (jdx i) q = A a (rowOf q) := by
      intro q
      simp only [hAlegs_def, dif_pos (rfl : i = i)]
      rfl
    have hAlegs_j : ∀ (q : Fin (d j)), Alegs j (jdx j) q = B (colOf q) b := by
      intro q
      simp only [hAlegs_def, dif_neg hij.symm]
      rfl
    have hrhs : (∑ idx, (∏ ℓ, Alegs ℓ (jdx ℓ) (idx ℓ)) * T idx) = (A * M * B) a b := by
      rw [Matrix.mul_apply]
      simp_rw [Matrix.mul_apply, Finset.sum_mul]
      -- Reindex `∑ idx` by the row/col split.
      rw [← Equiv.sum_comp (Equiv.piEquivPiSubtypeProd (· ∈ ({i} : Finset (Fin 2)))
              (fun x => Fin (d x))).symm
            (fun idx : (∀ x : Fin 2, Fin (d x)) =>
              (∏ ℓ, Alegs ℓ (jdx ℓ) (idx ℓ)) * T idx)]
      rw [Fintype.sum_prod_type]
      -- RHS is `∑ rowT, ∑ k, A a rowT * M rowT k * B k b`.
      rw [show (∑ k, ∑ k_1, A a k_1 * M k_1 k * B k b)
            = ∑ rowT, ∑ colT, A a rowT * M rowT colT * B colT b from by
          rw [Finset.sum_comm]]
      refine Finset.sum_congr rfl ?_
      intro rowT _
      refine Finset.sum_congr rfl ?_
      intro colT _
      rw [hprod2, hAlegs_i, hAlegs_j]
      -- The reindexed `idx` evaluates to `rowT`/`colT` at legs `i`/`j`.
      have hti : ((Equiv.piEquivPiSubtypeProd (· ∈ ({i} : Finset (Fin 2)))
          (fun x => Fin (d x))).symm (rowT, colT)) i = rowT ⟨i, memi⟩ := by
        rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos memi]
      have htj : ((Equiv.piEquivPiSubtypeProd (· ∈ ({i} : Finset (Fin 2)))
          (fun x => Fin (d x))).symm (rowT, colT)) j = colT ⟨j, memj⟩ := by
        rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg memj]
      rw [hti, htj]
      -- `rowOf (rowT ⟨i,memi⟩) = rowT` and `colOf (colT ⟨j,memj⟩) = colT`.
      have hrow : rowOf (rowT ⟨i, memi⟩) = rowT := by
        funext x; obtain ⟨x, hx⟩ := x
        have hxi : x = i := Finset.mem_singleton.mp hx; subst hxi
        rfl
      have hcol : colOf (colT ⟨j, memj⟩) = colT := by
        funext x
        have hxj : x.val = j := hcolval x
        obtain ⟨x, hx⟩ := x; simp only at hxj; subst hxj
        rfl
      rw [hrow, hcol]
      -- `T (combine rowT colT) = M rowT colT`.
      have hTval : T ((Equiv.piEquivPiSubtypeProd (· ∈ ({i} : Finset (Fin 2)))
          (fun x => Fin (d x))).symm (rowT, colT)) = M rowT colT := by
        rw [hM_def, flattenMatrix]; congr 1
      rw [hTval]; ring
    rw [hrhs, _hAMB, Matrix.one_apply]
    rw [unitPairTensor]
    -- Match the `if`-conditions: `a = b ↔ (jdx i).val = (jdx j).val`.
    by_cases heq : (jdx i).val = (jdx j).val
    · rw [if_pos heq, if_pos]; rw [ha_def, hb_def]; apply Fin.ext; simpa using heq
    · rw [if_neg heq, if_neg]; intro hcontra; apply heq
      rw [ha_def, hb_def] at hcontra
      have := congrArg Fin.val hcontra; simpa using this

private lemma subrankPair_ge_flatRank_k2_singleton {d : Fin 2 → ℕ+}
    (T : KTensor F d) (i j : Fin 2) (hij : i ≠ j) :
    flatRank T {i} ≤ subrankPair T i j := by
  classical
  unfold subrankPair
  split_ifs with h
  · exact False.elim (hij h)
  · exact flatRank_le_pairUnitRestriction_sSup_k2 T i j h

/-- **General-arity `subrankPair` supremum set is bounded above (tex:836).**
    For any `k`-tensor `T` and legs `i ≠ j`, the set of positive `r` with
    `⟨r⟩_{i,j} ≤ₜ T` is bounded above by `flatRank T {i}` (via
    `pairUnit_restricts_le_flatRank`). This makes the `subrankPair` supremum a
    genuine maximum and unlocks `ℕ`-`sSup` monotonicity. -/
private lemma subrankPair_bddAbove {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (i j : Fin k) (hij : i ≠ j) :
    BddAbove { r : ℕ | ∃ hr : 0 < r,
      Restricts (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) T } := by
  refine ⟨flatRank T {i}, ?_⟩
  rintro s ⟨hs, hres⟩
  exact pairUnit_restricts_le_flatRank T i j hij hs hres

/-- **`subrankPair` is monotone under restriction (tex:392, 836).** If `S ≤ₜ T`
    then `subrankPair S i j ≤ subrankPair T i j`: every rank-`r` pair-unit that
    restricts to `S` also restricts to `T` (transitivity of `≤ₜ`), so `S`'s
    supremum set is a subset of `T`'s, and both sets are bounded above. -/
lemma subrankPair_mono_of_restricts {k : ℕ} {dS dT : Fin k → ℕ+}
    {S : KTensor F dS} {T : KTensor F dT} (hST : Restricts S T) (i j : Fin k) :
    subrankPair S i j ≤ subrankPair T i j := by
  classical
  unfold subrankPair
  split_ifs with hij
  · exact le_refl 0
  · -- `S`'s restricting set ⊆ `T`'s restricting set; `T`'s is bounded above.
    set sS := { r : ℕ | ∃ hr : 0 < r,
      Restricts (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) S } with hsS
    set sT := { r : ℕ | ∃ hr : 0 < r,
      Restricts (unitPairTensor (F := F) ⟨r, hr⟩ i j hij) T } with hsT
    have hsub : sS ⊆ sT := by
      rintro s ⟨hs, hres⟩
      exact ⟨hs, hres.trans hST⟩
    rcases Set.eq_empty_or_nonempty sS with hempty | hne
    · rw [hempty, show sSup (∅ : Set ℕ) = 0 from by simp]
      exact Nat.zero_le _
    · exact csSup_le_csSup (subrankPair_bddAbove T i j hij) hne hsub

/-! ## Kronecker multiplicativity of flatRank (paper tex:393).

Paper tex:393 verbatim: "For two `k`-tensors `S` and `T` their Kronecker
product `S ⊠ T` is the `k`-tensor obtained by taking the tensor product and
grouping corresponding legs."

Combined with paper tex:378-380 (the `flatRank` definition as matrix rank of
the `I`-flattening), this gives Kronecker multiplicativity of `flatRank`:
the `j`-flattening of `S ⊠ T` is the matrix Kronecker product of the
`j`-flattenings of `S` and `T`, and matrix rank is multiplicative under
Kronecker product. We only need the `≥`-direction.

The proof is direct, without going through an abstract `Matrix.kroneckerMap`
detour: we pick linearly independent column families of the `j`-flattenings
of `S` and `T`, then assemble `(flatRank S {j}) * (flatRank T {j})` linearly
independent columns of the `j`-flattening of `S ⊠ T`, indexed by pairs of
the chosen column indices.

The key entry-wise identity is:
  (S ⊠ T)(combine row col_kron) = S(combine rowS col_S) * T(combine rowT col_T)
where `(rowS, rowT)` is the per-leg `finProdFinEquiv.symm`-split of `row`,
and `col_kron i = finProdFinEquiv (col_S i, col_T i)`. -/

/-- **Linear independence of "Kronecker products" of two linearly independent
    families of functions** (the load-bearing lemma for Kronecker rank
    multiplicativity, paper tex:393).

    For finite types `α₁, α₂`, families `fM : Fin r1 → (α₁ → F)` and
    `fN : Fin r2 → (α₂ → F)` linearly independent, the "Kronecker product"
    family `g : Fin r1 × Fin r2 → (α₁ × α₂ → F)` defined by
    `g (p1, p2) (q1, q2) = fM p1 q1 * fN p2 q2` is also linearly independent.

    Standard tensor-product LI fact, proven by a 2-fix `q2`, use LI of `fM` to extract per-`p1`
    relations in `fN`;
    fix `p1`, use LI of `fN` to conclude. -/
private lemma linearIndependent_kron_of
    {α₁ α₂ : Type*} {r1 r2 : ℕ}
    {fM : Fin r1 → (α₁ → F)} {fN : Fin r2 → (α₂ → F)}
    (hfM : LinearIndependent F fM) (hfN : LinearIndependent F fN) :
    LinearIndependent F (fun p : Fin r1 × Fin r2 =>
      (fun q : α₁ × α₂ => fM p.1 q.1 * fN p.2 q.2)) := by
  classical
  rw [linearIndependent_iff']
  intro s coef hsum p hp
  -- Pointwise: ∀ q, ∑ p ∈ s, coef p * (fM p.1 q.1 * fN p.2 q.2) = 0.
  have hsum_apply : ∀ q : α₁ × α₂,
      ∑ p ∈ s, coef p * (fM p.1 q.1 * fN p.2 q.2) = 0 := by
    intro q
    have := congrArg (fun f : α₁ × α₂ → F => f q) hsum
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
  -- Fiberwise split on the first coordinate.
  have hsum_split : ∀ q1 : α₁, ∀ q2 : α₂,
      ∑ p1 : Fin r1, (∑ p ∈ s.filter (fun p => p.1 = p1), coef p * fN p.2 q2) *
          fM p1 q1 = 0 := by
    intro q1 q2
    rw [← hsum_apply (q1, q2)]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : Fin r1 × Fin r2 => p.1)
          (s := s) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl ?_
    intro p1 _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨_, hp1⟩
    subst hp1
    ring
  -- LI of fM (at each q2) → per-p1 fN relations.
  have hcoef_fM_zero : ∀ q2 : α₂, ∀ p1 : Fin r1,
      (∑ p ∈ s.filter (fun p => p.1 = p1), coef p * fN p.2 q2) = 0 := by
    intro q2 p1
    rw [linearIndependent_iff'] at hfM
    refine hfM Finset.univ
      (fun p1 => ∑ p ∈ s.filter (fun p => p.1 = p1), coef p * fN p.2 q2)
      ?_ p1 (Finset.mem_univ _)
    ext q1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hsum_split q1 q2]
  -- At each p1, the filtered sum (as a function of q2) is zero.
  have hcoef_fM_zero_fn : ∀ p1 : Fin r1,
      (∑ p ∈ s.filter (fun p => p.1 = p1), coef p • fN p.2 : α₂ → F) = 0 := by
    intro p1
    ext q2
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact hcoef_fM_zero q2 p1
  -- For p = (p1, p2), reindex over second coord and apply LI of fN.
  obtain ⟨p1, p2⟩ := p
  rw [linearIndependent_iff'] at hfN
  have hrel := hcoef_fM_zero_fn p1
  set s2 : Finset (Fin r2) := (s.filter (fun p => p.1 = p1)).image (fun p => p.2)
  have h_inject : Set.InjOn (fun p : Fin r1 × Fin r2 => p.2)
      ↑(s.filter (fun p => p.1 = p1)) := by
    intro x hx y hy hxy
    rcases Finset.mem_filter.mp hx with ⟨_, hx1⟩
    rcases Finset.mem_filter.mp hy with ⟨_, hy1⟩
    apply Prod.ext
    · rw [hx1, hy1]
    · exact hxy
  have hrel' : (∑ p2' ∈ s2, coef (p1, p2') • fN p2' : α₂ → F) = 0 := by
    rw [show (∑ p2' ∈ s2, coef (p1, p2') • fN p2' : α₂ → F)
          = ∑ p ∈ s.filter (fun p => p.1 = p1), coef p • fN p.2 from ?_]
    · exact hrel
    · rw [Finset.sum_image]
      · refine Finset.sum_congr rfl ?_
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨_, hp1⟩
        have : coef (p1, p.2) = coef p := by rw [← hp1]
        rw [this]
      · intro x hx y hy hxy
        exact h_inject hx hy hxy
  have h_p2_in_s2 : p2 ∈ s2 :=
    Finset.mem_image.mpr ⟨(p1, p2), Finset.mem_filter.mpr ⟨hp, rfl⟩, rfl⟩
  refine hfN s2 (fun p2' => coef (p1, p2')) ?_ p2 h_p2_in_s2
  ext q2
  have := congrArg (fun f : α₂ → F => f q2) hrel'
  simp only at this
  simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this

/-- **Helper (paper tex:393)**: For any matrices `M : Matrix m n F` and
    `N : Matrix m' n' F` with finite row and column types,
    `M.rank * N.rank ≤ (Matrix.kroneckerMap (· * ·) M N).rank`.

    Proof: pick `M.rank` columns of `M` whose span has dimension `M.rank` (by
    `Submodule.exists_fun_fin_finrank_span_eq`); similarly for `N`. Show
    the corresponding `M.rank * N.rank` columns of `kroneckerMap (·*·) M N`
    (indexed by pairs of chosen column indices) are linearly independent in
    `(Fin a × Fin c → F)` via `linearIndependent_kron_of`.

    Mathlib hooks: `Submodule.exists_fun_fin_finrank_span_eq` (basis
    extraction), `finrank_span_eq_card` (rank bound from linear independence),
    `Matrix.rank_eq_finrank_span_cols`. -/
lemma rank_kroneckerMap_mul_ge
    {a b c₁ d₁ : ℕ} (M : Matrix (Fin a) (Fin b) F) (N : Matrix (Fin c₁) (Fin d₁) F) :
    M.rank * N.rank ≤ (Matrix.kroneckerMap (· * ·) M N).rank := by
  classical
  have hM : M.rank = Module.finrank F (Submodule.span F (Set.range M.col)) :=
    M.rank_eq_finrank_span_cols
  have hN : N.rank = Module.finrank F (Submodule.span F (Set.range N.col)) :=
    N.rank_eq_finrank_span_cols
  obtain ⟨fM, hfM_mem, _, hfM_li⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq F (Set.range M.col)
  obtain ⟨fN, hfN_mem, _, hfN_li⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq F (Set.range N.col)
  choose jM hjM using fun i => hfM_mem i
  choose jN hjN using fun i => hfN_mem i
  let MN : Matrix (Fin a × Fin c₁) (Fin b × Fin d₁) F :=
      Matrix.kroneckerMap (· * ·) M N
  -- The candidate column-vector family: g (p1, p2) = "fM p1 ⊗ fN p2"
  let g : Fin (Module.finrank F (Submodule.span F (Set.range M.col))) ×
          Fin (Module.finrank F (Submodule.span F (Set.range N.col))) →
          (Fin a × Fin c₁ → F) :=
      fun p q => fM p.1 q.1 * fN p.2 q.2
  -- Each `g (p1, p2)` equals the `MN`-column at `(jM p1, jN p2)`.
  have hg_is_col : ∀ p, g p = MN.col (jM p.1, jN p.2) := by
    intro p
    funext q
    have h1 : M q.1 (jM p.1) = fM p.1 q.1 := by
      have heq : M.col (jM p.1) q.1 = (fM p.1) q.1 := by rw [hjM p.1]
      simpa [Matrix.col_apply] using heq
    have h2 : N q.2 (jN p.2) = fN p.2 q.2 := by
      have heq : N.col (jN p.2) q.2 = (fN p.2) q.2 := by rw [hjN p.2]
      simpa [Matrix.col_apply] using heq
    change fM p.1 q.1 * fN p.2 q.2 = MN q (jM p.1, jN p.2)
    simp [MN, Matrix.kroneckerMap_apply, h1, h2]
  -- LI of `g` from LI of `fM`, `fN`.
  have hg_li : LinearIndependent F g :=
    linearIndependent_kron_of (F := F) hfM_li hfN_li
  -- finrank (span g) = r1 * r2.
  have hspan_dim : Module.finrank F (Submodule.span F (Set.range g)) =
      Module.finrank F (Submodule.span F (Set.range M.col)) *
      Module.finrank F (Submodule.span F (Set.range N.col)) := by
    rw [finrank_span_eq_card hg_li, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
  -- Each `g p` is a column of `MN`, so the span ⊆ column-span ⊆ `MN.rank`.
  have hrank_MN : (Module.finrank F (Submodule.span F (Set.range g))) ≤ MN.rank := by
    rw [MN.rank_eq_finrank_span_cols]
    apply Submodule.finrank_mono
    rw [Submodule.span_le]
    rintro v ⟨p, rfl⟩
    rw [hg_is_col]
    exact Submodule.subset_span ⟨(jM p.1, jN p.2), rfl⟩
  rw [hM, hN]
  rw [← hspan_dim]
  exact hrank_MN

/-! ## flatRank Kronecker multiplicativity, paper tex:393. -/

/-- **Per-leg PNat-product equivalence (paper tex:393 engineering)**: for any
    `dS dT : ℕ+`, the type `Fin (dS * dT)` is equivalent to `Fin dS × Fin dT`
    via Mathlib's `finProdFinEquiv` (composed with the PNat coercion).

    Used as the per-leg row/col index split for `flatRank_kron_mul_le`. -/
private def kronLegEquiv (dS dT : ℕ+) :
    Fin ((dS * dT : ℕ+) : ℕ) ≃ Fin (dS : ℕ) × Fin (dT : ℕ) :=
  (Fin.castOrderIso (PNat.mul_coe dS dT)).toEquiv.trans finProdFinEquiv.symm

/-- **Kronecker multiplicativity of flatRank, singleton case** (paper tex:393,
    `\label{subsec:prelim}`).

    Paper tex:393 verbatim: "For two `k`-tensors `S` and `T` their Kronecker
    product `S ⊠ T` is the `k`-tensor obtained by taking the tensor product
    and grouping corresponding legs."

    Combined with paper tex:378-380 (the `flatRank` definition), this gives
    `flatRank S {j} * flatRank T {j} ≤ flatRank (S ⊠ T) {j}`.

    Proof outline: pick linearly independent column families
    `fS : Fin (flatRank S {j}) → (RowS → F)` and `fT` of the `S`- and
    `T`-flattenings via `Submodule.exists_fun_fin_finrank_span_eq`. The
    "Kronecker product" family
    `gPair (p1, p2) (rowS, rowT) := fS p1 rowS * fT p2 rowT`
    is linearly independent in `(RowS × RowT → F)` (`linearIndependent_kron_of`).
    Composing with the row-split bijection `rowSplit : RowST ≃ RowS × RowT`
    (per-leg `kronLegEquiv`) preserves LI, and each `gCol p` is exactly the
    column of `flattenMatrix (S ⊠ T) {j}` at the column index obtained by
    combining the chosen S- and T-column indices leg-wise via
    `(kronLegEquiv _ _).symm`. Hence `flatRank (S ⊠ T) {j} ≥ r1 * r2`. -/
lemma flatRank_kron_mul_le {k : ℕ} {dS dT : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT) (j : Fin k) :
    flatRank S {j} * flatRank T {j} ≤ flatRank (S ⊠ T) {j} := by
  classical
  -- Per-leg row/col-index split.
  let RowST := ∀ i : {i : Fin k // i ∈ ({j} : Finset (Fin k))},
    Fin ((dS i.val * dT i.val : ℕ+) : ℕ)
  let RowS := ∀ i : {i : Fin k // i ∈ ({j} : Finset (Fin k))}, Fin ((dS i.val : ℕ+) : ℕ)
  let RowT := ∀ i : {i : Fin k // i ∈ ({j} : Finset (Fin k))}, Fin ((dT i.val : ℕ+) : ℕ)
  let ColST := ∀ i : {i : Fin k // i ∉ ({j} : Finset (Fin k))},
    Fin ((dS i.val * dT i.val : ℕ+) : ℕ)
  let ColS := ∀ i : {i : Fin k // i ∉ ({j} : Finset (Fin k))}, Fin ((dS i.val : ℕ+) : ℕ)
  let ColT := ∀ i : {i : Fin k // i ∉ ({j} : Finset (Fin k))}, Fin ((dT i.val : ℕ+) : ℕ)
  -- Per-leg row/col split via kronLegEquiv (this is just finProdFinEquiv.symm modulo cast).
  let rowSplitS : RowST → RowS :=
    fun row i => (kronLegEquiv (dS i.val) (dT i.val) (row i)).1
  let rowSplitT : RowST → RowT :=
    fun row i => (kronLegEquiv (dS i.val) (dT i.val) (row i)).2
  let colCombine : ColS → ColT → ColST :=
    fun cS cT i => (kronLegEquiv (dS i.val) (dT i.val)).symm (cS i, cT i)
  -- Step 1: Pick linearly independent column families of S- and T-flattenings.
  have hS := (flattenMatrix S {j}).rank_eq_finrank_span_cols
  have hT := (flattenMatrix T {j}).rank_eq_finrank_span_cols
  obtain ⟨fS, hfS_mem, _, hfS_li⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq F (Set.range (flattenMatrix S {j}).col)
  obtain ⟨fT, hfT_mem, _, hfT_li⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq F (Set.range (flattenMatrix T {j}).col)
  choose jS hjS using fun i => hfS_mem i
  choose jT hjT using fun i => hfT_mem i
  -- Step 2: LI of the "Kronecker product" family on RowS × RowT.
  have hgPair_li : LinearIndependent F
      (fun p : Fin (Module.finrank F (Submodule.span F (Set.range (flattenMatrix S {j}).col))) ×
         Fin (Module.finrank F (Submodule.span F (Set.range (flattenMatrix T {j}).col))) =>
       fun (rowPair : RowS × RowT) => fS p.1 rowPair.1 * fT p.2 rowPair.2) :=
    linearIndependent_kron_of (F := F) hfS_li hfT_li
  -- Step 3: gCol p is a column of flattenMatrix (S ⊠ T) {j}.
  -- Define the column-index map and the LI-preserving reindex.
  -- Each `gCol p` equals the column of `flattenMatrix (S ⊠ T) {j}` at colIdx p.
  -- For row : RowST, gCol p row = (S ⊠ T) row_extended_with_colIdx (jS p.1, jT p.2).
  -- Specifically:
  --   gCol p row = fS p.1 (rowSplitS row) * fT p.2 (rowSplitT row)
  --             = flattenMatrix S {j} (rowSplitS row) (jS p.1) *
  --               flattenMatrix T {j} (rowSplitT row) (jT p.2)
  --             = S (combine_S (rowSplitS row) (jS p.1)) *
  --               T (combine_T (rowSplitT row) (jT p.2))
  --             = (S ⊠ T) (combine_ST row (colCombine (jS p.1) (jT p.2)))
  --   = (flattenMatrix (S ⊠ T) {j}) row (colCombine (jS p.1) (jT p.2)).
  -- The last identity uses: for each i, kronLeftIndex/kronRightIndex of the
  -- combined index extracts rowSplitS/T row when i ∈ {j}, and (jS, jT) p when
  -- i ∉ {j}.
  set colIdx : Fin (Module.finrank F (Submodule.span F (Set.range (flattenMatrix S {j}).col))) ×
        Fin (Module.finrank F (Submodule.span F (Set.range (flattenMatrix T {j}).col))) → ColST :=
      fun p => colCombine (jS p.1) (jT p.2) with hcolIdx_def
  -- The kronLegEquiv ↔ kronLeftIndex relationship: for any
  -- `idx : ∀ i, Fin (dS i * dT i)`, `kronLeftIndex idx i = (kronLegEquiv (dS i) (dT i) (idx i)).1`.
  have hkronL : ∀ {dS' dT' : Fin k → ℕ+} (idx : ∀ i, Fin (dS' i * dT' i)) (i : Fin k),
      kronLeftIndex (dS := dS') (dT := dT') idx i =
      (kronLegEquiv (dS' i) (dT' i) (idx i)).1 := by
    intro dS' dT' idx i
    simp [kronLeftIndex, kronLegEquiv]
  have hkronR : ∀ {dS' dT' : Fin k → ℕ+} (idx : ∀ i, Fin (dS' i * dT' i)) (i : Fin k),
      kronRightIndex (dS := dS') (dT := dT') idx i =
      (kronLegEquiv (dS' i) (dT' i) (idx i)).2 := by
    intro dS' dT' idx i
    simp [kronRightIndex, kronLegEquiv]
  -- The entry-level identity.
  have hentry : ∀ (p : Fin _ × Fin _) (row : RowST),
      (fS p.1 (rowSplitS row) * fT p.2 (rowSplitT row) : F) =
      (flattenMatrix (S ⊠ T) {j}) row (colIdx p) := by
    intro p row
    -- Rewrite fS via flattenMatrix S.
    have hfS_eq : fS p.1 (rowSplitS row) =
        (flattenMatrix S {j}) (rowSplitS row) (jS p.1) := by
      have := congrArg (fun f : RowS → F => f (rowSplitS row)) (hjS p.1)
      simpa [Matrix.col_apply] using this.symm
    have hfT_eq : fT p.2 (rowSplitT row) =
        (flattenMatrix T {j}) (rowSplitT row) (jT p.2) := by
      have := congrArg (fun f : RowT → F => f (rowSplitT row)) (hjT p.2)
      simpa [Matrix.col_apply] using this.symm
    rw [hfS_eq, hfT_eq]
    -- Unfold flattenMatrix and kroneckerTensor.
    change S (fun i => if h : i ∈ ({j} : Finset (Fin k))
            then (rowSplitS row) ⟨i, h⟩ else jS p.1 ⟨i, h⟩) *
         T (fun i => if h : i ∈ ({j} : Finset (Fin k))
            then (rowSplitT row) ⟨i, h⟩ else jT p.2 ⟨i, h⟩) =
         (S ⊠ T) (fun i => if h : i ∈ ({j} : Finset (Fin k))
            then row ⟨i, h⟩ else colIdx p ⟨i, h⟩)
    -- (S ⊠ T) idx = S (kronLeftIndex idx) * T (kronRightIndex idx).
    change _ = S (kronLeftIndex (dS := dS) (dT := dT)
        (fun i => if h : i ∈ ({j} : Finset (Fin k))
          then row ⟨i, h⟩ else colIdx p ⟨i, h⟩)) *
      T (kronRightIndex (dS := dS) (dT := dT)
        (fun i => if h : i ∈ ({j} : Finset (Fin k))
          then row ⟨i, h⟩ else colIdx p ⟨i, h⟩))
    congr 1
    · -- S-factor.
      apply congrArg
      funext i
      rw [hkronL]
      by_cases hi : i ∈ ({j} : Finset (Fin k))
      · -- row position.
        simp only [dif_pos hi]
        rfl
      · -- col position.
        simp only [dif_neg hi]
        -- Goal: jS p.1 ⟨i, hi⟩ = (kronLegEquiv (dS i) (dT i) (colIdx p ⟨i, hi⟩)).1.
        -- colIdx p ⟨i, hi⟩ = (kronLegEquiv ...).symm (jS p.1 ⟨i, hi⟩, jT p.2 ⟨i, hi⟩).
        rw [show colIdx p ⟨i, hi⟩
              = (kronLegEquiv (dS i) (dT i)).symm
                  (jS p.1 ⟨i, hi⟩, jT p.2 ⟨i, hi⟩) from rfl]
        rw [Equiv.apply_symm_apply]
    · -- T-factor.
      apply congrArg
      funext i
      rw [hkronR]
      by_cases hi : i ∈ ({j} : Finset (Fin k))
      · simp only [dif_pos hi]
        rfl
      · simp only [dif_neg hi]
        rw [show colIdx p ⟨i, hi⟩
              = (kronLegEquiv (dS i) (dT i)).symm
                  (jS p.1 ⟨i, hi⟩, jT p.2 ⟨i, hi⟩) from rfl]
        rw [Equiv.apply_symm_apply]
  -- Step 4: define gCol from the pair family, then transfer LI via rowCombine.
  -- gCol p row := fS p.1 (rowSplitS row) * fT p.2 (rowSplitT row).
  set gCol : Fin (Module.finrank F (Submodule.span F (Set.range (flattenMatrix S {j}).col))) ×
        Fin (Module.finrank F (Submodule.span F (Set.range (flattenMatrix T {j}).col))) →
        (RowST → F) :=
      fun p row => fS p.1 (rowSplitS row) * fT p.2 (rowSplitT row) with hgCol_def
  -- LI of gCol: build rowCombine to invert the rowSplit; then use LI of gPair.
  let rowCombine : RowS → RowT → RowST :=
    fun rS rT i => (kronLegEquiv (dS i.val) (dT i.val)).symm (rS i, rT i)
  have rowSplit_combine_S : ∀ rS rT, rowSplitS (rowCombine rS rT) = rS := by
    intro rS rT
    funext i
    change (kronLegEquiv (dS i.val) (dT i.val)
      ((kronLegEquiv (dS i.val) (dT i.val)).symm (rS i, rT i))).1 = rS i
    rw [Equiv.apply_symm_apply]
  have rowSplit_combine_T : ∀ rS rT, rowSplitT (rowCombine rS rT) = rT := by
    intro rS rT
    funext i
    change (kronLegEquiv (dS i.val) (dT i.val)
      ((kronLegEquiv (dS i.val) (dT i.val)).symm (rS i, rT i))).2 = rT i
    rw [Equiv.apply_symm_apply]
  have hgCol_li : LinearIndependent F gCol := by
    rw [linearIndependent_iff']
    intro s coef hsum p hp
    rw [linearIndependent_iff'] at hgPair_li
    refine hgPair_li s coef ?_ p hp
    ext rowPair
    obtain ⟨rowS, rowT⟩ := rowPair
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have := congrArg (fun f : RowST → F => f (rowCombine rowS rowT)) hsum
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    -- Both sides have form ∑ q ∈ s, coef q * (...); show pointwise equal at q.
    rw [show (∑ q ∈ s, coef q * (fS q.1 rowS * fT q.2 rowT)) =
          ∑ q ∈ s, coef q * gCol q (rowCombine rowS rowT) from ?_]
    · exact this
    · refine Finset.sum_congr rfl fun q _ => ?_
      congr 1
      show fS q.1 rowS * fT q.2 rowT = gCol q (rowCombine rowS rowT)
      simp only [gCol]
      rw [rowSplit_combine_S, rowSplit_combine_T]
  -- Step 5: gCol p is a column of (S ⊠ T)-flattening.
  have hgCol_is_col : ∀ p, gCol p = (flattenMatrix (S ⊠ T) {j}).col (colIdx p) := by
    intro p
    funext row
    change fS p.1 (rowSplitS row) * fT p.2 (rowSplitT row)
        = (flattenMatrix (S ⊠ T) {j}) row (colIdx p)
    exact hentry p row
  -- Step 6: conclude.
  have hspan_dim : Module.finrank F (Submodule.span F (Set.range gCol)) =
      Module.finrank F (Submodule.span F (Set.range (flattenMatrix S {j}).col)) *
      Module.finrank F (Submodule.span F (Set.range (flattenMatrix T {j}).col)) := by
    rw [finrank_span_eq_card hgCol_li, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
  have hcols_le : Module.finrank F (Submodule.span F (Set.range gCol)) ≤
      flatRank (S ⊠ T) {j} := by
    unfold flatRank
    rw [(flattenMatrix (S ⊠ T) {j}).rank_eq_finrank_span_cols]
    apply Submodule.finrank_mono
    rw [Submodule.span_le]
    rintro v ⟨p, rfl⟩
    rw [hgCol_is_col p]
    exact Submodule.subset_span ⟨colIdx p, rfl⟩
  unfold flatRank
  rw [hS, hT, ← hspan_dim]
  exact hcols_le

/-! ## flatRank Kronecker multiplicativity, the `≤`-direction (paper tex:393).

The `≥`-direction (`flatRank_kron_mul_le`) is above.  For the exact equality we
also need `flatRank (S ⊠ T) {j} ≤ flatRank S {j} * flatRank T {j}`.  The
`{j}`-flattening of `S ⊠ T` is the matrix Kronecker product of the
`{j}`-flattenings of `S` and `T` (reindexed by the per-leg index splits), and
matrix rank is submultiplicative under Kronecker product
(`Matrix.rank` of a Kronecker product `≤` product of ranks).  The latter is a
standard `TensorProduct.map` fact, replicated here as
`Semicontinuity.rank_kroneckerMap_mul_le` to avoid importing the ShannonCapacity
tree. -/

/-- **Submultiplicativity of `Matrix.rank` under Kronecker product** (replicated
    from `ShannonCapacity.Matrix.rank_kronecker_le` to avoid a cross-tree import).
    For matrices `A, B` over a field, `(kroneckerMap (·*·) A B).rank ≤ A.rank * B.rank`.

    Proof via `Matrix.toLin_kronecker` (the Kronecker matrix is `TensorProduct.map`
    of the two linear maps in tensor-product bases) and the finrank bound on the
    range of a `TensorProduct.map`. -/
private lemma finrank_range_tensorProduct_map_le
    {M N P Q : Type*} [AddCommGroup M] [Module F M] [AddCommGroup N]
    [Module F N] [AddCommGroup P] [Module F P] [AddCommGroup Q] [Module F Q]
    (f : M →ₗ[F] P) (g : N →ₗ[F] Q)
    [Module.Finite F (LinearMap.range f)] [Module.Finite F (LinearMap.range g)] :
    Module.finrank F (LinearMap.range (TensorProduct.map f g)) ≤
      Module.finrank F (LinearMap.range f) * Module.finrank F (LinearMap.range g) := by
  classical
  let rf : Submodule F P := LinearMap.range f
  let rg : Submodule F Q := LinearMap.range g
  let incl : rf ⊗[F] rg →ₗ[F] P ⊗[F] Q := TensorProduct.map rf.subtype rg.subtype
  have hrange : LinearMap.range (TensorProduct.map f g) ≤ LinearMap.range incl := by
    rw [TensorProduct.range_map_eq_span_tmul, TensorProduct.range_map_eq_span_tmul]
    apply Submodule.span_mono
    rintro z ⟨x, y, rfl⟩
    exact ⟨⟨f x, ⟨x, rfl⟩⟩, ⟨g y, ⟨y, rfl⟩⟩, by simp [rf, rg]⟩
  calc
    Module.finrank F (LinearMap.range (TensorProduct.map f g))
        ≤ Module.finrank F (LinearMap.range incl) := Submodule.finrank_mono hrange
    _ ≤ Module.finrank F (rf ⊗[F] rg) := LinearMap.finrank_range_le incl
    _ = Module.finrank F (LinearMap.range f) * Module.finrank F (LinearMap.range g) := by
        simp [rf, rg]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Submultiplicativity of `Matrix.rank` under Kronecker product** (replicated
    from `ShannonCapacity.Matrix.rank_kronecker_le` to avoid a cross-tree import).
    For matrices `A, B` over a field, `(kroneckerMap (·*·) A B).rank ≤ A.rank * B.rank`.
    The `Fintype`/`DecidableEq` instances on the row index types are load-bearing in
    the proof (bases, `toLin`) though the linter flags them as unused in the type. -/
private lemma rank_kroneckerMap_mul_le
    {ι κ ι' κ' : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq ι'] [DecidableEq κ']
    [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    (A : Matrix ι' ι F) (B : Matrix κ' κ F) :
    (Matrix.kroneckerMap (· * ·) A B).rank ≤ A.rank * B.rank := by
  classical
  let bι : Module.Basis ι F (ι → F) := Pi.basisFun F ι
  let bκ : Module.Basis κ F (κ → F) := Pi.basisFun F κ
  let bι' : Module.Basis ι' F (ι' → F) := Pi.basisFun F ι'
  let bκ' : Module.Basis κ' F (κ' → F) := Pi.basisFun F κ'
  calc
    (Matrix.kroneckerMap (· * ·) A B).rank =
        Module.finrank F
          (LinearMap.range
            (Matrix.toLin (bι.tensorProduct bκ) (bι'.tensorProduct bκ')
              (Matrix.kroneckerMap (· * ·) A B))) :=
      Matrix.rank_eq_finrank_range_toLin (Matrix.kroneckerMap (· * ·) A B)
        (bι'.tensorProduct bκ') (bι.tensorProduct bκ)
    _ ≤ Module.finrank F (LinearMap.range (Matrix.toLin bι bι' A)) *
          Module.finrank F (LinearMap.range (Matrix.toLin bκ bκ' B)) := by
        rw [Matrix.toLin_kronecker bι bκ bι' bκ']
        exact finrank_range_tensorProduct_map_le (Matrix.toLin bι bι' A) (Matrix.toLin bκ bκ' B)
    _ = A.rank * B.rank := by
        rw [← Matrix.rank_eq_finrank_range_toLin A bι' bι,
          ← Matrix.rank_eq_finrank_range_toLin B bκ' bκ]

/-- **Row/column index-split equiv for the `I`-flattening of a Kronecker product**
    (paper tex:393 engineering).  For any predicate `P` selecting legs, the
    indices of the `P`-block of the `S ⊠ T` flattening (per-leg
    `Fin (dS i * dT i)`) split into the `S`- and `T`-flattening indices
    (per-leg `Fin (dS i)` and `Fin (dT i)`), leg-by-leg via `kronLegEquiv`. -/
private def flattenSplitEquiv {k : ℕ} (dS dT : Fin k → ℕ+)
    (P : Fin k → Prop) [DecidablePred P] :
    (∀ i : {i : Fin k // P i}, Fin (((dS i.val * dT i.val : ℕ+) : ℕ))) ≃
      (∀ i : {i : Fin k // P i}, Fin ((dS i.val : ℕ+) : ℕ)) ×
        (∀ i : {i : Fin k // P i}, Fin ((dT i.val : ℕ+) : ℕ)) :=
  (Equiv.piCongrRight (fun i : {i : Fin k // P i} => kronLegEquiv (dS i.val) (dT i.val))).trans
    (Equiv.arrowProdEquivProdArrow _ _ _)

/-- **Kronecker multiplicativity of flatRank, `≤`-direction** (paper tex:393).

    `flatRank (S ⊠ T) {j} ≤ flatRank S {j} * flatRank T {j}`.

    The `{j}`-flattening of `S ⊠ T` is, after reindexing the row and column
    multi-indices by the per-leg `kronLegEquiv` splits (`flattenSplitEquiv`),
    the matrix Kronecker product of the `{j}`-flattenings of `S` and `T`; matrix
    rank is submultiplicative under Kronecker product (`rank_kroneckerMap_mul_le`)
    and invariant under reindexing (`Matrix.rank_submatrix`). -/
lemma flatRank_kron_mul_ge {k : ℕ} {dS dT : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT) (I : Finset (Fin k)) :
    flatRank (S ⊠ T) I ≤ flatRank S I * flatRank T I := by
  classical
  set MS := flattenMatrix S I with hMS
  set MT := flattenMatrix T I with hMT
  set eRow := flattenSplitEquiv (k := k) dS dT (· ∈ I)
  set eCol := flattenSplitEquiv (k := k) dS dT (· ∉ I)
  -- The flattening of `S ⊠ T` is the kronecker product reindexed by the splits.
  have heq : flattenMatrix (S ⊠ T) I
      = (Matrix.kroneckerMap (· * ·) MS MT).submatrix eRow eCol := by
    ext row col
    change (S ⊠ T) (fun i => if h : i ∈ I
            then row ⟨i, h⟩ else col ⟨i, h⟩) = _
    -- RHS unfolds to `MS (eRow row).1 (eCol col).1 * MT (eRow row).2 (eCol col).2`.
    rw [Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
    change S (kronLeftIndex (dS := dS) (dT := dT)
        (fun i => if h : i ∈ I then row ⟨i, h⟩ else col ⟨i, h⟩)) *
      T (kronRightIndex (dS := dS) (dT := dT)
        (fun i => if h : i ∈ I then row ⟨i, h⟩ else col ⟨i, h⟩))
      = MS ((eRow row).1) ((eCol col).1) * MT ((eRow row).2) ((eCol col).2)
    -- `MS u v = S (combine u v)`, `MT = ...`; reduce both factors leg-wise.
    change _ = S (fun i => if h : i ∈ I
            then (eRow row).1 ⟨i, h⟩ else (eCol col).1 ⟨i, h⟩) *
        T (fun i => if h : i ∈ I
            then (eRow row).2 ⟨i, h⟩ else (eCol col).2 ⟨i, h⟩)
    -- `kronLeftIndex idx i = (kronLegEquiv (dS i) (dT i) (idx i)).1`, similarly right.
    have hkronL : ∀ (idx : ∀ i, Fin (dS i * dT i)) (i : Fin k),
        kronLeftIndex (dS := dS) (dT := dT) idx i =
        (kronLegEquiv (dS i) (dT i) (idx i)).1 := by
      intro idx i; simp [kronLeftIndex, kronLegEquiv]
    have hkronR : ∀ (idx : ∀ i, Fin (dS i * dT i)) (i : Fin k),
        kronRightIndex (dS := dS) (dT := dT) idx i =
        (kronLegEquiv (dS i) (dT i) (idx i)).2 := by
      intro idx i; simp [kronRightIndex, kronLegEquiv]
    congr 1
    · -- S-factor: `kronLeftIndex (combine row col) i = combine (eRow row).1 (eCol col).1 i`.
      apply congrArg
      funext i
      rw [hkronL]
      by_cases hi : i ∈ I
      · simp only [dif_pos hi]
        show (kronLegEquiv (dS i) (dT i) (row ⟨i, hi⟩)).1 = (eRow row).1 ⟨i, hi⟩
        rfl
      · simp only [dif_neg hi]
        show (kronLegEquiv (dS i) (dT i) (col ⟨i, hi⟩)).1 = (eCol col).1 ⟨i, hi⟩
        rfl
    · -- T-factor.
      apply congrArg
      funext i
      rw [hkronR]
      by_cases hi : i ∈ I
      · simp only [dif_pos hi]
        show (kronLegEquiv (dS i) (dT i) (row ⟨i, hi⟩)).2 = (eRow row).2 ⟨i, hi⟩
        rfl
      · simp only [dif_neg hi]
        show (kronLegEquiv (dS i) (dT i) (col ⟨i, hi⟩)).2 = (eCol col).2 ⟨i, hi⟩
        rfl
  unfold flatRank
  rw [heq, Matrix.rank_submatrix]
  exact rank_kroneckerMap_mul_le MS MT

/-- **Exact Kronecker multiplicativity of flatRank, general cut** (paper tex:393).

    `flatRank (S ⊠ T) I = flatRank S I * flatRank T I` for any leg set `I`.

    Combines the `≥`-direction (`flatRank_kron_mul_le`, singleton — generalized to
    `I` here via `Finset.sum`/submatrix the same way) and the `≤`-direction
    (`flatRank_kron_mul_ge`, now general `I`).  The `≥`-direction we only have at
    singletons; for the `≤`-bound consumed by Cor 3.5 we expose the general-`I`
    `flatRank_kron_mul_ge` directly. -/
lemma flatRank_kron {k : ℕ} {dS dT : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT) (j : Fin k) :
    flatRank (S ⊠ T) {j} = flatRank S {j} * flatRank T {j} :=
  le_antisymm (flatRank_kron_mul_ge S T {j}) (flatRank_kron_mul_le S T j)

/-! ## Lemma 3.4 (tex:858-866): the flush lemma.

Field-cardinality condition `|F| > rank` (tex:862) is encoded as
`(rank : Cardinal) < Cardinal.mk F`, which is automatic when `F` is infinite. -/

/-- The set of column vectors of `M : Matrix (Fin a) (Fin b) F`, as `Fin a → F`. -/
def columnSet {a b : ℕ} (M : Matrix (Fin a) (Fin b) F) : Set (Fin a → F) :=
  Set.range fun j : Fin b => fun i => M i j

/-- The first `min r b` columns of `M : Matrix (Fin a) (Fin b) F`.

For `r ≤ b` this is the first `r` columns, matching the paper's `M|_{[r]}`
(tex:864); for `r > b` it is all columns. The `Nat.min` ensures the cast is
total and avoids dragging a `r ≤ b` hypothesis through the theorem. -/
def firstColumns {a b : ℕ} (M : Matrix (Fin a) (Fin b) F) (r : ℕ) :
    Set (Fin a → F) :=
  Set.range fun j : Fin (Nat.min r b) =>
    fun i => M i ⟨j.val, lt_of_lt_of_le j.isLt (Nat.min_le_right _ _)⟩

/-- Horizontal concatenation of `c` matrices in `Matrix (Fin a) (Fin b) F`, as a
    `Matrix (Fin a) (Fin c × Fin b) F`. -/
noncomputable def concatBlocks {a b c : ℕ} (M : Fin c → Matrix (Fin a) (Fin b) F) :
    Matrix (Fin a) (Fin c × Fin b) F :=
  fun row p => M p.1 row p.2

/-- The rank-increment sequence `r_i = rank([M_1; ⋯; M_i]) - rank([M_1; ⋯; M_{i-1}])`
    used in `flush_lemma` (tex:859-861).

    At `i = 0` the right summand is the rank of an `a × 0` matrix (`= 0`), so
    `r_0 = rank(M_0)`. -/
noncomputable def rankIncrement {a b c : ℕ} (M : Fin c → Matrix (Fin a) (Fin b) F)
    (i : Fin c) : ℕ :=
  (concatBlocks (c := i.val + 1) (fun j : Fin (i.val + 1) =>
    M ⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩)).rank
  -
  (concatBlocks (c := i.val) (fun j : Fin i.val =>
    M ⟨j.val, lt_trans j.isLt i.isLt⟩)).rank

/-- Telescoping sum of forward differences of a monotone `ℕ`-valued function:
    `∑_{i<c} (f(i+1) - f(i)) = f c - f 0`. Pure `ℕ` arithmetic helper. -/
private lemma sum_forward_diff_eq {c : ℕ} (f : ℕ → ℕ) (hf : Monotone f) :
    (∑ i : Fin c, (f (i.val + 1) - f i.val)) = f c - f 0 := by
  induction c with
  | zero => simp
  | succ d ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    have h0d : f 0 ≤ f d := hf (Nat.zero_le d)
    have hdd1 : f d ≤ f (d + 1) := hf (Nat.le_succ d)
    omega

/-- The rank of the prefix concatenation `[M_0; ⋯; M_{n-1}]` of the first
    `min n c` blocks. Packages the telescoping identity
    `∑_i rankIncrement M i = rank([M_0; ⋯; M_{c-1}])` underlying the degree
    bound in `flush_lemma` (tex:859-861, 893). -/
noncomputable def prefixRank {a b c : ℕ} (M : Fin c → Matrix (Fin a) (Fin b) F)
    (n : ℕ) : ℕ :=
  (concatBlocks (c := Nat.min n c) (fun j : Fin (Nat.min n c) =>
    M ⟨j.val, lt_of_lt_of_le j.isLt (Nat.min_le_right _ _)⟩)).rank

/-- `prefixRank M 0 = 0`: the empty concatenation has rank `0`. -/
private lemma prefixRank_zero {a b c : ℕ} (M : Fin c → Matrix (Fin a) (Fin b) F) :
    prefixRank M 0 = 0 := by
  apply Nat.le_zero.mp
  refine le_trans (Matrix.rank_le_card_width _) ?_
  simp

set_option maxHeartbeats 800000 in
-- `prefixRank M c` unfolds through `Fin (min c c)`; the `Fintype`-instance
-- defeq for the reindexing submatrix needs a raised heartbeat budget.
/-- `prefixRank M c = rank([M_0; ⋯; M_{c-1}])`. The prefix over `Fin (min c c)`
    is a reindexing of the full concatenation over `Fin c`. -/
private lemma prefixRank_full {a b c : ℕ} (M : Fin c → Matrix (Fin a) (Fin b) F) :
    prefixRank M c = (concatBlocks M).rank := by
  have hsub :
      (concatBlocks (c := Nat.min c c) (fun j : Fin (Nat.min c c) =>
          M ⟨j.val, lt_of_lt_of_le j.isLt (Nat.min_le_right _ _)⟩))
        = (concatBlocks M).submatrix (⇑(Equiv.refl (Fin a)))
            (⇑((finCongr (Nat.min_self c)).prodCongr (Equiv.refl (Fin b)))) := by
    funext row p
    simp only [concatBlocks, Matrix.submatrix_apply, Equiv.prodCongr_apply,
      Equiv.coe_refl, Prod.map, id_eq, finCongr_apply]
    congr 2
  exact (congrArg Matrix.rank hsub).trans
    (Matrix.rank_submatrix (concatBlocks M) (Equiv.refl (Fin a))
      ((finCongr (Nat.min_self c)).prodCongr (Equiv.refl (Fin b))))

/-- `prefixRank` is monotone in `n`: the columns of a shorter prefix
    concatenation are a subset of those of a longer one, so its column-span
    rank is `≤`. -/
private lemma prefixRank_mono {a b c : ℕ} (M : Fin c → Matrix (Fin a) (Fin b) F)
    {m n : ℕ} (hmn : m ≤ n) : prefixRank M m ≤ prefixRank M n := by
  have hmn' : Nat.min m c ≤ Nat.min n c := min_le_min hmn le_rfl
  simp only [prefixRank]
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  apply Submodule.finrank_mono
  rw [Submodule.span_le]
  rintro _ ⟨col, rfl⟩
  refine Submodule.subset_span
    ⟨(⟨⟨col.1.val, lt_of_lt_of_le col.1.isLt hmn'⟩, col.2⟩ :
        Fin (Nat.min n c) × Fin b), ?_⟩
  rfl

set_option maxHeartbeats 800000 in
-- two `prefixRank` unfoldings through `Fin (min · c)`; the reindexing-submatrix
-- `Fintype`-instance defeq needs a raised heartbeat budget.
/-- `rankIncrement M i = prefixRank M (i+1) - prefixRank M i`: the `i`th greedy
    increment is the prefix-rank jump (tex:859-861). For `i : Fin c` both
    `i.val` and `i.val+1` are `≤ c`, so the `min`s in `prefixRank` collapse. -/
private lemma rankIncrement_eq_prefixRank_sub {a b c : ℕ}
    (M : Fin c → Matrix (Fin a) (Fin b) F) (i : Fin c) :
    rankIncrement M i = prefixRank M (i.val + 1) - prefixRank M i.val := by
  have hi1 : Nat.min (i.val + 1) c = i.val + 1 :=
    Nat.min_eq_left (Nat.succ_le_of_lt i.isLt)
  have hi0 : Nat.min i.val c = i.val :=
    Nat.min_eq_left (le_of_lt i.isLt)
  have hpr1 :
      prefixRank M (i.val + 1) =
        (concatBlocks (c := i.val + 1) (fun j : Fin (i.val + 1) =>
          M ⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩)).rank := by
    have hsub :
        (concatBlocks (c := Nat.min (i.val + 1) c) (fun j : Fin (Nat.min (i.val + 1) c) =>
            M ⟨j.val, lt_of_lt_of_le j.isLt (Nat.min_le_right _ _)⟩))
          = (concatBlocks (c := i.val + 1) (fun j : Fin (i.val + 1) =>
              M ⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩)).submatrix
              (⇑(Equiv.refl (Fin a)))
              (⇑((finCongr hi1).prodCongr (Equiv.refl (Fin b)))) := by
      funext row p
      simp only [concatBlocks, Matrix.submatrix_apply, Equiv.prodCongr_apply,
        Equiv.coe_refl, Prod.map, id_eq, finCongr_apply]
      congr 2
    exact (congrArg Matrix.rank hsub).trans
      (Matrix.rank_submatrix _ (Equiv.refl (Fin a))
        ((finCongr hi1).prodCongr (Equiv.refl (Fin b))))
  have hpr0 :
      prefixRank M i.val =
        (concatBlocks (c := i.val) (fun j : Fin i.val =>
          M ⟨j.val, lt_trans j.isLt i.isLt⟩)).rank := by
    have hsub :
        (concatBlocks (c := Nat.min i.val c) (fun j : Fin (Nat.min i.val c) =>
            M ⟨j.val, lt_of_lt_of_le j.isLt (Nat.min_le_right _ _)⟩))
          = (concatBlocks (c := i.val) (fun j : Fin i.val =>
              M ⟨j.val, lt_trans j.isLt i.isLt⟩)).submatrix
              (⇑(Equiv.refl (Fin a)))
              (⇑((finCongr hi0).prodCongr (Equiv.refl (Fin b)))) := by
      funext row p
      simp only [concatBlocks, Matrix.submatrix_apply, Equiv.prodCongr_apply,
        Equiv.coe_refl, Prod.map, id_eq, finCongr_apply]
      congr 2
    exact (congrArg Matrix.rank hsub).trans
      (Matrix.rank_submatrix _ (Equiv.refl (Fin a))
        ((finCongr hi0).prodCongr (Equiv.refl (Fin b))))
  rw [rankIncrement, hpr1, hpr0]

/-- **Telescoping** (tex:893): `∑_i rankIncrement M i = rank([M_0; ⋯; M_{c-1}])`.

    This is the degree-budget identity for the Schwartz–Zippel argument in
    `flush_lemma`: the flush minor selecting `r_i` columns from each block has
    total degree `∑_i r_i`, which this lemma equates with
    `(concatBlocks M).rank`, matching the cardinality hypothesis `hF`. -/
theorem sum_rankIncrement_eq_rank {a b c : ℕ}
    (M : Fin c → Matrix (Fin a) (Fin b) F) :
    (∑ i : Fin c, rankIncrement M i) = (concatBlocks M).rank := by
  -- Rewrite each increment as a prefix-rank jump, then telescope over `ℕ`.
  have hstep : ∀ i : Fin c,
      rankIncrement M i = prefixRank M (i.val + 1) - prefixRank M i.val :=
    rankIncrement_eq_prefixRank_sub M
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  -- Telescoping for the monotone `ℕ`-valued `prefixRank M`.
  have hmono : Monotone (prefixRank M) := fun _ _ h => prefixRank_mono M h
  rw [sum_forward_diff_eq (prefixRank M) hmono, prefixRank_full M, prefixRank_zero M,
    Nat.sub_zero]

/-- **(B-arith)** Pure `ℕ` bound: a sum of nonnegative terms is bounded by the
    maximum term times the number of nonzero terms,
    `∑ i, f i ≤ (sup_i f i) · #{i : f i ≠ 0}`.

    This is the elementary arithmetic step from Briët et al. ITCS 2024,
    Thm. 3.2, tex:914-920:
      `∑_i r_i ≤ max_i r_i · |{i : r_i ≠ 0}|`. -/
private lemma sum_le_sup_mul_support_card {ι : Type*} [Fintype ι] (f : ι → ℕ) :
    (∑ i, f i) ≤
      (Finset.univ.sup f) * (Finset.univ.filter (fun i => f i ≠ 0)).card := by
  classical
  rw [← Finset.sum_filter_ne_zero]
  calc (∑ i ∈ Finset.univ.filter (fun i => f i ≠ 0), f i)
      ≤ ∑ _i ∈ Finset.univ.filter (fun i => f i ≠ 0), Finset.univ.sup f := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        exact Finset.le_sup (Finset.mem_univ i)
    _ = (Finset.univ.sup f) *
          (Finset.univ.filter (fun i => f i ≠ 0)).card := by
        rw [Finset.sum_const, smul_eq_mul]; ring

/-- **(B0)+(B-arith)** The block-decomposition rank bound from Briët et al.
    ITCS 2024, Thm. 3.2 (tex:893-920): the rank of a block concatenation is
    bounded by the maximum greedy rank increment times the number of nonzero
    increments,
      `rank([M_0; ⋯; M_{c-1}]) ≤ (max_i r_i) · |{i : r_i ≠ 0}|`
    where `r_i = rankIncrement M i`.

    Combines the telescoping identity `sum_rankIncrement_eq_rank` (B0,
    `∑_i r_i = rank`) with the elementary arithmetic bound
    `sum_le_sup_mul_support_card` (B-arith). This is fully proved; it is
    the load-bearing block-arithmetic core of the `k ≠ 2` induction step,
    independent of the slice/leg-permutation recursion. -/
theorem concatBlocks_rank_le_maxIncrement_mul_support {a b c : ℕ}
    (M : Fin c → Matrix (Fin a) (Fin b) F) :
    (concatBlocks M).rank ≤
      (Finset.univ.sup (rankIncrement M)) *
        (Finset.univ.filter (fun i => rankIncrement M i ≠ 0)).card := by
  rw [← sum_rankIncrement_eq_rank M]
  exact sum_le_sup_mul_support_card (rankIncrement M)

/-! ### Flush-lemma geometry: block columns, prefix span, and the
    rank-increment as a quotient finrank.

These mirror the analogous Schwartz–Zippel column-flush infrastructure in
`StabDim/FullyFlushedExistence_LIpoly.lean` (`detPoly`, `Δi`, `MMatrix`,
`combinedΔ_ne_zero`), adapted to the `concatBlocks`/`rankIncrement`
setup of `flush_lemma` (Briët et al. ITCS 2024, Lemma 3.4, tex:864-872). -/

/-- The `k`-th column of block `i`, as a vector in `Fin a → F`. -/
def blockCol {a b c : ℕ} (M : Fin c → Matrix (Fin a) (Fin b) F)
    (i : Fin c) (k : Fin b) : Fin a → F :=
  fun row => M i row k

/-- The span of all columns of the first `n` blocks `M_0, …, M_{n-1}`.
    `prevSpan M i.val` is the "previous-blocks" span against which the
    rank increment of block `i` is measured. -/
noncomputable def prevSpan {a b c : ℕ} (M : Fin c → Matrix (Fin a) (Fin b) F)
    (n : ℕ) : Submodule F (Fin a → F) :=
  Submodule.span F
    (⋃ (j : Fin c) (_ : j.val < n), Set.range (blockCol M j))

/-- The columns of the prefix concatenation `[M_0; ⋯; M_{n-1}]` span exactly
    `prevSpan M n`. -/
private lemma span_prefix_cols_eq_prevSpan
    {a b c : ℕ} (M : Fin c → Matrix (Fin a) (Fin b) F) (n : ℕ) :
    Submodule.span F (Set.range
      (concatBlocks (c := Nat.min n c) (fun j : Fin (Nat.min n c) =>
        M ⟨j.val, lt_of_lt_of_le j.isLt (Nat.min_le_right _ _)⟩)).col)
      = prevSpan M n := by
  unfold prevSpan
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    -- column `p : Fin (min n c) × Fin b` of the prefix block matrix is
    -- `blockCol M ⟨p.1.val, _⟩ p.2`, with `p.1.val < n`.
    have hjlt : p.1.val < n := lt_of_lt_of_le p.1.isLt (Nat.min_le_left _ _)
    have hjc : p.1.val < c := lt_of_lt_of_le p.1.isLt (Nat.min_le_right _ _)
    refine Submodule.subset_span ?_
    simp only [Set.mem_iUnion]
    refine ⟨⟨p.1.val, hjc⟩, hjlt, p.2, ?_⟩
    funext row
    simp only [blockCol, Matrix.col_apply, concatBlocks]
  · rw [Submodule.span_le]
    rintro _ hv
    simp only [Set.mem_iUnion, Set.mem_range] at hv
    obtain ⟨j, hjn, k, rfl⟩ := hv
    refine Submodule.subset_span ?_
    have hjmin : j.val < Nat.min n c :=
      Nat.lt_min.mpr ⟨hjn, j.isLt⟩
    refine ⟨(⟨⟨j.val, hjmin⟩, k⟩ : Fin (Nat.min n c) × Fin b), ?_⟩
    funext row
    simp only [blockCol, Matrix.col_apply, concatBlocks]

/-- `prefixRank M n = finrank (prevSpan M n)`: the prefix rank is the
    dimension of the span of the first `n` blocks' columns. -/
private lemma prefixRank_eq_finrank_prevSpan
    {a b c : ℕ} (M : Fin c → Matrix (Fin a) (Fin b) F) (n : ℕ) :
    prefixRank M n = Module.finrank F (prevSpan M n) := by
  unfold prefixRank
  rw [Matrix.rank_eq_finrank_span_cols, span_prefix_cols_eq_prevSpan]

/-- `prevSpan M (i+1) = prevSpan M i ⊔ span(columns of block i)`: adding the
    `(i)`-th block adjoins its columns to the previous-blocks span. -/
private lemma prevSpan_succ {a b c : ℕ} (M : Fin c → Matrix (Fin a) (Fin b) F)
    (i : Fin c) :
    prevSpan M (i.val + 1) =
      prevSpan M i.val ⊔ Submodule.span F (Set.range (blockCol M i)) := by
  unfold prevSpan
  rw [← Submodule.span_union]
  congr 1
  ext v
  constructor
  · intro hv
    simp only [Set.mem_iUnion] at hv
    obtain ⟨j, hjlt, hv⟩ := hv
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjlt with hlt | heq
    · left; simp only [Set.mem_iUnion]; exact ⟨j, hlt, hv⟩
    · right
      have : j = i := Fin.ext heq
      rw [this] at hv; exact hv
  · intro hv
    rcases hv with hL | hR
    · simp only [Set.mem_iUnion] at hL ⊢
      obtain ⟨j, hjlt, hv⟩ := hL
      exact ⟨j, Nat.lt_succ_of_lt hjlt, hv⟩
    · simp only [Set.mem_iUnion]
      exact ⟨i, Nat.lt_succ_self _, hR⟩

/-- `rankIncrement M i` equals the dimension of the image of block `i`'s column
    span in the quotient `(Fin a → F) ⧸ prevSpan M i.val`. Mirrors
    `cPart_eq_finrank_image` in the stabilizer column-flush. -/
private lemma rankIncrement_eq_finrank_image
    {a b c : ℕ} (M : Fin c → Matrix (Fin a) (Fin b) F) (i : Fin c) :
    rankIncrement M i = Module.finrank F
      ((Submodule.span F (Set.range (blockCol M i))).map
        (prevSpan M i.val).mkQ) := by
  classical
  set S : Submodule F (Fin a → F) := prevSpan M i.val with hS_def
  set A : Submodule F (Fin a → F) :=
    Submodule.span F (Set.range (blockCol M i)) with hA_def
  have h_sup : A ⊔ S = prevSpan M (i.val + 1) := by
    rw [prevSpan_succ M i, hS_def, hA_def, sup_comm]
  -- rank-nullity for `S.mkQ.domRestrict A`.
  have h_ker_dom : LinearMap.ker (S.mkQ.domRestrict A) =
      (A ⊓ S).comap A.subtype := by
    ext ⟨v, hv⟩
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.coe_subtype, Submodule.mem_inf]
    exact ⟨fun h => ⟨hv, h⟩, fun h => h.2⟩
  have h_range_dom : LinearMap.range (S.mkQ.domRestrict A) = A.map S.mkQ := by
    ext y
    simp only [LinearMap.mem_range, LinearMap.domRestrict_apply,
      Submodule.mem_map, Submodule.mkQ_apply]
    constructor
    · rintro ⟨⟨v, hv⟩, hy⟩; exact ⟨v, hv, hy⟩
    · rintro ⟨v, hv, hy⟩; exact ⟨⟨v, hv⟩, hy⟩
  have h_rk : Module.finrank F (LinearMap.range (S.mkQ.domRestrict A))
      + Module.finrank F (LinearMap.ker (S.mkQ.domRestrict A))
      = Module.finrank F A :=
    LinearMap.finrank_range_add_finrank_ker (S.mkQ.domRestrict A)
  rw [h_ker_dom, h_range_dom] at h_rk
  have h_finrank_ker :
      Module.finrank F ((A ⊓ S).comap A.subtype) =
        Module.finrank F ((A ⊓ S : Submodule F (Fin a → F))) := by
    apply LinearEquiv.finrank_eq
    exact Submodule.comapSubtypeEquivOfLe (inf_le_left : A ⊓ S ≤ A)
  rw [h_finrank_ker] at h_rk
  have h_sup_inf : Module.finrank F ↑(A ⊔ S) + Module.finrank F ↑(A ⊓ S)
      = Module.finrank F A + Module.finrank F S :=
    Submodule.finrank_sup_add_finrank_inf_eq A S
  rw [h_sup] at h_sup_inf
  -- rankIncrement M i = prefixRank M (i+1) - prefixRank M i = finrank S_{i+1} - finrank S.
  rw [rankIncrement_eq_prefixRank_sub M i,
    prefixRank_eq_finrank_prevSpan M (i.val + 1),
    prefixRank_eq_finrank_prevSpan M i.val]
  have h_le : Module.finrank F S
      ≤ Module.finrank F ↑(prevSpan M (i.val + 1)) := by
    apply Submodule.finrank_mono
    rw [← h_sup]; exact le_sup_right
  change Module.finrank F ↑(prevSpan M (i.val + 1))
      - Module.finrank F ↑S = Module.finrank F (Submodule.map S.mkQ A)
  omega

/-- `rankIncrement M i ≤ b`: the increment is the dimension of the image of
    the `b` block-columns in a quotient, so it is at most `b`. This is the
    width bound needed for the `firstColumns` truncation to be exact. -/
private lemma rankIncrement_le_width
    {a b c : ℕ} (M : Fin c → Matrix (Fin a) (Fin b) F) (i : Fin c) :
    rankIncrement M i ≤ b := by
  classical
  rw [rankIncrement_eq_finrank_image M i]
  refine le_trans (Submodule.finrank_map_le (prevSpan M i.val).mkQ _) ?_
  refine le_trans (finrank_span_le_card (R := F) (Set.range (blockCol M i))) ?_
  rw [Set.toFinset_range]
  exact le_trans Finset.card_image_le (by simp)

/-- **`rankIncrement M i ≤ (M i).rank`** (Briët et al. ITCS 2024, Thm. 3.2,
    tex:943 `\label{eq:11b}`): the `i`th greedy rank increment — the dimension of
    block `i`'s column span modulo the previous blocks' span — is at most the full
    rank of the block `M i`, since the quotient map can only decrease dimension and
    `(M i).rank = finrank (span (range (blockCol M i)))`. -/
private lemma rankIncrement_le_block_rank
    {a b c : ℕ} (M : Fin c → Matrix (Fin a) (Fin b) F) (i : Fin c) :
    rankIncrement M i ≤ (M i).rank := by
  classical
  rw [rankIncrement_eq_finrank_image M i, Matrix.rank_eq_finrank_span_cols]
  refine le_trans (Submodule.finrank_map_le (prevSpan M i.val).mkQ _) ?_
  apply le_of_eq
  have hcol : (M i).col = blockCol M i := by
    funext k row; simp [blockCol, Matrix.col_apply]
  rw [hcol]

/-- For each block `i`, there is an embedding `A : Fin (rankIncrement M i) ↪ Fin b`
    selecting columns whose quotient classes (modulo `prevSpan M i.val`) are
    linearly independent. Mirrors `exists_transversal_columns`. -/
private lemma exists_flush_transversal
    {a b c : ℕ} (M : Fin c → Matrix (Fin a) (Fin b) F) (i : Fin c) :
    ∃ A : Fin (rankIncrement M i) ↪ Fin b,
      LinearIndependent F
        (fun t : Fin (rankIncrement M i) =>
          Submodule.Quotient.mk (p := prevSpan M i.val) (blockCol M i (A t))) := by
  classical
  set S : Submodule F (Fin a → F) := prevSpan M i.val with hS_def
  set g : Fin b → ((Fin a → F) ⧸ S) :=
    fun k => Submodule.Quotient.mk (blockCol M i k) with hg_def
  have h_span :
      (Submodule.span F (Set.range g) : Submodule F ((Fin a → F) ⧸ S)) =
        (Submodule.span F (Set.range (blockCol M i))).map S.mkQ := by
    rw [Submodule.map_span]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range, hg_def]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨blockCol M i k, ⟨k, rfl⟩, by rw [← hk]; rfl⟩
    · rintro ⟨v, ⟨k, hk⟩, hv⟩; exact ⟨k, by rw [← hk] at hv; rw [← hv]; rfl⟩
  have h_finrank :
      Module.finrank F (Submodule.span F (Set.range g)) = rankIncrement M i := by
    rw [h_span]; exact (rankIncrement_eq_finrank_image M i).symm
  obtain ⟨f, hf_mem, _hf_span, hf_LI⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq (K := F) (Set.range g)
  have h_choose : ∀ t : Fin (Module.finrank F (Submodule.span F (Set.range g))),
      ∃ k : Fin b, g k = f t := by
    intro t; have := hf_mem t; simpa [Set.mem_range] using this
  let kf : Fin (Module.finrank F (Submodule.span F (Set.range g))) → Fin b :=
    fun t => (h_choose t).choose
  have hkf : ∀ t, g (kf t) = f t := fun t => (h_choose t).choose_spec
  have hf_inj : Function.Injective f := hf_LI.injective
  have hkf_inj : Function.Injective kf := by
    intro t1 t2 ht; apply hf_inj; rw [← hkf t1, ← hkf t2, ht]
  let eFin : Fin (rankIncrement M i) ≃
      Fin (Module.finrank F (Submodule.span F (Set.range g))) :=
    Fin.castOrderIso h_finrank.symm |>.toEquiv
  refine ⟨⟨fun t => kf (eFin t), hkf_inj.comp eFin.injective⟩, ?_⟩
  have hLI_comp : LinearIndependent F (fun t => f (eFin t)) :=
    hf_LI.comp _ eFin.injective
  have h_eq : (fun t : Fin (rankIncrement M i) =>
      Submodule.Quotient.mk (p := S) (blockCol M i (kf (eFin t)))) =
      (fun t : Fin (rankIncrement M i) => f (eFin t)) := by
    funext t; exact hkf (eFin t)
  change LinearIndependent F (fun t : Fin (rankIncrement M i) =>
    Submodule.Quotient.mk (p := S) (blockCol M i (kf (eFin t))))
  rw [h_eq]; exact hLI_comp

/-- For each block `i` with a transversal `A`, there exist linear functionals
    `lam` annihilating `prevSpan M i.val` whose Gram matrix against the
    selected columns is the identity (hence has nonzero determinant).
    Mirrors `exists_separating_dual`. -/
private lemma exists_flush_dual
    {a b c : ℕ} (M : Fin c → Matrix (Fin a) (Fin b) F) (i : Fin c)
    (A : Fin (rankIncrement M i) ↪ Fin b)
    (hA : LinearIndependent F
            (fun t : Fin (rankIncrement M i) =>
              Submodule.Quotient.mk (p := prevSpan M i.val) (blockCol M i (A t)))) :
    ∃ lam : Fin (rankIncrement M i) → ((Fin a → F) →ₗ[F] F),
      (∀ t, ∀ v ∈ prevSpan M i.val, lam t v = 0) ∧
      ((Matrix.of (fun t m =>
          lam t (blockCol M i (A m)))).det ≠ 0) := by
  classical
  set S : Submodule F (Fin a → F) := prevSpan M i.val with hS_def
  set bb : Fin (rankIncrement M i) → ((Fin a → F) ⧸ S) :=
    fun t => Submodule.Quotient.mk (p := S) (blockCol M i (A t)) with hbb_def
  have hbb_LI : LinearIndependent F bb := hA
  let V : Submodule F ((Fin a → F) ⧸ S) := Submodule.span F (Set.range bb)
  let bV : Module.Basis (Fin (rankIncrement M i)) F V := Module.Basis.span hbb_LI
  let bVd : Module.Basis (Fin (rankIncrement M i)) F (Module.Dual F V) := bV.dualBasis
  let μ' : Fin (rankIncrement M i) → (V →ₗ[F] F) := fun t => bVd t
  let ν : Fin (rankIncrement M i) → ((Fin a → F) ⧸ S →ₗ[F] F) :=
    fun t => (μ' t).exists_extend.choose
  have hν_extend : ∀ t, (ν t).comp V.subtype = μ' t :=
    fun t => (μ' t).exists_extend.choose_spec
  refine ⟨fun t => (ν t).comp S.mkQ, ?_, ?_⟩
  · intro t v hv
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero S).mpr hv, map_zero]
  · have h_bm_mem : ∀ m, bb m ∈ V := fun m => Submodule.subset_span ⟨m, rfl⟩
    have hbV_eq : ∀ m, (bV m : ((Fin a → F) ⧸ S)) = bb m := by
      intro m; exact Module.Basis.span_apply hbb_LI m
    have h_dual_self : ∀ t m, (μ' t) (bV m) = (if m = t then (1 : F) else 0) := by
      intros t m; change (bVd t) (bV m) = _; rw [bV.dualBasis_apply_self]
    have h_dual : ∀ t m, (ν t) (bb m) = (if m = t then (1 : F) else 0) := by
      intros t m
      rw [← hbV_eq m]
      change (ν t) (V.subtype (bV m)) = _
      rw [show (ν t) (V.subtype (bV m)) = ((ν t).comp V.subtype) (bV m) from rfl,
        hν_extend t]
      exact h_dual_self t m
    have h_mat :
        (Matrix.of (fun (t m : Fin (rankIncrement M i)) =>
          ((ν t).comp S.mkQ) (blockCol M i (A m)))) =
          (1 : Matrix (Fin (rankIncrement M i)) (Fin (rankIncrement M i)) F) := by
      ext t m
      simp only [Matrix.of_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
        Matrix.one_apply]
      have heq : ((ν t) (Submodule.Quotient.mk (p := S) (blockCol M i (A m)))) =
          (if m = t then (1 : F) else 0) := h_dual t m
      rw [show (Submodule.Quotient.mk (blockCol M i (A m)) : (Fin a → F) ⧸ S)
          = bb m from rfl] at heq
      rw [heq]
      by_cases h : t = m
      · simp [h]
      · simp [h, Ne.symm h]
    rw [h_mat, Matrix.det_one]; exact one_ne_zero

/-- The "generic determinant" polynomial of the `b × b` matrix of
    indeterminates `X (s, t)`. Used to force `det U ≠ 0` (invertibility)
    on the Schwartz–Zippel specialization. Mirrors `detPoly`. -/
noncomputable def flushDetPoly (b : ℕ) :
    MvPolynomial (Fin b × Fin b) F :=
  (Matrix.of (fun (s t : Fin b) =>
    (MvPolynomial.X (s, t) : MvPolynomial (Fin b × Fin b) F))).det

/-- `flushDetPoly ≠ 0`: evaluate at the identity matrix. Mirrors
    `detPoly_ne_zero`. -/
private lemma flushDetPoly_ne_zero {b : ℕ} :
    (flushDetPoly (F := F) b) ≠ 0 := by
  classical
  intro h
  let g : Fin b × Fin b → F := fun p => if p.1 = p.2 then 1 else 0
  have hev : MvPolynomial.eval g (flushDetPoly (F := F) b) = 1 := by
    have hmap :
        (MvPolynomial.eval g : MvPolynomial (Fin b × Fin b) F →+* F)
          (Matrix.of (fun (s t : Fin b) =>
            (MvPolynomial.X (s, t) : MvPolynomial (Fin b × Fin b) F))).det
        = (((Matrix.of (fun (s t : Fin b) =>
            (MvPolynomial.X (s, t) : MvPolynomial (Fin b × Fin b) F))).map
            (MvPolynomial.eval g))).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply]
    have hone :
        ((Matrix.of (fun (s t : Fin b) =>
            (MvPolynomial.X (s, t) : MvPolynomial (Fin b × Fin b) F))).map
            (MvPolynomial.eval g)) = (1 : Matrix (Fin b) (Fin b) F) := by
      ext s t; simp [g, Matrix.one_apply, Matrix.map, MvPolynomial.eval_X]
    unfold flushDetPoly
    rw [hmap, hone, Matrix.det_one]
  rw [h] at hev; simp only [map_zero] at hev; exact zero_ne_one hev

/-- The polynomial Gram matrix for block `i`: entry `(t, m)` pairs the
    functional `lam t` against the generic flushed column
    `m ↦ ∑_k X(k, ⟨m.val, _⟩) • blockCol M i k`. Mirrors `MMatrix'`. -/
noncomputable def flushGram
    {a b c : ℕ} (M : Fin c → Matrix (Fin a) (Fin b) F) (i : Fin c)
    (hr : rankIncrement M i ≤ b)
    (lam : Fin (rankIncrement M i) → ((Fin a → F) →ₗ[F] F)) :
    Matrix (Fin (rankIncrement M i)) (Fin (rankIncrement M i))
      (MvPolynomial (Fin b × Fin b) F) :=
  fun t m =>
    ∑ k : Fin b,
      (MvPolynomial.X (k, ⟨m.val, lt_of_lt_of_le m.isLt hr⟩) :
          MvPolynomial (Fin b × Fin b) F) *
        MvPolynomial.C (lam t (blockCol M i k))

/-- Per-block polynomial `Δᵢ := det (flushGram …)`. Degree `≤ rankIncrement M i`. -/
noncomputable def flushΔ
    {a b c : ℕ} (M : Fin c → Matrix (Fin a) (Fin b) F) (i : Fin c)
    (hr : rankIncrement M i ≤ b)
    (lam : Fin (rankIncrement M i) → ((Fin a → F) →ₗ[F] F)) :
    MvPolynomial (Fin b × Fin b) F :=
  (flushGram M i hr lam).det

/-- Evaluating `flushΔ` at a concrete matrix `U` gives the scalar determinant
    of the Gram matrix `(lam t (∑_k U k ⟨m.val,_⟩ • blockCol M i k))_{t,m}`.
    Mirrors `eval_Δi'`. -/
private lemma eval_flushΔ
    {a b c : ℕ} (M : Fin c → Matrix (Fin a) (Fin b) F) (i : Fin c)
    (hr : rankIncrement M i ≤ b)
    (lam : Fin (rankIncrement M i) → ((Fin a → F) →ₗ[F] F))
    (U : Matrix (Fin b) (Fin b) F) :
    MvPolynomial.eval (fun p : Fin b × Fin b => U p.1 p.2) (flushΔ M i hr lam) =
      (Matrix.of (fun (t m : Fin (rankIncrement M i)) =>
        lam t (fun row => ∑ k,
          U k ⟨m.val, lt_of_lt_of_le m.isLt hr⟩ * M i row k))).det := by
  classical
  set f : Fin b × Fin b → F := fun p => U p.1 p.2 with hf_def
  have h1 :
      MvPolynomial.eval f (flushΔ M i hr lam) =
        ((flushGram M i hr lam).map (MvPolynomial.eval f)).det := by
    unfold flushΔ
    rw [RingHom.map_det (MvPolynomial.eval f) (flushGram M i hr lam),
        RingHom.mapMatrix_apply]
  have hentry : ∀ t m,
      ((flushGram M i hr lam).map (MvPolynomial.eval f)) t m =
        lam t (fun row => ∑ k, U k ⟨m.val, lt_of_lt_of_le m.isLt hr⟩ * M i row k) := by
    intro t m
    change MvPolynomial.eval f (flushGram M i hr lam t m) =
        lam t (fun row => ∑ k, U k ⟨m.val, lt_of_lt_of_le m.isLt hr⟩ * M i row k)
    unfold flushGram
    rw [map_sum]
    have h_each : ∀ k : Fin b,
        MvPolynomial.eval f
            ((MvPolynomial.X (k, ⟨m.val, lt_of_lt_of_le m.isLt hr⟩) :
                MvPolynomial (Fin b × Fin b) F) *
              MvPolynomial.C (lam t (blockCol M i k)))
          = U k ⟨m.val, lt_of_lt_of_le m.isLt hr⟩ * lam t (blockCol M i k) := by
      intro k
      simp [MvPolynomial.eval_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, hf_def]
    simp_rw [h_each]
    rw [show
      (∑ k : Fin b, U k ⟨m.val, lt_of_lt_of_le m.isLt hr⟩ * lam t (blockCol M i k))
      = lam t (∑ k : Fin b,
          U k ⟨m.val, lt_of_lt_of_le m.isLt hr⟩ • blockCol M i k) from ?_]
    · congr 1
      funext row
      simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, blockCol]
    · rw [map_sum]
      congr 1
      funext k
      rw [LinearMap.map_smul, smul_eq_mul]
  rw [h1]; congr 1; ext t m; exact hentry t m

/-- `flushΔ ≠ 0` whenever the base-field Gram determinant
    `(lam t (blockCol M i (A m)))_{t,m}` is nonzero. Witness: the matrix
    `U₀` whose `m`-th column is `e_{A m}`, so the generic flushed column `m`
    specializes to `blockCol M i (A m)`. Mirrors `Δi'_ne_zero`. -/
private lemma flushΔ_ne_zero
    {a b c : ℕ} (M : Fin c → Matrix (Fin a) (Fin b) F) (i : Fin c)
    (hr : rankIncrement M i ≤ b)
    (A : Fin (rankIncrement M i) ↪ Fin b)
    (lam : Fin (rankIncrement M i) → ((Fin a → F) →ₗ[F] F))
    (h_gram : (Matrix.of (fun (t m : Fin (rankIncrement M i)) =>
        lam t (blockCol M i (A m)))).det ≠ 0) :
    flushΔ M i hr lam ≠ 0 := by
  classical
  intro hzero
  -- U₀ : column ⟨m.val,_⟩ is e_{A m}; entry (k, t) = [t < r] · [A t = k].
  let U₀ : Matrix (Fin b) (Fin b) F := Matrix.of fun k t =>
    if ht : t.val < rankIncrement M i then (if A ⟨t.val, ht⟩ = k then (1 : F) else 0)
    else 0
  have hev := eval_flushΔ M i hr lam U₀
  rw [hzero] at hev
  simp only [map_zero] at hev
  apply h_gram
  rw [show
      (Matrix.of (fun (t m : Fin (rankIncrement M i)) =>
        lam t (blockCol M i (A m))))
      = (Matrix.of (fun (t m : Fin (rankIncrement M i)) =>
        lam t (fun row => ∑ k : Fin b,
          U₀ k ⟨m.val, lt_of_lt_of_le m.isLt hr⟩ * M i row k))) from ?_]
  · exact hev.symm
  · ext t m
    simp only [Matrix.of_apply]
    apply congrArg
    funext row
    rw [Finset.sum_eq_single (A m)]
    · have h1 : U₀ (A m) ⟨m.val, lt_of_lt_of_le m.isLt hr⟩ = 1 := by
        change (if ht : (⟨m.val, lt_of_lt_of_le m.isLt hr⟩ : Fin b).val < rankIncrement M i
              then (if A ⟨(⟨m.val, lt_of_lt_of_le m.isLt hr⟩ : Fin b).val, ht⟩ = A m
                then (1 : F) else 0) else 0) = 1
        rw [dif_pos m.isLt, if_pos]; rfl
      rw [h1, one_mul]; rfl
    · intro k _ hk
      have h0 : U₀ k ⟨m.val, lt_of_lt_of_le m.isLt hr⟩ = 0 := by
        change (if ht : (⟨m.val, lt_of_lt_of_le m.isLt hr⟩ : Fin b).val < rankIncrement M i
              then (if A ⟨(⟨m.val, lt_of_lt_of_le m.isLt hr⟩ : Fin b).val, ht⟩ = k
                then (1 : F) else 0) else 0) = 0
        rw [dif_pos m.isLt, if_neg]
        intro heq; apply hk; rw [← heq]
      rw [h0, zero_mul]
    · intro hb; exact (hb (Finset.mem_univ _)).elim

/-- Each `flushGram` entry is a sum of `X · C` monomials, hence has
    total degree `≤ 1` (linear in the `U`-indeterminates). -/
private lemma flushGram_entry_totalDegree_le
    {a b c : ℕ} (M : Fin c → Matrix (Fin a) (Fin b) F) (i : Fin c)
    (hr : rankIncrement M i ≤ b)
    (lam : Fin (rankIncrement M i) → ((Fin a → F) →ₗ[F] F))
    (t m : Fin (rankIncrement M i)) :
    (flushGram M i hr lam t m).totalDegree ≤ 1 := by
  unfold flushGram
  refine le_trans (MvPolynomial.totalDegree_finset_sum _ _) ?_
  apply Finset.sup_le
  intro k _
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  have hX : (MvPolynomial.X (k, ⟨m.val, lt_of_lt_of_le m.isLt hr⟩) :
      MvPolynomial (Fin b × Fin b) F).totalDegree ≤ 1 := by
    rw [MvPolynomial.X]
    exact le_trans (MvPolynomial.totalDegree_monomial_le _ _) (by simp)
  refine le_trans (add_le_add hX
    (le_of_eq (MvPolynomial.totalDegree_C _))) ?_
  simp

/-- `flushΔ` has total degree `≤ rankIncrement M i`: the determinant of an
    `r × r` matrix with degree-`≤1` entries. This is the per-block degree
    contribution to the Schwartz–Zippel budget. -/
private lemma flushΔ_totalDegree_le
    {a b c : ℕ} (M : Fin c → Matrix (Fin a) (Fin b) F) (i : Fin c)
    (hr : rankIncrement M i ≤ b)
    (lam : Fin (rankIncrement M i) → ((Fin a → F) →ₗ[F] F)) :
    (flushΔ M i hr lam).totalDegree ≤ rankIncrement M i := by
  unfold flushΔ
  rw [Matrix.det_apply]
  refine le_trans (MvPolynomial.totalDegree_finset_sum _ _) ?_
  apply Finset.sup_le
  intro p _
  refine le_trans (MvPolynomial.totalDegree_smul_le _ _) ?_
  refine le_trans (MvPolynomial.totalDegree_finset_prod _ _) ?_
  calc (∑ x : Fin (rankIncrement M i), (flushGram M i hr lam (p x) x).totalDegree)
      ≤ ∑ _x : Fin (rankIncrement M i), 1 := by
        apply Finset.sum_le_sum
        intro x _; exact flushGram_entry_totalDegree_le M i hr lam (p x) x
    _ = rankIncrement M i := by simp

/-- The combined Schwartz–Zippel polynomial `p := ∏ᵢ flushΔᵢ`. Its total
    degree is `≤ ∑ᵢ rankIncrement M i = (concatBlocks M).rank` (by
    `sum_rankIncrement_eq_rank`), matching `hF`; and it is nonzero whenever
    each block has a transversal with nonzero base-field Gram determinant.
    Per the paper's degree budget (tex:858-866, 893) the determinant of `U`
    is *not* multiplied in (its degree `b` would break the budget when
    `R < b`); invertibility is recovered separately via basis completion. -/
private lemma flush_combined_poly_exists
    {a b c : ℕ} (M : Fin c → Matrix (Fin a) (Fin b) F)
    (hr : ∀ i : Fin c, rankIncrement M i ≤ b)
    (A : ∀ i : Fin c, Fin (rankIncrement M i) ↪ Fin b)
    (lam : ∀ i, Fin (rankIncrement M i) → ((Fin a → F) →ₗ[F] F))
    (h_gram : ∀ i, (Matrix.of (fun (t m : Fin (rankIncrement M i)) =>
        lam i t (blockCol M i (A i m)))).det ≠ 0) :
    ∃ p : MvPolynomial (Fin b × Fin b) F,
      p ≠ 0 ∧ p.totalDegree ≤ (concatBlocks M).rank ∧
      ∀ x : Fin b × Fin b → F, MvPolynomial.eval x p ≠ 0 →
        ∀ i : Fin c,
          (Matrix.of (fun (t m : Fin (rankIncrement M i)) =>
            lam i t (fun row => ∑ k,
              x (k, ⟨m.val, lt_of_lt_of_le m.isLt (hr i)⟩) * M i row k))).det ≠ 0 := by
  classical
  refine ⟨∏ i : Fin c, flushΔ M i (hr i) (lam i), ?_, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro i _
    exact flushΔ_ne_zero M i (hr i) (A i) (lam i) (h_gram i)
  · refine le_trans (MvPolynomial.totalDegree_finset_prod _ _) ?_
    rw [← sum_rankIncrement_eq_rank M]
    apply Finset.sum_le_sum
    intro i _
    exact flushΔ_totalDegree_le M i (hr i) (lam i)
  · intro x hx i
    by_contra hg
    apply hx
    rw [map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    set U : Matrix (Fin b) (Fin b) F := Matrix.of (fun k t => x (k, t)) with hU
    have hfeq :
        MvPolynomial.eval x (flushΔ M i (hr i) (lam i)) =
          MvPolynomial.eval (fun p : Fin b × Fin b => U p.1 p.2)
            (flushΔ M i (hr i) (lam i)) := by
      congr 1
    rw [hfeq, eval_flushΔ M i (hr i) (lam i) U]
    -- entries `U k ⟨m.val,_⟩ = x (k, ⟨m.val,_⟩)`, matching `hg`.
    convert hg using 3

/-- A linearly independent family `v : Fin n → V` in a finite-dimensional space
    extends to a linearly independent family `w : Fin m → V` for any `n ≤ m ≤
    finrank V`, with the prefix preserved: `w (castLE t) = v t`. Used to complete
    the flushed columns of `U` to an invertible matrix in `flush_lemma`. -/
private lemma exists_LI_extension {V : Type*} [AddCommGroup V] [Module F V]
    {n m : ℕ} (hnm : n ≤ m) (hm : m ≤ Module.finrank F V)
    (v : Fin n → V) (hv : LinearIndependent F v) :
    ∃ w : Fin m → V, LinearIndependent F w ∧ ∀ t : Fin n, w (Fin.castLE hnm t) = v t := by
  induction m with
  | zero =>
    have hn0 : n = 0 := Nat.le_zero.mp hnm
    subst hn0
    exact ⟨Fin.elim0, linearIndependent_empty_type, fun t => t.elim0⟩
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · have hnm' : n ≤ m := Nat.lt_succ_iff.mp hlt
      have hm' : m ≤ Module.finrank F V := le_trans (Nat.le_succ m) hm
      obtain ⟨w, hw, hwv⟩ := ih hnm' hm'
      have hmlt : m < Module.finrank F V := lt_of_lt_of_le (Nat.lt_succ_self m) hm
      obtain ⟨z, hz⟩ := exists_linearIndependent_snoc_of_lt_finrank hw hmlt
      refine ⟨Fin.snoc w z, hz, fun t => ?_⟩
      have hcast : (Fin.castLE hnm t : Fin (m + 1)) = (Fin.castLE hnm' t).castSucc :=
        Fin.ext rfl
      rw [hcast, Fin.snoc_castSucc, hwv t]
    · have hnm2 : n = m + 1 := le_antisymm hnm hge
      subst hnm2
      exact ⟨v, hv, fun t => by simp⟩

/-- A family `g` of vectors is linearly independent when there are functionals
    `φ` whose Gram matrix `(φ t (g m))_{t,m}` has nonzero determinant. -/
private lemma linearIndependent_of_gram_det_ne_zero {V : Type*} [AddCommGroup V]
    [Module F V] {r : ℕ} (g : Fin r → V) (φ : Fin r → (V →ₗ[F] F))
    (hdet : (Matrix.of (fun t m => φ t (g m))).det ≠ 0) :
    LinearIndependent F g := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro cc hsum m
  have hAcc : (Matrix.of (fun t m => φ t (g m))).mulVec cc = 0 := by
    funext t
    simp only [Matrix.mulVec, Matrix.of_apply, dotProduct, Pi.zero_apply]
    have hrw : ∑ m, φ t (g m) * cc m = φ t (∑ m, cc m • g m) := by
      rw [map_sum]; apply Finset.sum_congr rfl; intro m _
      rw [map_smul, smul_eq_mul, mul_comm]
    rw [hrw, hsum, map_zero]
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hAcc) m

/-- A linearly independent family `g : Fin r → V` landing inside a submodule `Im`
    of `finrank = r` spans `Im`. -/
private lemma submodule_le_span_of_LI_card_eq_finrank {V : Type*} [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] {r : ℕ} (g : Fin r → V)
    (Im : Submodule F V) (hmem : ∀ m, g m ∈ Im) (hLI : LinearIndependent F g)
    (hfr : Module.finrank F Im = r) :
    Im ≤ Submodule.span F (Set.range g) := by
  classical
  let g' : Fin r → Im := fun m => ⟨g m, hmem m⟩
  have hLI' : LinearIndependent F g' := by
    have h0 : LinearIndependent F (Im.subtype ∘ g') := by
      simpa [g', Function.comp] using hLI
    exact h0.of_comp Im.subtype
  have hcard : Fintype.card (Fin r) = Module.finrank F Im := by simp [hfr]
  have htop : Submodule.span F (Set.range g') = ⊤ :=
    hLI'.span_eq_top_of_card_eq_finrank' hcard
  intro v hv
  have hmem_top : (⟨v, hv⟩ : Im) ∈ (⊤ : Submodule F Im) := Submodule.mem_top
  rw [← htop] at hmem_top
  have himg : (Im.subtype) ⟨v, hv⟩ ∈
      Submodule.map Im.subtype (Submodule.span F (Set.range g')) :=
    Submodule.mem_map_of_mem hmem_top
  rw [Submodule.map_span] at himg
  refine Submodule.span_mono ?_ himg
  rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
  exact ⟨m, rfl⟩

/-- **Lemma 3.4** (tex:858-866, `\label{lem:flush}`).

For matrices `M_1, …, M_c ∈ F^{a × b}` and increments `r_i`,
if `|F| > rank([M_1; ⋯; M_c])` then there exists an invertible `U ∈ F^{b × b}` such that
the column span of the truncated concatenation `[(M_1 U)|_{[r_1]}; ⋯; (M_c U)|_{[r_c]}]`
equals the column span of `[M_1; ⋯; M_c]`. -/
theorem flush_lemma
    {a b c : ℕ} (M : Fin c → Matrix (Fin a) (Fin b) F)
    (hF : ((concatBlocks M).rank : Cardinal) < Cardinal.mk F) :
    ∃ U : Matrix (Fin b) (Fin b) F, IsUnit U.det ∧
      Submodule.span F (⋃ i : Fin c, firstColumns (M i * U) (rankIncrement M i))
        = Submodule.span F (⋃ i : Fin c, columnSet (M i)) := by
  classical
  /- **Briët et al. ITCS 2024, Lemma 3.4 (paper tex:864-872).**

     Genuine determinant-polynomial construction: for each block `i` choose
     a transversal `A i` of the rank-increment columns (`exists_flush_transversal`)
     and separating dual functionals `lam i` whose base-field Gram determinant
     is nonzero (`exists_flush_dual`). The combined polynomial
     `p = ∏ᵢ flushΔᵢ` is nonzero with `totalDegree ≤ (concatBlocks M).rank`
     (`flush_combined_poly_exists`, using the telescoping `sum_rankIncrement_eq_rank`
     for the degree budget — note `det U` is *not* multiplied in, per tex:893). -/
  have hr : ∀ i : Fin c, rankIncrement M i ≤ b := rankIncrement_le_width M
  choose A hA using (fun i : Fin c => exists_flush_transversal M i)
  choose lam h_lam_ann h_gram using
    (fun i : Fin c => exists_flush_dual M i (A i) (hA i))
  obtain ⟨p, hp_ne, hp_degree, hp_certifies⟩ :=
    flush_combined_poly_exists M hr A lam h_gram
  -- Schwartz–Zippel: the field-cardinality bound `hF` gives a specialization.
  have hp_degree_card : (p.totalDegree : Cardinal) < Cardinal.mk F := by
    have hp_degree_card_le :
        (p.totalDegree : Cardinal.{u}) ≤ ((concatBlocks M).rank : Cardinal.{u}) := by
      exact_mod_cast hp_degree
    exact lt_of_le_of_lt hp_degree_card_le hF
  obtain ⟨x, hx⟩ :=
    mvPolynomial_exists_eval_ne_zero_of_totalDegree_lt_card
      (F := F) (σ := Fin b × Fin b) hp_ne hp_degree_card
  -- The specialization certifies that every block's flushed Gram determinant
  -- is nonzero: the first `rankIncrement M i` columns of `Mᵢ·U` (with
  -- `U k t = x (k, t)`) are linearly independent modulo `prevSpan M i.val`.
  have h_flushed_gram :
      ∀ i : Fin c,
        (Matrix.of (fun (t m : Fin (rankIncrement M i)) =>
          lam i t (fun row => ∑ k,
            x (k, ⟨m.val, lt_of_lt_of_le m.isLt (hr i)⟩) * M i row k))).det ≠ 0 :=
    hp_certifies x hx
  /- **Remaining geometric bridge (Briët et al. ITCS 2024, Lemma 3.4,
     paper tex:864-872).** With `U k t := x (k, t)`:

     * `h_flushed_gram i` certifies the first `rankIncrement M i` columns of
       `Mᵢ·U` are linearly independent modulo `prevSpan M i.val` (the previous
       blocks' span), via `h_lam_ann i` (annihilation) + nonzero Gram det.
     * Since `rankIncrement M i = finrank` of block `i`'s image in that
       quotient (`rankIncrement_eq_finrank_image`), those flushed columns
       *span* the same image — so the flushed union spans each block's
       columns modulo the previous span, hence (by induction over blocks)
       the whole `columnSet`.
     * Invertibility of `U` is obtained by completing the first `R = max r_i`
       columns of `U₀ := Matrix.of x` — linearly independent in `Fᵇ`, witnessed
       by the maximal-increment block — to a basis of `Fᵇ` via
       `exists_LI_extension`, keeping the flushed columns fixed (NOT from the
       polynomial — its degree `b` would break the tex:893 budget when
       `rank < b`).

     This linear-algebra assembly is proved below proved using the
     proved helpers `linearIndependent_of_gram_det_ne_zero`,
     `submodule_le_span_of_LI_card_eq_finrank`, and `exists_LI_extension`. -/
  -- The flushed column `m` of block `i` under a matrix `U`.
  set flcol : (Matrix (Fin b) (Fin b) F) → (i : Fin c) → Fin (rankIncrement M i) →
      (Fin a → F) :=
    fun U i m row => ∑ k, U k ⟨m.val, lt_of_lt_of_le m.isLt (hr i)⟩ * M i row k with hflcol
  -- `firstColumns (M i * U) (rankIncrement M i)` is exactly the range of `flcol U i`.
  have hfirstCols : ∀ (U : Matrix (Fin b) (Fin b) F) (i : Fin c),
      firstColumns (M i * U) (rankIncrement M i) = Set.range (flcol U i) := by
    intro U i
    have hmin : Nat.min (rankIncrement M i) b = rankIncrement M i :=
      Nat.min_eq_left (hr i)
    ext v
    simp only [firstColumns, Set.mem_range]
    constructor
    · rintro ⟨j, rfl⟩
      have hjr : j.val < rankIncrement M i := lt_of_lt_of_le j.isLt (le_of_eq hmin)
      refine ⟨⟨j.val, hjr⟩, ?_⟩
      funext row
      simp only [hflcol, Matrix.mul_apply]
      exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
    · rintro ⟨m, rfl⟩
      have hmr : m.val < Nat.min (rankIncrement M i) b :=
        lt_of_lt_of_le m.isLt (le_of_eq hmin.symm)
      refine ⟨⟨m.val, hmr⟩, ?_⟩
      funext row
      simp only [hflcol, Matrix.mul_apply]
      exact (Finset.sum_congr rfl (fun k _ => mul_comm _ _))
  -- Each flushed column of block `i` lies in the span of block `i`'s columns.
  have hflcol_mem : ∀ (U : Matrix (Fin b) (Fin b) F) (i : Fin c)
      (m : Fin (rankIncrement M i)),
      flcol U i m ∈ Submodule.span F (Set.range (blockCol M i)) := by
    intro U i m
    have : flcol U i m =
        ∑ k : Fin b, U k ⟨m.val, lt_of_lt_of_le m.isLt (hr i)⟩ • blockCol M i k := by
      funext row
      simp only [hflcol, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, blockCol]
    rw [this]
    exact Submodule.sum_mem _ (fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  -- Block inclusion: if the flushed Gram det of `U` is nonzero for block `i`,
  -- then block `i`'s columns lie in `prevSpan ⊔ span(flushed columns of U)`.
  have block_incl : ∀ (U : Matrix (Fin b) (Fin b) F),
      (∀ i : Fin c, (Matrix.of (fun (t m : Fin (rankIncrement M i)) =>
          lam i t (flcol U i m))).det ≠ 0) →
      ∀ i : Fin c,
        Submodule.span F (Set.range (blockCol M i)) ≤
          prevSpan M i.val ⊔
            Submodule.span F (firstColumns (M i * U) (rankIncrement M i)) := by
    intro U hUgram i
    set S : Submodule F (Fin a → F) := prevSpan M i.val with hS_def
    -- functionals on the quotient lifting `lam i t`.
    set φ : Fin (rankIncrement M i) → (((Fin a → F) ⧸ S) →ₗ[F] F) :=
      fun t => Submodule.liftQ S (lam i t) (fun v hv => h_lam_ann i t v hv) with hφ
    set g : Fin (rankIncrement M i) → ((Fin a → F) ⧸ S) :=
      fun m => Submodule.Quotient.mk (flcol U i m) with hg
    have hφg : ∀ t m, φ t (g m) = lam i t (flcol U i m) := by
      intro t m; simp only [hφ, hg, Submodule.liftQ_apply]
    have hLI_g : LinearIndependent F g := by
      apply linearIndependent_of_gram_det_ne_zero g φ
      have : (Matrix.of (fun t m => φ t (g m))) =
          (Matrix.of (fun (t m : Fin (rankIncrement M i)) =>
            lam i t (flcol U i m))) := by
        ext t m; simp only [Matrix.of_apply]; exact hφg t m
      rw [this]; exact hUgram i
    -- the image of block `i`'s span in the quotient has finrank = rankIncrement.
    set Im : Submodule F ((Fin a → F) ⧸ S) :=
      (Submodule.span F (Set.range (blockCol M i))).map S.mkQ with hIm
    have hg_mem : ∀ m, g m ∈ Im := by
      intro m
      exact Submodule.mem_map_of_mem (hflcol_mem U i m)
    have hfr : Module.finrank F Im = rankIncrement M i :=
      (rankIncrement_eq_finrank_image M i).symm
    have hIm_le : Im ≤ Submodule.span F (Set.range g) :=
      submodule_le_span_of_LI_card_eq_finrank g Im hg_mem hLI_g hfr
    -- transfer to the ambient space.
    rw [hfirstCols U i]
    intro v hv
    have hmkv : S.mkQ v ∈ Im := Submodule.mem_map_of_mem hv
    have hmkv2 : S.mkQ v ∈ Submodule.span F (Set.range g) := hIm_le hmkv
    have hrange_eq : Set.range g = S.mkQ '' (Set.range (flcol U i)) := by
      ext z
      simp only [hg, Set.mem_range, Set.mem_image]
      constructor
      · rintro ⟨m, rfl⟩; exact ⟨flcol U i m, ⟨m, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨m, rfl⟩, rfl⟩; exact ⟨m, rfl⟩
    rw [hrange_eq, ← Submodule.map_span] at hmkv2
    obtain ⟨y, hy_mem, hy_eq⟩ := hmkv2
    have hsub : v - y ∈ S := by
      rw [← Submodule.Quotient.eq]; exact hy_eq.symm
    have : v = (v - y) + y := by ring
    rw [this]
    exact Submodule.add_mem_sup hsub (Submodule.span_mono (le_refl _) hy_mem)
  -- Build the invertible `U`. `U₀ := Matrix.of x` realizes `h_flushed_gram`.
  set U₀ : Matrix (Fin b) (Fin b) F := Matrix.of (fun k t => x (k, t)) with hU₀
  have hgram0 : ∀ i : Fin c,
      (Matrix.of (fun (t m : Fin (rankIncrement M i)) =>
          lam i t (flcol U₀ i m))).det ≠ 0 := by
    intro i
    have heq : (Matrix.of (fun (t m : Fin (rankIncrement M i)) =>
          lam i t (flcol U₀ i m))) =
        (Matrix.of (fun (t m : Fin (rankIncrement M i)) =>
          lam i t (fun row => ∑ k,
            x (k, ⟨m.val, lt_of_lt_of_le m.isLt (hr i)⟩) * M i row k))) := by
      ext t m; simp only [Matrix.of_apply, hflcol, hU₀, Matrix.of_apply]
    rw [heq]; exact h_flushed_gram i
  have schwartz_zippel_flush_witness :
      ∃ U : Matrix (Fin b) (Fin b) F, IsUnit U.det ∧
        Submodule.span F (⋃ i : Fin c, columnSet (M i)) ≤
          Submodule.span F
            (⋃ i : Fin c, firstColumns (M i * U) (rankIncrement M i)) := by
    rcases Nat.eq_zero_or_pos c with hc | hc
    · -- no blocks: both spans trivial.
      subst hc
      refine ⟨1, by simp, ?_⟩
      simp only [Set.iUnion_of_empty, Submodule.span_empty, le_refl]
    · -- choose the max-increment block to witness global linear independence.
      obtain ⟨istar, _, hmax⟩ :=
        Finset.exists_max_image (Finset.univ : Finset (Fin c))
          (fun i => rankIncrement M i) ⟨⟨0, hc⟩, Finset.mem_univ _⟩
      set R : ℕ := rankIncrement M istar with hR
      have hRb : R ≤ b := hr istar
      have hmax' : ∀ i : Fin c, rankIncrement M i ≤ R := fun i =>
        hmax i (Finset.mem_univ _)
      -- the first R columns of U₀ form an LI family in `Fᵇ`.
      set vR : Fin R → (Fin b → F) :=
        fun t k => U₀ k ⟨t.val, lt_of_lt_of_le t.isLt hRb⟩ with hvR
      have hLI_vR : LinearIndependent F vR := by
        -- LI of the flushed columns of block `istar` (in `Fᵃ`) factors through `vR`.
        set S0 : Submodule F (Fin a → F) := prevSpan M istar.val with hS0
        have hLI_g0 : LinearIndependent F
            (fun m : Fin R => Submodule.Quotient.mk (p := S0) (flcol U₀ istar m)) := by
          apply linearIndependent_of_gram_det_ne_zero
            (fun m : Fin R => Submodule.Quotient.mk (p := S0) (flcol U₀ istar m))
            (fun t => Submodule.liftQ S0 (lam istar t)
              (fun v hv => h_lam_ann istar t v hv))
          have : (Matrix.of (fun (t m : Fin R) =>
              (Submodule.liftQ S0 (lam istar t)
                (fun v hv => h_lam_ann istar t v hv))
                (Submodule.Quotient.mk (p := S0) (flcol U₀ istar m)))) =
              (Matrix.of (fun (t m : Fin (rankIncrement M istar)) =>
                lam istar t (flcol U₀ istar m))) := by
            ext t m; simp only [Matrix.of_apply, Submodule.liftQ_apply]
          rw [this]; exact hgram0 istar
        have hLI_flcol : LinearIndependent F (fun m : Fin R => flcol U₀ istar m) :=
          hLI_g0.of_comp S0.mkQ
        -- flcol U₀ istar m = (M istar).mulVecLin (vR m).
        have hfact : (fun m : Fin R => flcol U₀ istar m) =
            (Matrix.mulVecLin (M istar)) ∘ vR := by
          funext m row
          simp only [Function.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec,
            dotProduct, hvR, hflcol, hU₀, Matrix.of_apply]
          exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
        rw [hfact] at hLI_flcol
        exact hLI_flcol.of_comp _
      -- extend to a full LI family of `b` columns.
      have hfrb : Module.finrank F (Fin b → F) = b := by simp
      obtain ⟨w, hw_LI, hw_pref⟩ :=
        exists_LI_extension hRb (by rw [hfrb]) vR hLI_vR
      set U : Matrix (Fin b) (Fin b) F := Matrix.of (fun k t => w t k) with hUdef
      have hUcol : U.col = w := by funext t; rfl
      have hUunit : IsUnit U.det := by
        rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_cols_iff_isUnit,
          hUcol]
        exact hw_LI
      -- `U` agrees with `U₀` on the first `R` columns.
      have hUagree : ∀ (t : Fin b), t.val < R → ∀ k, U k t = U₀ k ⟨t.val, t.isLt⟩ := by
        intro t ht k
        have hcol : U.col t = vR ⟨t.val, ht⟩ := by
          rw [hUcol]
          have hc2 : w t = w (Fin.castLE hRb ⟨t.val, ht⟩) := by
            apply congrArg; exact Fin.ext rfl
          rw [hc2, hw_pref ⟨t.val, ht⟩]
        have hck : U k t = vR ⟨t.val, ht⟩ k := congrFun hcol k
        rw [hck, hvR]
      -- the flushed Gram det of `U` matches that of `U₀` for each block.
      have hUgram : ∀ i : Fin c,
          (Matrix.of (fun (t m : Fin (rankIncrement M i)) =>
              lam i t (flcol U i m))).det ≠ 0 := by
        intro i
        have hfleq : ∀ m : Fin (rankIncrement M i), flcol U i m = flcol U₀ i m := by
          intro m
          funext row
          simp only [hflcol]
          apply Finset.sum_congr rfl
          intro k _
          have hlt : (⟨m.val, lt_of_lt_of_le m.isLt (hr i)⟩ : Fin b).val < R :=
            lt_of_lt_of_le m.isLt (hmax' i)
          rw [hUagree _ hlt k]
        have : (Matrix.of (fun (t m : Fin (rankIncrement M i)) =>
              lam i t (flcol U i m))) =
            (Matrix.of (fun (t m : Fin (rankIncrement M i)) =>
              lam i t (flcol U₀ i m))) := by
          ext t m; simp only [Matrix.of_apply, hfleq m]
        rw [this]; exact hgram0 i
      refine ⟨U, hUunit, ?_⟩
      -- span inclusion via prevSpan induction.
      set T : Submodule F (Fin a → F) :=
        Submodule.span F (⋃ i : Fin c, firstColumns (M i * U) (rankIncrement M i))
        with hT
      have hfc_le : ∀ i : Fin c,
          Submodule.span F (firstColumns (M i * U) (rankIncrement M i)) ≤ T := by
        intro i
        apply Submodule.span_mono
        exact Set.subset_iUnion (fun i => firstColumns (M i * U) (rankIncrement M i)) i
      have haux : ∀ n, n ≤ c → prevSpan M n ≤ T := by
        intro n
        induction n with
        | zero =>
          intro _
          have : prevSpan M 0 = ⊥ := by
            unfold prevSpan
            simp only [Nat.not_lt_zero, Set.iUnion_of_empty, Set.iUnion_empty,
              Submodule.span_empty]
          rw [this]; exact bot_le
        | succ n ih =>
          intro hsucc
          have hnc : n < c := hsucc
          set i : Fin c := ⟨n, hnc⟩ with hi
          have hprev : prevSpan M n ≤ T := ih (le_of_lt hnc)
          have hprev' : prevSpan M i.val ≤ T := hprev
          rw [show n + 1 = i.val + 1 from rfl, prevSpan_succ M i]
          apply sup_le hprev'
          have hbi := block_incl U hUgram i
          exact le_trans hbi (sup_le hprev' (hfc_le i))
      have hfinal : prevSpan M c ≤ T := haux c le_rfl
      -- `prevSpan M c = span(⋃ columnSet)`.
      have hpc : prevSpan M c = Submodule.span F (⋃ i : Fin c, columnSet (M i)) := by
        unfold prevSpan
        congr 1
        ext v
        simp only [Set.mem_iUnion, columnSet]
        constructor
        · rintro ⟨j, _, hv⟩; exact ⟨j, hv⟩
        · rintro ⟨j, hv⟩; exact ⟨j, j.isLt, hv⟩
      rw [hpc] at hfinal
      exact hfinal
  obtain ⟨U, hUdet, hhard⟩ := schwartz_zippel_flush_witness
  refine ⟨U, hUdet, le_antisymm ?_ hhard⟩
  rw [Submodule.span_le]
  intro v hv
  rw [Set.mem_iUnion] at hv
  obtain ⟨i, hv⟩ := hv
  rw [firstColumns] at hv
  obtain ⟨j, rfl⟩ := hv
  have hlocal :
      (fun row =>
          (M i * U) row
            ⟨j.val, lt_of_lt_of_le j.isLt (Nat.min_le_right (rankIncrement M i) b)⟩) ∈
        Submodule.span F (columnSet (M i)) := by
    rw [show
        (fun row =>
            (M i * U) row
              ⟨j.val, lt_of_lt_of_le j.isLt (Nat.min_le_right (rankIncrement M i) b)⟩) =
          ∑ k : Fin b,
            U k ⟨j.val, lt_of_lt_of_le j.isLt
                (Nat.min_le_right (rankIncrement M i) b)⟩ •
              (fun row => M i row k) from by
      funext row
      rw [Matrix.mul_apply]
      simp only [Finset.sum_apply, Pi.smul_apply]
      exact Finset.sum_congr rfl (fun k _ =>
        mul_comm (M i row k)
          (U k ⟨j.val, lt_of_lt_of_le j.isLt
            (Nat.min_le_right (rankIncrement M i) b)⟩))]
    apply Submodule.sum_mem
    intro k _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨k, rfl⟩
  exact (Submodule.span_mono
    (Set.subset_iUnion (fun i : Fin c => columnSet (M i)) i)) hlocal

/-- **Flush-support bound** (Briët et al. ITCS 2024, Thm. 3.2, tex:951-969,
    `\label{eq:12b}`).  For blocks `M_i ∈ F^{a×b}` with
    `|F| > rank([M_1; ⋯; M_c])`, there is a *single* column vector `u : Fin b → F`
    (the first column of the flush matrix `U` of `flush_lemma`) such that the matrix
    `M'_u` whose `i`-th column is the `u`-contraction of block `i`
    (`M'_u row i = ∑ l, M i row l · u l`) has rank at least the number of blocks
    with nonzero rank-increment:
    `#{i : r_i ≠ 0} ≤ rank(M'_u)`.

    Math (tex:945-949, 962-963): after the column flush `U`, the first `r_i`
    columns of each `M_i·U` are linearly independent (they span the column space
    `⋃_i columnSet(M_i)` of total dimension `∑_i r_i = rank([M_1;⋯;M_c])`, and there
    are exactly `∑_i r_i` of them, so a spanning set of size = dimension is a basis).
    The first column of each block `i` with `r_i ≠ 0` is one such flushed column, so
    the `#{i : r_i ≠ 0}` columns of `M'_u` (column `i` = flushed column `0` of
    `M_i·U`) are a linearly independent subfamily, giving the rank bound. -/
theorem flush_support_le_rank {a b c : ℕ}
    (M : Fin c → Matrix (Fin a) (Fin b) F)
    (hF : ((concatBlocks M).rank : Cardinal) < Cardinal.mk F) :
    ∃ u : Fin b → F,
      (Finset.univ.filter (fun i => rankIncrement M i ≠ 0)).card ≤
        (Matrix.of (fun (row : Fin a) (i : Fin c) => ∑ l, M i row l * u l)).rank := by
  classical
  have hr : ∀ i : Fin c, rankIncrement M i ≤ b := rankIncrement_le_width M
  -- When `b = 0` every increment is `0`, so the support is empty and the bound is trivial.
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · subst hb0
    refine ⟨fun l => Fin.elim0 l, ?_⟩
    have hsupp_empty : (Finset.univ.filter (fun i => rankIncrement M i ≠ 0)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro i _
      simp only [not_not]
      exact Nat.le_zero.mp (hr i)
    rw [hsupp_empty, Finset.card_empty]
    exact Nat.zero_le _
  haveI : NeZero b := ⟨Nat.pos_iff_ne_zero.mp hbpos⟩
  obtain ⟨U, _hUdet, hspan⟩ := flush_lemma M hF
  -- `u := first column of U`.
  refine ⟨fun l => U l 0, ?_⟩
  set u : Fin b → F := fun l => U l 0 with hu
  set N : Matrix (Fin a) (Fin c) F :=
    Matrix.of (fun (row : Fin a) (i : Fin c) => ∑ l, M i row l * u l) with hN
  -- The flushed family, indexed by `Σ i, Fin (min r_i b)`.
  set flushFam : (Σ i : Fin c, Fin (Nat.min (rankIncrement M i) b)) → (Fin a → F) :=
    fun p => fun row => (M p.1 * U) row
      ⟨p.2.val, lt_of_lt_of_le p.2.isLt (Nat.min_le_right _ _)⟩ with hflushFam
  -- `range flushFam = ⋃ i, firstColumns (M i * U) r_i`.
  have hrange : Set.range flushFam =
      ⋃ i : Fin c, firstColumns (M i * U) (rankIncrement M i) := by
    ext v
    simp only [Set.mem_range, Set.mem_iUnion, firstColumns]
    constructor
    · rintro ⟨⟨i, j⟩, rfl⟩; exact ⟨i, ⟨j, rfl⟩⟩
    · rintro ⟨i, ⟨j, rfl⟩⟩; exact ⟨⟨i, j⟩, rfl⟩
  -- finrank of the flushed span = `(concatBlocks M).rank = ∑ r_i`.
  have hspan_eq : Submodule.span F (Set.range flushFam) = prevSpan M c := by
    rw [hrange, hspan]
    -- `span(⋃ columnSet) = prevSpan M c`.
    unfold prevSpan
    congr 1
    ext v
    simp only [Set.mem_iUnion, columnSet]
    constructor
    · rintro ⟨j, hv⟩; exact ⟨j, j.isLt, hv⟩
    · rintro ⟨j, _, hv⟩; exact ⟨j, hv⟩
  have hfinrank_span : Module.finrank F (Submodule.span F (Set.range flushFam))
      = (concatBlocks M).rank := by
    rw [hspan_eq, ← prefixRank_eq_finrank_prevSpan, prefixRank_full]
  -- Cardinality of the index type: `∑ i, min r_i b = ∑ i, r_i = (concatBlocks M).rank`.
  have hcard : Fintype.card (Σ i : Fin c, Fin (Nat.min (rankIncrement M i) b))
      = (concatBlocks M).rank := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [Finset.sum_congr rfl (fun i _ => Nat.min_eq_left (hr i))]
    rw [← Finset.sum_attach Finset.univ (fun i => rankIncrement M i)]
    simp only [Finset.sum_attach]
    exact sum_rankIncrement_eq_rank M
  -- The flushed family is linearly independent (spanning set of size = dim).
  have hLI : LinearIndependent F flushFam := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    rw [hcard]
    -- `Set.finrank F (range flushFam) = finrank(span ...) = (concatBlocks M).rank`.
    show (concatBlocks M).rank = Set.finrank F (Set.range flushFam)
    rw [Set.finrank, hfinrank_span]
  -- The subfamily of first columns over `{i : r_i ≠ 0}` injects into the index type.
  set supp : Finset (Fin c) := Finset.univ.filter (fun i => rankIncrement M i ≠ 0)
    with hsupp
  -- For `i ∈ supp`, `min r_i b ≥ 1` so `0 : Fin (min r_i b)` exists.
  have hpos : ∀ i : {i // i ∈ supp},
      0 < Nat.min (rankIncrement M i.val) b := by
    rintro ⟨i, hi⟩
    simp only [hsupp, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hri : 1 ≤ rankIncrement M i := Nat.one_le_iff_ne_zero.mpr hi
    have hb : 1 ≤ b := le_trans hri (hr i)
    exact Nat.lt_min.mpr ⟨hri, hb⟩
  -- Injection `{i // i ∈ supp} → Σ i, Fin (min r_i b)`, `i ↦ ⟨i, 0⟩`.
  set ι : {i // i ∈ supp} → (Σ i : Fin c, Fin (Nat.min (rankIncrement M i) b)) :=
    fun i => ⟨i.val, ⟨0, hpos i⟩⟩ with hι
  have hιinj : Function.Injective ι := by
    rintro ⟨i, hi⟩ ⟨i', hi'⟩ heq
    simp only [hι, Sigma.mk.injEq] at heq
    exact Subtype.ext heq.1
  -- The subfamily is linearly independent.
  have hLIsub : LinearIndependent F (flushFam ∘ ι) := hLI.comp ι hιinj
  -- `flushFam (ι i) = N.col i`.
  have hsubcol : ∀ i : {i // i ∈ supp}, (flushFam ∘ ι) i = N.col i.val := by
    rintro ⟨i, hi⟩
    funext row
    simp only [Function.comp_apply, hι, hflushFam, Matrix.col_apply, hN, Matrix.of_apply,
      Matrix.mul_apply, hu]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    congr 1
  -- `support = finrank(span(range subfamily)) ≤ finrank(span(range N.col)) = N.rank`.
  rw [Matrix.rank_eq_finrank_span_cols]
  calc supp.card
      = Fintype.card {i // i ∈ supp} := by
        rw [Fintype.card_coe]
    _ = Module.finrank F (Submodule.span F (Set.range (flushFam ∘ ι))) := by
        rw [finrank_span_eq_card hLIsub, Fintype.card_coe]
    _ ≤ Module.finrank F (Submodule.span F (Set.range N.col)) := by
        apply Submodule.finrank_mono
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        rw [hsubcol i]
        exact Submodule.subset_span ⟨i.val, rfl⟩

/-! ## Slice tensors and slice-flattening monotonicity (tex:868-878, 920-921, 947-949).

Briët et al. ITCS 2024, Thm. 3.2 invokes, twice, the fact that a *slice* of `T`
(obtained by fixing the coordinates on some legs to fixed values) has a
flattening matrix that is a **column-submatrix** of `flattenMatrix T I`:

* tex:920-921: "Since `M_i` is a submatrix of `T_I`, we have
  `tensorrank_I(T) ≥ tensorrank_k(P^{(L)}_i T)`."  Here `M_i` (the `k`-flattening
  of the `L`-slice `P^{(L)}_i T`) is the block of columns of `T_I` whose
  `L`-coordinates equal `i`.
* tex:947-949: "the `L`-flattening of `P^{(k)}_1 T` is a matrix `M'` for which the
  columns are precisely each first column of the matrices `M_i` ...  In
  particular `tensorrank_I(T) ≥ tensorrank_L(P^{(k)}_1 T)`."

Both are instances of the single column-submatrix monotonicity lemma
`flatRank_submatrix_le` below.  The reduced-arity slice tensor is
`sliceLeg T ℓ v` (fix leg `ℓ` to value `v`), realized on the same `Fin k` arity
with `d ℓ` collapsed to dimension `1` via `Function.update d ℓ 1`. -/

/-- `flatRank T I` is by definition the rank of the `I`-flattening matrix.  This
    `rfl` lemma lets downstream proofs rewrite `flatRank` into `Matrix.rank`
    without forcing the elaborator to `whnf` the (heavy `Pi`-`Fintype`) index
    types during unification. -/
theorem flatRank_eq_rank {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (I : Finset (Fin k)) :
    flatRank T I = (flattenMatrix T I).rank := rfl

/-- Any column-submatrix of `flattenMatrix T I` has rank `≤ flatRank T I`.  This
    is the matrix-level form of "a slice (a sub-collection of columns of the
    `I`-flattening) has flattening rank at most `flatRank_I(T)`" used twice in
    Briët et al. ITCS 2024, Thm. 3.2 (tex:926-927, 953-955).

    Stated against `(flattenMatrix T I).rank` (not `flatRank T I`); bridge via
    `flatRank_eq_rank`.  Proved through `Matrix.rank_eq_finrank_span_cols` +
    `Submodule.finrank_mono` (rather than `Matrix.rank_submatrix_le`) to avoid an
    elaboration blowup on the heavy `Pi`-`Fintype` flattening index types. -/
theorem flattenMatrix_rank_submatrix_le {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (I : Finset (Fin k)) {β : Type*} [Fintype β]
    (g : β → (∀ j : {j : Fin k // j ∉ I}, Fin (d j.val))) :
    ((flattenMatrix T I).submatrix id g).rank ≤ (flattenMatrix T I).rank := by
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  apply Submodule.finrank_mono
  rw [Submodule.span_le]
  rintro _ ⟨col, rfl⟩
  exact Submodule.subset_span ⟨g col, by ext r; simp [Matrix.submatrix]⟩

/-- **`ℓ`-slice of `T`** (Briët et al. ITCS 2024, tex:874-884): the tensor
    obtained from `T` by fixing the leg-`ℓ` coordinate to `v`.  Realized on the
    same `Fin k` arity with the format `d` updated so that leg `ℓ` has dimension
    `1` (i.e. `Function.update d ℓ 1`); leg `ℓ` then carries no information.

    The single `Fin (1 : ℕ+) = Fin 1` value on leg `ℓ` is `0`; all other legs
    keep their coordinate. -/
noncomputable def sliceLeg {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (ℓ : Fin k) (v : Fin (d ℓ)) :
    KTensor F (Function.update d ℓ (1 : ℕ+)) :=
  fun idx => T (fun i =>
    if h : i = ℓ then h ▸ v
    else by
      have : (Function.update d ℓ (1 : ℕ+)) i = d i := Function.update_of_ne h _ _
      exact this ▸ idx i)

set_option maxHeartbeats 1600000 in
-- Raised heartbeats: the column-submatrix reindexing unfolds large `Fin`-product
-- equivalences whose elaboration exceeds the default budget.
/-- **Slice-flattening monotonicity** (Briët et al. ITCS 2024, tex:926-927,
    953-955): for a complement leg `ℓ ∉ I`, the `I`-flattening of the `ℓ`-slice
    `sliceLeg T ℓ v` is a column-submatrix of `flattenMatrix T I` (the columns
    whose leg-`ℓ` coordinate is `v`), so its rank is `≤ flatRank T I`.

    This is the single monotonicity fact invoked twice in the proof of
    Theorem 3.2: "`M_i` is a submatrix of `T_I`" (tex:920-921) and "`M'` is a
    submatrix of `T_I`" (tex:947-949). -/
theorem flatRank_sliceLeg_le {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (I : Finset (Fin k)) (ℓ : Fin k) (hℓ : ℓ ∉ I)
    (v : Fin (d ℓ)) :
    flatRank (sliceLeg T ℓ v) I ≤ flatRank T I := by
  classical
  -- For complement-or-row legs `i ≠ ℓ`, the updated format agrees with `d`.
  have hne : ∀ {i : Fin k}, i ∈ I → i ≠ ℓ := by
    rintro i hi rfl; exact hℓ hi
  -- Row equiv: `(∀ i∈I, Fin (d' i)) ≃ (∀ i∈I, Fin (d i))`, since `i∈I → i≠ℓ`.
  let erow : (∀ i : {i : Fin k // i ∈ I}, Fin ((Function.update d ℓ (1 : ℕ+)) i.val))
      ≃ (∀ i : {i : Fin k // i ∈ I}, Fin (d i.val)) :=
    Equiv.piCongrRight (fun i =>
      finCongr (congrArg (fun (m : ℕ+) => (m : ℕ)) (Function.update_of_ne (hne i.2) _ _)))
  -- Column injection: send a slice-column index to the `T`-column index whose
  -- leg-`ℓ` coordinate is `v` (and which agrees elsewhere).
  let gcol : (∀ j : {j : Fin k // j ∉ I}, Fin ((Function.update d ℓ (1 : ℕ+)) j.val))
      → (∀ j : {j : Fin k // j ∉ I}, Fin (d j.val)) :=
    fun col j =>
      if h : j.val = ℓ then (Fin.cast (congrArg (fun (m : ℕ+) => (m : ℕ)) (congrArg d h.symm)) v)
      else (finCongr (congrArg (fun (m : ℕ+) => (m : ℕ))
              (Function.update_of_ne h _ _)) (col j))
  -- The slice flattening is the row-reindexed column-submatrix of `T`'s.
  have hfact : flattenMatrix (sliceLeg T ℓ v) I
      = ((flattenMatrix T I).submatrix id gcol).submatrix erow id := by
    funext row col
    simp only [Matrix.submatrix_apply, id_eq]
    change sliceLeg T ℓ v (fun i => if h : i ∈ I then row ⟨i, h⟩ else col ⟨i, h⟩)
      = flattenMatrix T I (erow row) (gcol col)
    change sliceLeg T ℓ v _ = T (fun i => if h : i ∈ I then (erow row) ⟨i, h⟩
        else (gcol col) ⟨i, h⟩)
    unfold sliceLeg
    congr 1
    funext i
    -- Both sides land in `Fin (d i)`; compare via `.val` after the casts.
    by_cases hiI : i ∈ I
    · -- Row leg: `i ∈ I`, so `i ≠ ℓ`.
      have hiℓ : i ≠ ℓ := hne hiI
      rw [dif_neg hiℓ, dif_pos hiI]
      apply Fin.ext
      simp only [erow, Equiv.piCongrRight_apply, Pi.map_apply, finCongr_apply,
        Fin.val_cast, eqRec_eq_cast, dif_pos hiI]
      rw [← Fin.cast_eq_cast (congrArg (fun m : ℕ+ => (m : ℕ))
        (Function.update_of_ne hiℓ (1 : ℕ+) d)), Fin.val_cast]
    · -- Column leg: `i ∉ I`.
      rw [dif_neg hiI]
      by_cases hiℓ : i = ℓ
      · -- The fixed leg `ℓ`: both sides reduce to the slice value `v`.
        subst hiℓ
        simp only [gcol, dif_pos rfl, dite_true]
        apply Fin.ext
        simp
      · -- Other column legs `i ≠ ℓ`: same coordinate, format agrees.
        rw [dif_neg hiℓ]
        simp only [gcol, dif_neg hiℓ]
        apply Fin.ext
        rw [dif_neg hiI]
        simp only [finCongr_apply, Fin.val_cast, eqRec_eq_cast]
        rw [← Fin.cast_eq_cast (congrArg (fun m : ℕ+ => (m : ℕ))
          (Function.update_of_ne hiℓ (1 : ℕ+) d)), Fin.val_cast]
  rw [flatRank_eq_rank, flatRank_eq_rank, hfact]
  rw [show (((flattenMatrix T I).submatrix id gcol).submatrix erow id)
      = ((flattenMatrix T I).submatrix id gcol).submatrix erow (Equiv.refl _) from rfl,
    Matrix.rank_submatrix _ erow (Equiv.refl _)]
  exact flattenMatrix_rank_submatrix_le T I gcol

/-- **The `ℓ`-slice is a restriction of `T` (Briët et al. ITCS 2024, tex:874-884).**
    `sliceLeg T ℓ v ≤ₜ T`: leg `ℓ` is restricted by the `1 × d ℓ` selector matrix
    picking coordinate `v` (`1` at column `v`, `0` elsewhere); every other leg `i`
    uses the identity matrix (its dimension is unchanged, `update d ℓ 1 i = d i`).
    The Kronecker contraction then collapses the sum to the single index whose
    leg-`ℓ` coordinate is `v`, reproducing `sliceLeg T ℓ v`. -/
lemma sliceLeg_restricts {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (ℓ : Fin k) (v : Fin (d ℓ)) :
    Restricts (sliceLeg T ℓ v) T := by
  classical
  -- Leg matrices: identity off `ℓ`, the coordinate-`v` selector on `ℓ`.
  refine ⟨fun i => if hi : i = ℓ then
      (fun _ col => if (Fin.cast (by rw [hi]) col) = v then (1 : F) else 0)
    else (fun row col =>
      if (Fin.cast (by rw [Function.update_of_ne hi]) row) = col then 1 else 0), ?_⟩
  intro jdx
  -- The unique surviving index `idx₀`: leg `ℓ ↦ v`, leg `i ≠ ℓ ↦ (cast) jdx i`.
  set idx₀ : (∀ i : Fin k, Fin (d i)) := fun i =>
    if hi : i = ℓ then hi ▸ v
    else Fin.cast (by rw [Function.update_of_ne hi]) (jdx i) with hidx₀
  rw [Finset.sum_eq_single idx₀]
  · -- The surviving term: product is `1`, and `T idx₀ = sliceLeg T ℓ v jdx`.
    have hprod1 : (∏ i, (if hi : i = ℓ then
          (fun _ col => if (Fin.cast (by rw [hi]) col) = v then (1 : F) else 0)
        else (fun row col =>
          if (Fin.cast (by rw [Function.update_of_ne hi]) row) = col then 1 else 0))
          (jdx i) (idx₀ i)) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      by_cases hi : i = ℓ
      · simp only [dif_pos hi]
        rw [if_pos]
        subst hi
        simp [hidx₀]
      · simp only [dif_neg hi]
        rw [if_pos]
        simp only [hidx₀, dif_neg hi]
    rw [hprod1, one_mul]
    -- `T idx₀ = sliceLeg T ℓ v jdx`.
    unfold sliceLeg
    congr 1
    funext i
    by_cases hi : i = ℓ
    · subst hi; simp [hidx₀]
    · simp only [hidx₀, dif_neg hi]
      apply Fin.ext
      rw [Fin.val_cast, eqRec_eq_cast, ← Fin.cast_eq_cast, Fin.val_cast]
      rw [Function.update_of_ne hi]
  · -- Off the surviving index, the product is `0`.
    intro idx _ hne
    have : ∃ i, idx i ≠ idx₀ i := by
      by_contra hall
      push_neg at hall
      exact hne (funext hall)
    obtain ⟨i₀, hi₀⟩ := this
    apply mul_eq_zero_of_left
    apply Finset.prod_eq_zero (Finset.mem_univ i₀)
    by_cases hi : i₀ = ℓ
    · simp only [dif_pos hi]
      rw [if_neg]
      intro hc
      apply hi₀
      simp only [hidx₀, dif_pos hi]
      subst hi
      apply Fin.ext
      have := congrArg Fin.val hc
      simpa using this
    · simp only [dif_neg hi]
      rw [if_neg]
      intro hc
      apply hi₀
      simp only [hidx₀, dif_neg hi]
      apply Fin.ext
      have := congrArg Fin.val hc
      simpa using this.symm
  · intro hni; exact absurd (Finset.mem_univ _) hni

/-- **`subrankPair` under slicing a complement leg (Briët et al. ITCS 2024,
    tex:923-969).**  For any complement leg `ℓ` and slice value `v`,
    `subrankPair (sliceLeg T ℓ v) i j ≤ subrankPair T i j`: the slice is a
    restriction of `T` (`sliceLeg_restricts`), and `subrankPair` is monotone under
    restriction (`subrankPair_mono_of_restricts`). -/
lemma subrankPair_sliceLeg_le {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (ℓ : Fin k) (v : Fin (d ℓ)) (i j : Fin k) :
    subrankPair (sliceLeg T ℓ v) i j ≤ subrankPair T i j :=
  subrankPair_mono_of_restricts (sliceLeg_restricts T ℓ v) i j

/-- Two `Fin`-valued applications of a dependent function at provably-equal
    indices have equal `.val`.  Pure dependent-`Fin` helper used to prove the
    coordinate-cast bookkeeping in `flatRank_dropLeg`. -/
theorem dfun_val_congr {ι : Type*} {φ : ι → ℕ} (g : ∀ x, Fin (φ x))
    {a b : ι} (hab : a = b) : (g a).val = (g b).val := by subst hab; rfl

/-- **Leg drop** (Briët et al. ITCS 2024, tex:884): for a `(k = n+1)`-tensor `T`
    one of whose legs `ℓ` has dimension `1` (`hℓ : d ℓ = 1`), `dropLeg T ℓ hℓ` is
    the genuinely `n`-ary tensor obtained by deleting the (information-free)
    dimension-`1` leg `ℓ`, reindexing the remaining legs by `ℓ.succAbove`.

    The lone `Fin (d ℓ) = Fin 1` coordinate of the dropped leg is reinserted at
    position `ℓ` via `Fin.insertNth` (as `hℓ ▸ 0`).  This is the *arity-reduction
    bridge* that lets the strong-induction hypothesis (stated at arity `< k`)
    apply to the dimension-`1`-leg slices `sliceLeg` produces (which keep arity
    `k`).  See `flatRank_dropLeg` for the rank-preservation statement. -/
noncomputable def dropLeg {n : ℕ} {d : Fin (n + 1) → ℕ+}
    (T : KTensor F d) (ℓ : Fin (n + 1)) (hℓ : d ℓ = 1) :
    KTensor F (fun i : Fin n => d (ℓ.succAbove i)) :=
  fun idx => T (Fin.insertNth ℓ (hℓ ▸ (0 : Fin 1)) idx)

/-- **Dropping a dimension-`1` leg preserves flattening rank** (Briët et al.
    ITCS 2024, tex:884, 926, 953).  For a complement leg `ℓ ∉ I` of dimension `1`,
    the `I'`-flattening of `dropLeg T ℓ hℓ` (where `I'` is `I` pulled back along
    `ℓ.succAbove`) has the *same* matrix rank as the `I`-flattening of `T`:
    the dimension-`1` leg carries no column information, so the two flattening
    matrices are reindexings of each other (row reindex `erowPi`, column reindex
    `ecol`), and `Matrix.rank_submatrix` gives equality.

    This is the load-bearing identity behind both eq:(1) and eq:(2): it transports
    `flatRank` of an `(m+1)`- (resp. `(k-1)`-) leg `sliceLeg`-slice — which still
    has the ambient `Fin k` arity — to the genuinely smaller arity at which the
    induction hypothesis is stated. -/
theorem flatRank_dropLeg {n : ℕ} {d : Fin (n + 1) → ℕ+} (T : KTensor F d)
    (ℓ : Fin (n + 1)) (hℓ : d ℓ = 1) (I : Finset (Fin (n + 1))) (hℓI : ℓ ∉ I) :
    flatRank (dropLeg T ℓ hℓ) (Finset.univ.filter (fun i' => ℓ.succAbove i' ∈ I))
      = flatRank T I := by
  classical
  set I' : Finset (Fin n) := Finset.univ.filter (fun i' => ℓ.succAbove i' ∈ I) with hI'
  have hmemI' : ∀ i' : Fin n, i' ∈ I' ↔ ℓ.succAbove i' ∈ I := by intro i'; simp [hI']
  have hpre : ∀ (j : Fin (n + 1)) (h : j ≠ ℓ),
      ℓ.succAbove ((finSuccAboveEquiv ℓ).symm ⟨j, h⟩) = j := by
    intro j h
    have := (finSuccAboveEquiv ℓ).apply_symm_apply ⟨j, h⟩
    rw [finSuccAboveEquiv_apply] at this; exact congrArg Subtype.val this
  have hsymmsucc : ∀ (j' : Fin n),
      (finSuccAboveEquiv ℓ).symm ⟨ℓ.succAbove j', Fin.succAbove_ne ℓ j'⟩ = j' := by
    intro j'; rw [Equiv.symm_apply_eq, finSuccAboveEquiv_apply]
  have hval1 : ∀ (x y : Fin (d ℓ)), x = y := by
    intro x y; apply Fin.ext; have hd1 : (d ℓ : ℕ) = 1 := by rw [hℓ]; rfl
    omega
  let erow : {i' : Fin n // i' ∈ I'} ≃ {i : Fin (n + 1) // i ∈ I} :=
    { toFun := fun i' => ⟨ℓ.succAbove i'.1, (hmemI' i'.1).mp i'.2⟩
      invFun := fun i => ⟨(finSuccAboveEquiv ℓ).symm ⟨i.1, fun h => hℓI (h ▸ i.2)⟩,
        by rw [hmemI', hpre]; exact i.2⟩
      left_inv := fun i' => by apply Subtype.ext; exact hsymmsucc i'.1
      right_inv := fun i => by apply Subtype.ext; simp only [hpre] }
  let Zc : {i : Fin (n + 1) // i ∈ I} → Type _ := fun i => Fin (d i.val)
  let ec : ∀ i' : {i' : Fin n // i' ∈ I'}, Fin (d (ℓ.succAbove i'.1)) ≃ Zc (erow i') :=
    fun i' => finCongr (by rfl)
  let erowPi : (∀ i' : {i' : Fin n // i' ∈ I'}, Fin ((d (ℓ.succAbove i'.1))))
      ≃ (∀ i : {i : Fin (n + 1) // i ∈ I}, Zc i) :=
    Equiv.piCongr erow ec
  have herowPi : ∀ (row : ∀ i' : {i' : Fin n // i' ∈ I'}, Fin ((d (ℓ.succAbove i'.1))))
      (i' : {i' : Fin n // i' ∈ I'}),
      ((erowPi row) (erow i')).val = (row i').val := by
    intro row i'
    have h := Equiv.piCongr_apply_apply erow ec row i'
    rw [show erowPi row = Equiv.piCongr erow ec row from rfl, h]; rfl
  let ecol : (∀ j' : {j' : Fin n // j' ∉ I'}, Fin ((d (ℓ.succAbove j'.1))))
      ≃ (∀ j : {j : Fin (n + 1) // j ∉ I}, Fin (d j.val)) :=
    { toFun := fun col' j =>
        if h : j.1 = ℓ then (h ▸ hℓ ▸ (0 : Fin 1))
        else Fin.cast (by rw [hpre j.1 h]) (col' ⟨(finSuccAboveEquiv ℓ).symm ⟨j.1, h⟩,
          by rw [hmemI', hpre]; exact j.2⟩)
      invFun := fun col j' => Fin.cast rfl (col ⟨ℓ.succAbove j'.1, by
        rw [← hmemI']; exact j'.2⟩)
      left_inv := fun col' => by
        funext j'
        have hne : (ℓ.succAbove j'.1) ≠ ℓ := Fin.succAbove_ne ℓ j'.1
        simp only [dif_neg hne]
        apply Fin.ext; rw [Fin.val_cast, Fin.val_cast]
        exact dfun_val_congr col' (Subtype.ext (hsymmsucc j'.1) :
          (⟨(finSuccAboveEquiv ℓ).symm ⟨ℓ.succAbove j'.1, hne⟩, by rw [hsymmsucc]; exact j'.2⟩
            : {x : Fin n // x ∉ I'}) = j')
      right_inv := fun col => by
        funext j
        by_cases h : j.1 = ℓ
        · simp only [dif_pos h]; subst h; exact hval1 _ _
        · simp only [dif_neg h]
          apply Fin.ext; rw [Fin.val_cast, Fin.val_cast]
          exact dfun_val_congr col (Subtype.ext (hpre j.1 h) :
            (⟨ℓ.succAbove ((finSuccAboveEquiv ℓ).symm ⟨j.1, h⟩), by rw [hpre]; exact j.2⟩
              : {x : Fin (n + 1) // x ∉ I}) = j) }
  have hecol_apply : ∀ (col : ∀ j' : {j' : Fin n // j' ∉ I'}, Fin ((d (ℓ.succAbove j'.1))))
      (j : {j : Fin (n + 1) // j ∉ I}) (h : j.1 ≠ ℓ),
      (ecol col j).val = (col ⟨(finSuccAboveEquiv ℓ).symm ⟨j.1, h⟩,
        by rw [hmemI', hpre]; exact j.2⟩).val := by
    intro col j h
    simp only [ecol, Equiv.coe_fn_mk]
    rw [dif_neg h, Fin.val_cast]
  have hfact : flattenMatrix (dropLeg T ℓ hℓ) I'
      = (flattenMatrix T I).submatrix (⇑erowPi) (⇑ecol) := by
    funext row col
    simp only [Matrix.submatrix_apply]
    change dropLeg T ℓ hℓ (fun i => if h : i ∈ I' then row ⟨i, h⟩ else col ⟨i, h⟩)
      = T (fun i => if h : i ∈ I then (erowPi row) ⟨i, h⟩ else (ecol col) ⟨i, h⟩)
    unfold dropLeg
    congr 1
    funext i
    by_cases hiℓ : i = ℓ
    · subst hiℓ; rw [Fin.insertNth_apply_same, dif_neg hℓI]; exact hval1 _ _
    · set i'' : Fin n := (finSuccAboveEquiv ℓ).symm ⟨i, hiℓ⟩ with hi''
      have hsa : ℓ.succAbove i'' = i := hpre i hiℓ
      rw [show i = ℓ.succAbove i'' from hsa.symm, Fin.insertNth_apply_succAbove]
      by_cases hiI : i ∈ I
      · rw [dif_pos (show i'' ∈ I' by rw [hmemI', hsa]; exact hiI)]
        rw [dif_pos (show ℓ.succAbove i'' ∈ I by rw [hsa]; exact hiI)]
        apply Fin.ext
        exact (herowPi row ⟨i'', by rw [hmemI', hsa]; exact hiI⟩).symm
      · rw [dif_neg (show i'' ∉ I' by rw [hmemI', hsa]; exact hiI)]
        rw [dif_neg (show ℓ.succAbove i'' ∉ I by rw [hsa]; exact hiI)]
        have hne2 : (ℓ.succAbove i'') ≠ ℓ := Fin.succAbove_ne ℓ i''
        apply Fin.ext
        rw [hecol_apply col ⟨ℓ.succAbove i'', by rw [hsa]; exact hiI⟩ hne2]
        exact (dfun_val_congr col (Subtype.ext (hsymmsucc i'') :
          (⟨(finSuccAboveEquiv ℓ).symm ⟨ℓ.succAbove i'', hne2⟩,
            by rw [hsymmsucc, hmemI', hsa]; exact hiI⟩
            : {x : Fin n // x ∉ I'}) = ⟨i'', by rw [hmemI', hsa]; exact hiI⟩)).symm
  rw [flatRank, flatRank, hfact, Matrix.rank_submatrix]

/-! ## Multi-leg slice substrate (tex:919-939, eq:11a; tex:942-963, eq:12a).

The eq:(1)/(2) block identities (`hB1_block`, `hB2` in `subrankPair_prod_ge_flatRank`)
identify each column-*block* `M_i` of the `I`-flattening with the flattening of a
slice that fixes **several** complement legs simultaneously (the whole internal
leg set `L`) to a multi-index `i`.  Concretely (paper tex:920-923, eq:11a): writing
`P^{(L)}_i T` for the `i`th `L`-slice, its `k`-flattening is the `(n_1⋯n_m) × n_k`
matrix `M_i`, which is a submatrix of `T_I`; hence
`rank_I(T) ≥ rank_k(P^{(L)}_i T) = rank(M_i)`.

`sliceLeg` fixes one leg; `multiSliceL` below folds that over a whole leg set `L`,
collapsing every `L`-leg to dimension `1`.  The block-rank identity
`block_rank_eq_flatRank_multiSliceL` then states that the rank of the column-block
of `flattenMatrix T I` selected by fixing the `L`-legs to `w` equals
`flatRank (multiSliceL T L w) I` — the formal content of "`M_i` is the
`k`-flattening of `P^{(L)}_i T`". -/

/-- **Multi-leg slice of `T`** (Briët et al. ITCS 2024, tex:925-929, eq:11a).
    The `i`th `L`-slice `P^{(L)}_i T`: the tensor obtained from `T` by fixing,
    *simultaneously*, the coordinate of every leg `ℓ ∈ L` to `w ℓ`.  Realized on
    the same `Fin k` arity with the format `d` updated so that every leg in `L`
    has dimension `1` (`fun i => if i ∈ L then 1 else d i`); the `L`-legs then
    carry no information.

    This is the finset-fold generalization of `sliceLeg` (which fixes a single
    leg): `sliceLeg T ℓ v = multiSliceL T {ℓ} (fun _ _ => v)` up to the format
    rewrite `Function.update d ℓ 1 = (fun i => if i ∈ {ℓ} then 1 else d i)`.  The
    value argument `w` supplies the fixed coordinate on each `L`-leg. -/
noncomputable def multiSliceL {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (L : Finset (Fin k))
    (w : ∀ ℓ : Fin k, ℓ ∈ L → Fin (d ℓ)) :
    KTensor F (fun i => if i ∈ L then (1 : ℕ+) else d i) :=
  fun idx => T (fun i =>
    if h : i ∈ L then w i h
    else by
      have : (if i ∈ L then (1 : ℕ+) else d i) = d i := if_neg h
      exact this ▸ idx i)

set_option maxHeartbeats 1600000 in
-- Raised heartbeats: the multi-leg column-block identification chains several
-- `Fin`-product reindexings, exceeding the default elaboration budget.
/-- **Multi-leg slice flattening ↔ column-block of `T_I`** (Briët et al. ITCS
    2024, Thm. 3.2, tex:925-929, eq:11a — the formal content of "`M_i` is the
    `k`-flattening of `P^{(L)}_i T`, a submatrix of `T_I`").

    For a leg set `L` **disjoint from `I`** (`hLI : ∀ ℓ ∈ L, ℓ ∉ I`), the
    `I`-flattening of the multi-slice `multiSliceL T L w` is a *row-reindex of a
    column-submatrix* of `flattenMatrix T I`: precisely the columns whose `L`-leg
    coordinates equal `w`.  Hence its `flatRank` equals the matrix rank of that
    column-block.

    **Intended call site (`hB1_block`).**  In `recursive_block_data` the block is
    `M i row col = flattenMatrix T I (rowEquiv row) (colEquiv (i, col))`, where
    `colEquiv (i, col)` is the complement-leg index whose `L`-coordinates are the
    multi-index `i ∈ Internal` and whose `ℓ_last`-coordinate is `col`.  Taking
    `L = (univ \ I) \ {ℓ_last}` and `w` = the coordinates `i` dictates, the
    column-block `fun row col => flattenMatrix T I row (gcol_w col)` selected here
    is, up to the `colEquiv`/`ecolSplit` reindex, exactly `M i`; so
    `(M i).rank = flatRank (multiSliceL T L w) I`, which the induction hypothesis
    then bounds.

    Hypotheses are exactly the source's: `L` disjoint from `I` (the internal legs
    are complement legs).  No extra hypotheses are added; the conclusion is the
    rank *equality* the source's "`M_i` is a submatrix of `T_I`" packages. -/
theorem flatRank_multiSliceL_eq_colBlock {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (I L : Finset (Fin k)) (hLI : ∀ ℓ ∈ L, ℓ ∉ I)
    (w : ∀ ℓ : Fin k, ℓ ∈ L → Fin (d ℓ)) :
    ∃ (erow : (∀ i : {i : Fin k // i ∈ I},
          Fin ((fun i => if i ∈ L then (1 : ℕ+) else d i) i.val))
        ≃ (∀ i : {i : Fin k // i ∈ I}, Fin (d i.val)))
      (gcol : (∀ j : {j : Fin k // j ∉ I},
          Fin ((fun i => if i ∈ L then (1 : ℕ+) else d i) j.val))
        → (∀ j : {j : Fin k // j ∉ I}, Fin (d j.val))),
      flattenMatrix (multiSliceL T L w) I
        = ((flattenMatrix T I).submatrix id gcol).submatrix erow id := by
  classical
  set d' : Fin k → ℕ+ := fun i => if i ∈ L then (1 : ℕ+) else d i with hd'
  -- Row legs are in `I`, hence (by disjointness) not in `L`, so the format agrees.
  have hrowfmt : ∀ {i : Fin k}, i ∈ I → d' i = d i := by
    intro i hi
    have hiL : i ∉ L := fun h => hLI i h hi
    simp only [hd', if_neg hiL]
  -- Row equiv: `(∀ i∈I, Fin (d' i)) ≃ (∀ i∈I, Fin (d i))`.
  let erow : (∀ i : {i : Fin k // i ∈ I}, Fin (d' i.val))
      ≃ (∀ i : {i : Fin k // i ∈ I}, Fin (d i.val)) :=
    Equiv.piCongrRight (fun i =>
      finCongr (congrArg (fun (m : ℕ+) => (m : ℕ)) (hrowfmt i.2)))
  -- Column injection: a multi-slice column index → the `T`-column index whose
  -- `L`-leg coordinates are `w` (and which agrees off `L`).
  let gcol : (∀ j : {j : Fin k // j ∉ I}, Fin (d' j.val))
      → (∀ j : {j : Fin k // j ∉ I}, Fin (d j.val)) :=
    fun col j =>
      if h : j.val ∈ L then (w j.val h)
      else (finCongr (congrArg (fun (m : ℕ+) => (m : ℕ)) (by simp [hd', if_neg h])) (col j))
  refine ⟨erow, gcol, ?_⟩
  funext row col
  simp only [Matrix.submatrix_apply, id_eq]
  change multiSliceL T L w (fun i => if h : i ∈ I then row ⟨i, h⟩ else col ⟨i, h⟩)
    = flattenMatrix T I (erow row) (gcol col)
  change multiSliceL T L w _ = T (fun i => if h : i ∈ I then (erow row) ⟨i, h⟩
      else (gcol col) ⟨i, h⟩)
  unfold multiSliceL
  congr 1
  funext i
  by_cases hiL : i ∈ L
  · -- `L`-leg: both sides reduce to the fixed slice value `w i`.
    have hiI : i ∉ I := hLI i hiL
    rw [dif_pos hiL, dif_neg hiI]
    simp only [gcol, dif_pos hiL]
  · -- Off `L`: split on whether `i` is a row leg or a column leg.
    rw [dif_neg hiL]
    by_cases hiI : i ∈ I
    · -- Row leg: `i ∈ I`.
      simp only [dif_pos hiI]
      apply Fin.ext
      simp only [erow, Equiv.piCongrRight_apply, Pi.map_apply, finCongr_apply,
        Fin.val_cast, eqRec_eq_cast]
      rw [← Fin.cast_eq_cast (congrArg (fun m : ℕ+ => (m : ℕ)) (if_neg hiL)), Fin.val_cast]
    · -- Column leg `i ∉ I`, `i ∉ L`: same coordinate, format agrees.
      rw [dif_neg hiI]
      simp only [gcol, dif_neg hiL]
      apply Fin.ext
      rw [dif_neg hiI]
      simp only [finCongr_apply, Fin.val_cast, eqRec_eq_cast]
      rw [← Fin.cast_eq_cast (congrArg (fun m : ℕ+ => (m : ℕ)) (if_neg hiL)), Fin.val_cast]

/-- **Multi-leg slice flattening rank ≤ `flatRank T I`** (Briët et al. ITCS 2024,
    Thm. 3.2, tex:926-927, eq:11a: "`M_i` is a submatrix of `T_I`, so
    `rank_I(T) ≥ rank_k(P^{(L)}_i T)`").  Immediate corollary of
    `flatRank_multiSliceL_eq_colBlock` via column-submatrix monotonicity.

    This is the multi-leg analogue of `flatRank_sliceLeg_le`; together with the
    arity-reduction `dropLeg`/`flatRank_dropLeg` it is the substrate the eq:(1)
    bound `hB1_block` consumes. -/
theorem flatRank_multiSliceL_le {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (I L : Finset (Fin k)) (hLI : ∀ ℓ ∈ L, ℓ ∉ I)
    (w : ∀ ℓ : Fin k, ℓ ∈ L → Fin (d ℓ)) :
    flatRank (multiSliceL T L w) I ≤ flatRank T I := by
  classical
  obtain ⟨erow, gcol, hfact⟩ := flatRank_multiSliceL_eq_colBlock T I L hLI w
  rw [flatRank_eq_rank, flatRank_eq_rank, hfact]
  rw [show (((flattenMatrix T I).submatrix id gcol).submatrix erow id)
      = ((flattenMatrix T I).submatrix id gcol).submatrix erow (Equiv.refl _) from rfl,
    Matrix.rank_submatrix _ erow (Equiv.refl _)]
  exact flattenMatrix_rank_submatrix_le T I gcol

/-- **The multi-leg slice is a restriction of `T`** (Briët et al. ITCS 2024,
    tex:925-929).  `multiSliceL T L w ≤ₜ T`: every leg `ℓ ∈ L` is restricted by the
    `1 × d ℓ` selector matrix picking coordinate `w ℓ`; every leg `i ∉ L` uses the
    identity matrix (its dimension is unchanged, `(if i∈L then 1 else d i) = d i`).
    The Kronecker contraction collapses the sum to the single index whose `L`-leg
    coordinates are `w`, reproducing `multiSliceL T L w`.

    This is the multi-leg analogue of `sliceLeg_restricts`. -/
lemma multiSliceL_restricts {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (L : Finset (Fin k))
    (w : ∀ ℓ : Fin k, ℓ ∈ L → Fin (d ℓ)) :
    Restricts (multiSliceL T L w) T := by
  classical
  -- Leg matrices: identity off `L`, the coordinate-`w ℓ` selector on `ℓ ∈ L`.
  refine ⟨fun i => if hi : i ∈ L then
      (fun _ col => if col = w i hi then (1 : F) else 0)
    else (fun row col =>
      if (Fin.cast (by simp only [if_neg hi]) row) = col then 1 else 0), ?_⟩
  intro jdx
  -- The unique surviving index `idx₀`: leg `ℓ ∈ L ↦ w ℓ`, leg `i ∉ L ↦ (cast) jdx i`.
  set idx₀ : (∀ i : Fin k, Fin (d i)) := fun i =>
    if hi : i ∈ L then w i hi
    else Fin.cast (by simp only [if_neg hi]) (jdx i) with hidx₀
  rw [Finset.sum_eq_single idx₀]
  · -- The surviving term: product is `1`, and `T idx₀ = multiSliceL T L w jdx`.
    have hprod1 : (∏ i, (if hi : i ∈ L then
          (fun _ col => if col = w i hi then (1 : F) else 0)
        else (fun row col =>
          if (Fin.cast (by simp only [if_neg hi]) row) = col then 1 else 0))
          (jdx i) (idx₀ i)) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      by_cases hi : i ∈ L
      · simp only [dif_pos hi]
        rw [if_pos]
        simp only [hidx₀, dif_pos hi]
      · simp only [dif_neg hi]
        rw [if_pos]
        simp only [hidx₀, dif_neg hi]
    rw [hprod1, one_mul]
    -- `T idx₀ = multiSliceL T L w jdx`.
    unfold multiSliceL
    congr 1
    funext i
    by_cases hi : i ∈ L
    · simp only [hidx₀, dif_pos hi]
    · simp only [hidx₀, dif_neg hi]
      apply Fin.ext
      rw [eqRec_eq_cast, ← Fin.cast_eq_cast (by simp only [if_neg hi]), Fin.val_cast]
  · -- Off the surviving index, the product is `0`.
    intro idx _ hne
    have hex : ∃ i, idx i ≠ idx₀ i := by
      by_contra hall
      push_neg at hall
      exact hne (funext hall)
    obtain ⟨i₀, hi₀⟩ := hex
    apply mul_eq_zero_of_left
    apply Finset.prod_eq_zero (Finset.mem_univ i₀)
    by_cases hi : i₀ ∈ L
    · simp only [dif_pos hi]
      rw [if_neg]
      intro hc
      apply hi₀
      simp only [hidx₀, dif_pos hi]
      exact hc
    · simp only [dif_neg hi]
      rw [if_neg]
      intro hc
      apply hi₀
      simp only [hidx₀, dif_neg hi]
      apply Fin.ext
      have := congrArg Fin.val hc
      rw [Fin.val_cast] at this
      exact this.symm
  · intro hni; exact absurd (Finset.mem_univ _) hni

/-- **`subrankPair` under a multi-leg slice** (Briët et al. ITCS 2024, tex:925-969).
    `subrankPair (multiSliceL T L w) i j ≤ subrankPair T i j`: the multi-slice is a
    restriction of `T` (`multiSliceL_restricts`), and `subrankPair` is monotone
    under restriction (`subrankPair_mono_of_restricts`).  Multi-leg analogue of
    `subrankPair_sliceLeg_le`. -/
lemma subrankPair_multiSliceL_le {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (L : Finset (Fin k))
    (w : ∀ ℓ : Fin k, ℓ ∈ L → Fin (d ℓ)) (i j : Fin k) :
    subrankPair (multiSliceL T L w) i j ≤ subrankPair T i j :=
  subrankPair_mono_of_restricts (multiSliceL_restricts T L w) i j

/-- **Vector-contraction slice of `T`** (Briët et al. ITCS 2024, Thm. 3.2,
    tex:951-955, 961-963).  Contract leg `ℓ` of `T` by the covector `u : Fin (d ℓ)
    → F`: `sliceVec T ℓ u idx = ∑ j, u j · T (idx with leg ℓ ↦ j)`.  This is the
    `u`-weighted superposition of all `ℓ`-coordinate slices; for `u = e_v` (the
    `v`-th basis covector) it reduces to the coordinate slice `multiSliceL T {ℓ}
    (·↦v)`.  Realized on the same `Fin k` arity with leg `ℓ` collapsed to dimension
    `1` (format `fun i => if i ∈ {ℓ} then 1 else d i`, matching `multiSliceL`),
    so it can feed the same arity-reduction / induction machinery.

    Math role (tex:955-957): the `I`-flattening of `sliceVec T ℓ_last u` is the
    matrix `M'` whose columns are the `u`-contractions of the blocks `M_i`. -/
noncomputable def sliceVec {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (ℓ : Fin k) (u : Fin (d ℓ) → F) :
    KTensor F (fun i => if i ∈ ({ℓ} : Finset (Fin k)) then (1 : ℕ+) else d i) :=
  fun idx => ∑ j : Fin (d ℓ), u j * T (fun i =>
    if h : i = ℓ then (h ▸ j)
    else by
      have : (fun i => if i ∈ ({ℓ} : Finset (Fin k)) then (1 : ℕ+) else d i) i = d i := by
        simp only [Finset.mem_singleton, if_neg h]
      exact this ▸ idx i)

set_option maxHeartbeats 1600000 in
-- The full-index Kronecker contraction over the heavy `Pi`-`Fintype` index type,
-- reindexed by the `ℓ`-coordinate, needs a raised heartbeat budget.
/-- **The vector slice is a restriction of `T`** (Briët et al. ITCS 2024,
    tex:951-955).  `sliceVec T ℓ u ≤ₜ T`: leg `ℓ` is restricted by the `1 × d ℓ`
    covector matrix whose single row is `u` (entry at column `j` is `u j`); every
    other leg `i` uses the identity matrix (its dimension is unchanged,
    `(if i∈{ℓ} then 1 else d i) = d i`).  The Kronecker contraction then sums over
    the `ℓ`-coordinate `j` with weight `u j`, reproducing `sliceVec T ℓ u`.

    Mirror of `sliceLeg_restricts`/`multiSliceL_restricts`, with the selector row
    `u` in place of the single coordinate selector. -/
lemma sliceVec_restricts {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (ℓ : Fin k) (u : Fin (d ℓ) → F) :
    Restricts (sliceVec T ℓ u) T := by
  classical
  -- Leg matrices: the covector `u` on leg `ℓ` (`1 × d ℓ`), identity elsewhere.
  refine ⟨fun i => if hi : i = ℓ then
      (fun _ col => u (Fin.cast (by rw [hi]) col))
    else (fun row col =>
      if (Fin.cast (by simp only [Finset.mem_singleton, if_neg hi]) row) = col then 1 else 0),
    ?_⟩
  intro jdx
  -- Abbreviations for the leg matrices and the per-index product.
  set A : ∀ i : Fin k, Matrix
      (Fin ((fun i => if i ∈ ({ℓ} : Finset (Fin k)) then (1 : ℕ+) else d i) i))
      (Fin (d i)) F :=
    fun i => if hi : i = ℓ then
        (fun _ col => u (Fin.cast (by rw [hi]) col))
      else (fun row col =>
        if (Fin.cast (by simp only [Finset.mem_singleton, if_neg hi]) row) = col
          then (1 : F) else 0) with hA
  change sliceVec T ℓ u jdx
    = ∑ idx : (∀ i : Fin k, Fin (d i)), (∏ i, A i (jdx i) (idx i)) * T idx
  -- The surviving index for `ℓ`-coordinate `j`: leg `ℓ ↦ j`, leg `i ≠ ℓ ↦ cast (jdx i)`.
  set idxOf : Fin (d ℓ) → (∀ i : Fin k, Fin (d i)) := fun j i =>
    if hi : i = ℓ then (hi ▸ j)
    else Fin.cast (by simp only [Finset.mem_singleton, if_neg hi]) (jdx i) with hidxOf
  have hidxOf_inj : Function.Injective idxOf := by
    intro j j' hjj
    have := congrFun hjj ℓ
    simp only [hidxOf, dif_pos rfl] at this
    exact this
  -- Value of the product at `idxOf j`: it is `u j`.
  have hprod_idxOf : ∀ j : Fin (d ℓ), (∏ i, A i (jdx i) (idxOf j i)) = u j := by
    intro j
    rw [Finset.prod_eq_single ℓ]
    · -- leg `ℓ`: `A ℓ (jdx ℓ) (idxOf j ℓ) = u (cast (cast j)) = u j`.
      simp only [hA, hidxOf, dif_pos rfl]
      congr 1
    · intro i _ hiℓ
      simp only [hA, hidxOf, dif_neg hiℓ, if_true]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- Value of the product at any `idx` NOT of the form `idxOf j`: it is `0`.
  have hprod_zero : ∀ idx : (∀ i : Fin k, Fin (d i)),
      idx ∉ Finset.univ.image idxOf → (∏ i, A i (jdx i) (idx i)) = 0 := by
    intro idx hidx
    -- If every leg `i ≠ ℓ` had `idx i = cast (jdx i)`, then `idx = idxOf (idx ℓ)`.
    by_cases hall : ∀ (i : Fin k) (hi : i ≠ ℓ), (idx i).val = (jdx i).val
    · exfalso
      apply hidx
      refine Finset.mem_image.mpr ⟨idx ℓ, Finset.mem_univ _, ?_⟩
      funext i
      by_cases hi : i = ℓ
      · subst hi; simp only [hidxOf, dif_pos rfl]
      · simp only [hidxOf, dif_neg hi]
        apply Fin.ext
        rw [Fin.val_cast]; exact (hall i hi).symm
    · push_neg at hall
      obtain ⟨i₀, hi₀ℓ, hi₀⟩ := hall
      apply Finset.prod_eq_zero (Finset.mem_univ i₀)
      simp only [hA, dif_neg hi₀ℓ]
      rw [if_neg]
      intro hc
      apply hi₀
      have := congrArg Fin.val hc
      rw [Fin.val_cast] at this
      exact this.symm
  -- Reindex: the full-index sum collapses to the `image idxOf` sum, then to `∑ j`.
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image idxOf))
        (fun idx _ hidx => by rw [hprod_zero idx hidx, zero_mul])]
  rw [Finset.sum_image (fun j _ j' _ h => hidxOf_inj h)]
  -- Now both sides are `∑ j`, with summand `u j * T (idxOf j)`.
  unfold sliceVec
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hprod_idxOf j]
  congr 1
  apply congrArg
  funext i
  by_cases hi : i = ℓ
  · subst hi
    change (if h : i = i then h ▸ j else _) = idxOf j i
    rw [dif_pos rfl]
    simp only [hidxOf, dif_pos rfl]
  · simp only [hidxOf, dif_neg hi]
    apply Fin.ext
    rw [Fin.val_cast, eqRec_eq_cast]
    exact Fin.val_eq_val_of_heq (cast_heq _ _)

/-- **`subrankPair` under a vector slice** (Briët et al. ITCS 2024, tex:951-955).
    `subrankPair (sliceVec T ℓ u) i j ≤ subrankPair T i j`: the vector slice is a
    restriction of `T` (`sliceVec_restricts`), and `subrankPair` is monotone under
    restriction (`subrankPair_mono_of_restricts`).  Analogue of
    `subrankPair_multiSliceL_le`. -/
lemma subrankPair_sliceVec_le {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (ℓ : Fin k) (u : Fin (d ℓ) → F) (i j : Fin k) :
    subrankPair (sliceVec T ℓ u) i j ≤ subrankPair T i j :=
  subrankPair_mono_of_restricts (sliceVec_restricts T ℓ u) i j

/-- **Multi-leg drop** (Briët et al. ITCS 2024, tex:884, all-at-once finset
    analogue of `dropLeg`).  Given a `k`-tensor `S` all of whose legs in `L` have
    dimension `1` (`hL : ∀ ℓ ∈ L, dS ℓ = 1`) and an enumeration `e : Fin n ≃
    {i // i ∉ L}` of the surviving legs, `dropLegs S L hL e` is the genuinely
    `n`-ary tensor obtained by deleting all `L`-legs (each carrying no
    information).  The dim-`1` `L`-coordinates are reinserted as `0`. -/
noncomputable def dropLegs {k n : ℕ} {dS : Fin k → ℕ+}
    (S : KTensor F dS) (L : Finset (Fin k)) (hL : ∀ ℓ ∈ L, dS ℓ = 1)
    (e : Fin n ≃ {i : Fin k // i ∉ L}) :
    KTensor F (fun a : Fin n => dS (e a).val) :=
  fun idx => S (fun i =>
    if h : i ∈ L then (hL i h ▸ (0 : Fin 1))
    else Fin.cast (by simp only [Equiv.apply_symm_apply]) (idx (e.symm ⟨i, h⟩)))

-- The dependent-`Fin` row/column equiv bookkeeping (`erowPi`, `ecol`) over the
-- heavy `Pi`-`Fintype` flattening index types needs a raised heartbeat budget.
set_option maxHeartbeats 1600000 in
-- Raised heartbeats: dropping dim-1 legs all-at-once unfolds nested product
-- equivalences whose elaboration exceeds the default budget.
/-- **Dropping the dim-`1` legs `L` preserves flattening rank** (Briët et al. ITCS
    2024, tex:884, 926, 953).  The all-at-once analogue of `flatRank_dropLeg`: for
    an index set `I` disjoint from `L` (`hIL : ∀ i ∈ I, i ∉ L`), the `I'`-flattening
    of `dropLegs S L hL e` (with `I' = e⁻¹ I`) has the same matrix rank as the
    `I`-flattening of `S`.  The `L`-legs are dim-`1`, so carry no column
    information; the two flattening matrices are reindexings of each other.

    This is the arity-reduction bridge taking `flatRank` of an ambient-`Fin k`
    multi-slice (`multiSliceL`, whose `L`-legs are dim `1`) to the genuinely smaller
    arity `n = k - |L|` at which the induction hypothesis is stated. -/
theorem flatRank_dropLegs {k n : ℕ} {dS : Fin k → ℕ+}
    (S : KTensor F dS) (L : Finset (Fin k)) (hL : ∀ ℓ ∈ L, dS ℓ = 1)
    (e : Fin n ≃ {i : Fin k // i ∉ L}) (I : Finset (Fin k)) (hIL : ∀ i ∈ I, i ∉ L) :
    flatRank (dropLegs S L hL e) (Finset.univ.filter (fun a => (e a).val ∈ I))
      = flatRank S I := by
  classical
  set I' : Finset (Fin n) := Finset.univ.filter (fun a => (e a).val ∈ I) with hI'def
  have hmemI' : ∀ a : Fin n, a ∈ I' ↔ (e a).val ∈ I := by intro a; simp [hI'def]
  -- For a surviving leg `i ∉ L`, `e (e.symm ⟨i,h⟩) = ⟨i,h⟩`.
  have hpre : ∀ (i : Fin k) (h : i ∉ L), (e (e.symm ⟨i, h⟩)).val = i := by
    intro i h; rw [Equiv.apply_symm_apply]
  have hval1 : ∀ (ℓ : Fin k) (hℓ : ℓ ∈ L) (x y : Fin (dS ℓ)), x = y := by
    intro ℓ hℓ x y; apply Fin.ext
    have : (dS ℓ : ℕ) = 1 := by rw [hL ℓ hℓ]; rfl
    omega
  -- Row equiv `{a // a ∈ I'} ≃ {i // i ∈ I}`.
  let erow : {a : Fin n // a ∈ I'} ≃ {i : Fin k // i ∈ I} :=
    { toFun := fun a => ⟨(e a.1).val, (hmemI' a.1).mp a.2⟩
      invFun := fun i => ⟨e.symm ⟨i.1, hIL i.1 i.2⟩,
        by rw [hmemI', hpre]; exact i.2⟩
      left_inv := fun a => by apply Subtype.ext; simp
      right_inv := fun i => by apply Subtype.ext; simp }
  let Zc : {i : Fin k // i ∈ I} → Type _ := fun i => Fin (dS i.val)
  let ec : ∀ a : {a : Fin n // a ∈ I'}, Fin (dS (e a.1).val) ≃ Zc (erow a) :=
    fun a => finCongr (by rfl)
  let erowPi : (∀ a : {a : Fin n // a ∈ I'}, Fin (dS (e a.1).val))
      ≃ (∀ i : {i : Fin k // i ∈ I}, Zc i) :=
    Equiv.piCongr erow ec
  have herowPi : ∀ (row : ∀ a : {a : Fin n // a ∈ I'}, Fin (dS (e a.1).val))
      (a : {a : Fin n // a ∈ I'}),
      ((erowPi row) (erow a)).val = (row a).val := by
    intro row a
    have h := Equiv.piCongr_apply_apply erow ec row a
    rw [show erowPi row = Equiv.piCongr erow ec row from rfl, h]; rfl
  -- Column equiv: fill the `L`-legs (dim 1) with `0`, reindex the rest by `e`.
  let ecol : (∀ a : {a : Fin n // a ∉ I'}, Fin (dS (e a.1).val))
      ≃ (∀ j : {j : Fin k // j ∉ I}, Fin (dS j.val)) :=
    { toFun := fun col' j =>
        if h : j.1 ∈ L then (hL j.1 h ▸ (0 : Fin 1))
        else Fin.cast (by rw [hpre j.1 h]) (col' ⟨e.symm ⟨j.1, h⟩,
          by rw [hmemI', hpre]; exact j.2⟩)
      invFun := fun col a => Fin.cast rfl (col ⟨(e a.1).val, by
        rw [← hmemI']; exact a.2⟩)
      left_inv := fun col' => by
        funext a
        have hnL : (e a.1).val ∉ L := (e a.1).2
        simp only [dif_neg hnL]
        apply Fin.ext; rw [Fin.val_cast, Fin.val_cast]
        exact dfun_val_congr col' (Subtype.ext (by simp [Equiv.symm_apply_apply]) :
          (⟨e.symm ⟨(e a.1).val, hnL⟩,
              by rw [hmemI', hpre]; exact fun hc => a.2 ((hmemI' a.1).mpr hc)⟩
            : {x : Fin n // x ∉ I'}) = a)
      right_inv := fun col => by
        funext j
        by_cases h : j.1 ∈ L
        · simp only [dif_pos h]; exact hval1 j.1 h _ _
        · simp only [dif_neg h]
          apply Fin.ext; rw [Fin.val_cast, Fin.val_cast]
          exact dfun_val_congr col (Subtype.ext (hpre j.1 h) :
            (⟨(e (e.symm ⟨j.1, h⟩)).val, by rw [hpre]; exact j.2⟩
              : {x : Fin k // x ∉ I}) = j) }
  have hecol_apply : ∀ (col : ∀ a : {a : Fin n // a ∉ I'}, Fin (dS (e a.1).val))
      (j : {j : Fin k // j ∉ I}) (h : j.1 ∉ L),
      (ecol col j).val = (col ⟨e.symm ⟨j.1, h⟩,
        by rw [hmemI', hpre]; exact j.2⟩).val := by
    intro col j h
    simp only [ecol, Equiv.coe_fn_mk]
    rw [dif_neg h, Fin.val_cast]
  have hfact : flattenMatrix (dropLegs S L hL e) I'
      = (flattenMatrix S I).submatrix (⇑erowPi) (⇑ecol) := by
    funext row col
    simp only [Matrix.submatrix_apply]
    change dropLegs S L hL e (fun a => if h : a ∈ I' then row ⟨a, h⟩ else col ⟨a, h⟩)
      = S (fun i => if h : i ∈ I then (erowPi row) ⟨i, h⟩ else (ecol col) ⟨i, h⟩)
    unfold dropLegs
    congr 1
    funext i
    by_cases hiL : i ∈ L
    · -- dropped leg: both sides land in `Fin (dS i) = Fin 1`.
      have hiI : i ∉ I := fun hc => hIL i hc hiL
      rw [dif_pos hiL]
      rw [dif_neg hiI]
      exact hval1 i hiL _ _
    · -- surviving leg `i ∉ L`.
      rw [dif_neg hiL]
      simp only []
      have hea : (e (e.symm ⟨i, hiL⟩)).val = i := hpre i hiL
      by_cases hiI : i ∈ I
      · rw [dif_pos (show e.symm ⟨i, hiL⟩ ∈ I' by rw [hmemI', hea]; exact hiI)]
        rw [dif_pos (show i ∈ I from hiI)]
        apply Fin.ext
        rw [Fin.val_cast]
        have := herowPi row ⟨e.symm ⟨i, hiL⟩, by rw [hmemI', hea]; exact hiI⟩
        rw [show (erow ⟨e.symm ⟨i, hiL⟩, by rw [hmemI', hea]; exact hiI⟩
              : {i // i ∈ I}) = ⟨i, hiI⟩ from Subtype.ext hea] at this
        exact this.symm
      · rw [dif_neg (show e.symm ⟨i, hiL⟩ ∉ I'
          by rw [hmemI', hea]; exact hiI)]
        rw [dif_neg (show i ∉ I from hiI)]
        apply Fin.ext
        rw [Fin.val_cast]
        rw [hecol_apply col ⟨i, hiI⟩ hiL]
  rw [flatRank, flatRank, hfact, Matrix.rank_submatrix]

omit [Field F] in
/-- Dependent matrix-entry congruence over a family `A : (i : ι) → Matrix (Fin (P i))
    (Fin (Q i)) F`: if `i₀ = i₁` and the row/column indices agree in value, the
    entries are equal.  Used to prove the `Fin.cast` bookkeeping when reindexing
    a Kronecker leg-matrix product along an `Equiv`. -/
private lemma matrix_entry_congr {ι : Type*} {P Q : ι → ℕ}
    (A : (i : ι) → Matrix (Fin (P i)) (Fin (Q i)) F)
    {i₀ i₁ : ι} (hi : i₀ = i₁)
    {x₀ : Fin (P i₀)} {x₁ : Fin (P i₁)} (hx : x₀.val = x₁.val)
    {y₀ : Fin (Q i₀)} {y₁ : Fin (Q i₁)} (hy : y₀.val = y₁.val) :
    A i₀ x₀ y₀ = A i₁ x₁ y₁ := by
  subst hi
  rw [Fin.ext hx, Fin.ext hy]

set_option maxHeartbeats 1600000 in
-- The cross-arity restriction lift inserts the dim-`1` `L`-legs and reindexes the
-- Kronecker contraction sum/product along `e`, a dependent-`Fin` bookkeeping that
-- needs a raised heartbeat budget.
/-- **Pair-subrank under `dropLegs` (Briët et al. ITCS 2024, Thm. 3.2,
    tex:925-945, eq:11a).**  Dropping the dimension-`1` legs `L` and relabeling the
    surviving legs by `e : Fin n ≃ {i // i ∉ L}` does not increase any pair-subrank:
    for surviving-leg indices `a b : Fin n`,
    `subrankPair (dropLegs S L hL e) a b ≤ subrankPair S (e a).val (e b).val`.

    Math content: a rank-`r` pair-unit `⟨r⟩_{a,b}` restricting to the arity-`n`
    tensor `dropLegs S L hL e` lifts to a rank-`r` pair-unit `⟨r⟩_{(e a),(e b)}`
    restricting to the arity-`k` tensor `S`, by inserting the dim-`1` `L`-legs (each
    carrying its unique value) with the `1 × 1` identity selector matrix.  Hence
    `S`'s pair-subrank supremum set contains `dropLegs S`'s, giving the inequality
    (the arity-reduction analogue of `subrankPair_multiSliceL_le`).

    This is the substrate the eq:(1) bound `hB1_block` consumes to transfer the
    induction-hypothesis subrank product (stated at the reduced arity `n = |I|+1`)
    back to the pair-subranks of the ambient tensor `T`. -/
theorem subrankPair_dropLegs {k n : ℕ} {dS : Fin k → ℕ+}
    (S : KTensor F dS) (L : Finset (Fin k)) (hL : ∀ ℓ ∈ L, dS ℓ = 1)
    (e : Fin n ≃ {i : Fin k // i ∉ L}) (a b : Fin n) :
    subrankPair (dropLegs S L hL e) a b ≤ subrankPair S (e a).val (e b).val := by
  classical
  -- Surviving legs are not in `L`.
  have haL : (e a).val ∉ L := (e a).2
  have hbL : (e b).val ∉ L := (e b).2
  -- `e` injective: `a = b ↔ (e a).val = (e b).val`.
  have hval1 : ∀ (ℓ : Fin k) (hℓ : ℓ ∈ L) (x y : Fin (dS ℓ)), x = y := by
    intro ℓ hℓ x y; apply Fin.ext
    have : (dS ℓ : ℕ) = 1 := by rw [hL ℓ hℓ]; rfl
    omega
  unfold subrankPair
  by_cases hab : a = b
  · simp [hab]
  · -- `(e a).val ≠ (e b).val`.
    have heab : (e a).val ≠ (e b).val := by
      intro h; exact hab (e.injective (Subtype.ext h))
    rw [dif_neg hab, dif_neg heab]
    set sLHS := { r : ℕ | ∃ hr : 0 < r,
      Restricts (unitPairTensor (F := F) ⟨r, hr⟩ a b hab) (dropLegs S L hL e) }
      with hsLHS
    set sRHS := { r : ℕ | ∃ hr : 0 < r,
      Restricts (unitPairTensor (F := F) ⟨r, hr⟩ (e a).val (e b).val heab) S }
      with hsRHS
    -- Subset: every LHS pair-unit restriction lifts to an RHS one.
    have hsub : sLHS ⊆ sRHS := by
      rintro r ⟨hr, A, hA⟩
      refine ⟨hr, ?_⟩
      -- Lift the arity-`n` restriction witness `A` to an arity-`k` witness `B`.
      -- Format equalities for the natural pair formats / dimensions.
      have hpre : ∀ (i : Fin k) (h : i ∉ L), (e (e.symm ⟨i, h⟩)).val = i := by
        intro i h; rw [Equiv.apply_symm_apply]
      -- For a surviving leg `i ∉ L`, the arity-`k` pair format at `i` equals the
      -- arity-`n` pair format at `e.symm i`.
      have hnpf_surv : ∀ (i : Fin k) (h : i ∉ L),
          naturalPairFormat (⟨r, hr⟩ : ℕ+) (e a).val (e b).val i
            = naturalPairFormat (⟨r, hr⟩ : ℕ+) a b (e.symm ⟨i, h⟩) := by
        intro i h
        simp only [naturalPairFormat]
        by_cases hia : e.symm ⟨i, h⟩ = a
        · have hib : i = (e a).val := by rw [← hia, hpre]
          simp [hib]
        · by_cases hib : e.symm ⟨i, h⟩ = b
          · have hieb : i = (e b).val := by rw [← hib, hpre]
            simp [hieb]
          · -- `i ≠ ea` and `i ≠ eb`.
            have hnea : i ≠ (e a).val := by
              intro h'; apply hia; apply e.injective; apply Subtype.ext
              rw [Equiv.apply_symm_apply]; exact h'
            have hneb : i ≠ (e b).val := by
              intro h'; apply hib; apply e.injective; apply Subtype.ext
              rw [Equiv.apply_symm_apply]; exact h'
            simp [hia, hib, hnea, hneb]
      -- For a dropped leg `i ∈ L`, the arity-`k` pair format at `i` is `1`.
      have hnpf_drop : ∀ (i : Fin k), i ∈ L →
          naturalPairFormat (⟨r, hr⟩ : ℕ+) (e a).val (e b).val i = (1 : ℕ+) := by
        intro i hiL
        simp only [naturalPairFormat]
        have hnea : i ≠ (e a).val := fun h => haL (h ▸ hiL)
        have hneb : i ≠ (e b).val := fun h => hbL (h ▸ hiL)
        simp [hnea, hneb]
      -- The lifted leg matrices `B`: identity `1×1` on dropped legs, the cast of
      -- `A (e.symm i)` on surviving legs.
      refine ⟨fun i => if hiL : i ∈ L then
          (fun _ _ => (1 : F))
        else
          (fun row col =>
            A (e.symm ⟨i, hiL⟩)
              (Fin.cast (congrArg (fun (m : ℕ+) => (m : ℕ)) (hnpf_surv i hiL)) row)
              (Fin.cast (congrArg (fun (x : Fin k) => (dS x : ℕ)) (hpre i hiL).symm) col)), ?_⟩
      intro jdx
      -- The reindexing equiv: arity-`n` column indices ↔ arity-`k` column indices
      -- (the `L`-legs are dim-`1`, hence determined).
      set Ψ : (∀ c : Fin n, Fin (dS (e c).val)) ≃ (∀ i : Fin k, Fin (dS i)) :=
        { toFun := fun idx i =>
            if h : i ∈ L then (hL i h ▸ (0 : Fin 1))
            else Fin.cast (congrArg (fun (x : Fin k) => (dS x : ℕ)) (hpre i h))
              (idx (e.symm ⟨i, h⟩))
          invFun := fun idx c => idx (e c).val
          left_inv := by
            intro idx; funext c
            have hnL : (e c).val ∉ L := (e c).2
            simp only [dif_neg hnL]
            have hsec : e.symm ⟨(e c).val, hnL⟩ = c := by
              rw [Subtype.coe_eta, Equiv.symm_apply_apply]
            apply Fin.ext
            rw [Fin.val_cast, hsec]
          right_inv := by
            intro idx; funext i
            by_cases h : i ∈ L
            · simp only [dif_pos h]; exact hval1 i h _ _
            · simp only [dif_neg h]
              apply Fin.ext
              rw [Fin.val_cast, hpre i h] } with hΨ
      -- `S ∘ Ψ = dropLegs S L hL e`.
      have hSΨ : ∀ idx : (∀ c : Fin n, Fin (dS (e c).val)),
          S (Ψ idx) = dropLegs S L hL e idx := by
        intro idx; unfold dropLegs; rfl
      -- The arity-`k` pair format at `(e c).val` matches the arity-`n` one at `c`.
      have hnpf_ec : ∀ c : Fin n,
          (naturalPairFormat (⟨r, hr⟩ : ℕ+) (e a).val (e b).val (e c).val : ℕ)
            = (naturalPairFormat (⟨r, hr⟩ : ℕ+) a b c : ℕ) := by
        intro c
        rw [hnpf_surv (e c).val (e c).2]
        congr 2
        rw [Subtype.coe_eta, Equiv.symm_apply_apply]
      -- Pull the arity-`k` row index `jdx` back to an arity-`n` row index `jdx'`.
      set jdx' : (∀ c : Fin n, Fin (naturalPairFormat (⟨r, hr⟩ : ℕ+) a b c)) :=
        fun c => Fin.cast (hnpf_ec c) (jdx (e c).val)
        with hjdx'
      -- Abbreviation for the lifted leg matrices `B`.
      set B : (i : Fin k) →
          Matrix (Fin (naturalPairFormat (⟨r, hr⟩ : ℕ+) (e a).val (e b).val i)) (Fin (dS i)) F :=
        fun i => if hiL : i ∈ L then (fun _ _ => (1 : F))
          else (fun row col => A (e.symm ⟨i, hiL⟩)
            (Fin.cast (congrArg (fun (m : ℕ+) => (m : ℕ)) (hnpf_surv i hiL)) row)
            (Fin.cast (congrArg (fun (x : Fin k) => (dS x : ℕ)) (hpre i hiL).symm) col))
        with hB
      -- Reindex `∑ idx` over `idx : ∀ i, Fin (dS i)` by `Ψ` (arity-`n` indices).
      rw [← Equiv.sum_comp Ψ
        (fun idx : (∀ i : Fin k, Fin (dS i)) => (∏ i, B i (jdx i) (idx i)) * S idx)]
      -- `hA` at `jdx'` rewrites the arity-`n` sum.
      have key : ∀ idxn : (∀ c : Fin n, Fin (dS (e c).val)),
          (∏ i, B i (jdx i) (Ψ idxn i)) * S (Ψ idxn)
            = (∏ c, A c (jdx' c) (idxn c)) * dropLegs S L hL e idxn := by
        intro idxn
        rw [hSΨ]
        congr 1
        -- Split the `Fin k` product into `∉ L` and `∈ L` factors.
        rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∉ L)
          (fun i => B i (jdx i) (Ψ idxn i))]
        -- The `∈ L` factor is `1`.
        rw [show (∏ i : {i // ¬ i ∉ L}, B i.val (jdx i.val) (Ψ idxn i.val)) = 1 from ?_, mul_one]
        · -- Reindex the `∉ L` product over `Fin n` via `e`.
          rw [← Equiv.prod_comp e (fun i : {i // i ∉ L} => B i.val (jdx i.val) (Ψ idxn i.val))]
          refine Finset.prod_congr rfl (fun c _ => ?_)
          -- `B (e c) (jdx (e c)) (Ψ idxn (e c)) = A c (jdx' c) (idxn c)`.
          have hnL : (e c).val ∉ L := (e c).2
          simp only [hB, dif_neg hnL]
          -- The `A`-index `e.symm ⟨(e c).val, hnL⟩` equals `c`; the row/col agree in
          -- value, so `matrix_entry_congr` closes the entry equality.
          have hce : e.symm ⟨(e c).val, hnL⟩ = c := by
            rw [Subtype.coe_eta, Equiv.symm_apply_apply]
          refine matrix_entry_congr A hce ?_ ?_
          · rw [hjdx', Fin.val_cast, Fin.val_cast]
          · rw [Fin.val_cast]
            simp only [hΨ, Equiv.coe_fn_mk, dif_neg hnL, Fin.val_cast]
            rw [hce]
        · -- The `L`-leg product is `1`.
          apply Finset.prod_eq_one
          intro c _
          have hcL : c.val ∈ L := not_not.mp c.2
          simp only [hB, dif_pos hcL]
      rw [Finset.sum_congr rfl (fun idxn _ => key idxn), ← hA jdx']
      -- Match the `if`-conditions of the two pair-unit tensors.
      unfold unitPairTensor
      have hrowa : (jdx' a).val = (jdx (e a).val).val := by
        rw [hjdx']; simp [Fin.val_cast]
      have hrowb : (jdx' b).val = (jdx (e b).val).val := by
        rw [hjdx']; simp [Fin.val_cast]
      rw [hrowa, hrowb]
    rcases Set.eq_empty_or_nonempty sLHS with hempty | hne
    · rw [hempty, show sSup (∅ : Set ℕ) = 0 from by simp]; exact Nat.zero_le _
    · exact csSup_le_csSup (subrankPair_bddAbove S (e a).val (e b).val heab) hne hsub

/-- **(B-prod), product factorization (Briët et al. ITCS 2024, Thm. 3.2,
    tex:906-929).**  For any complement leg `ℓ_last ∉ I` and `L = (univ \ I) \ {ℓ_last}`,
    the full pair-subrank product over `I ×ˢ (univ \ I)` factors as the last-leg
    product times the internal product:
    `(∏_{j∈I} subrank_{j,ℓ_last}) · (∏_{j∈I, ℓ∈L} subrank_{j,ℓ}) = ∏ pair-subranks`.

    This is the "leg-permutation / complement normalization" step of the paper,
    where the full product is split into the eq:(1) factor (legs `I` to the last
    leg) and the eq:(2) factor (legs `I` to the internal legs `L`). -/
private lemma subrankPair_prod_split {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (I : Finset (Fin k)) (ℓ_last : Fin k)
    (hℓ_last : ℓ_last ∉ I) :
    (∏ j ∈ I, subrankPair T j ℓ_last)
      * (∏ j ∈ I, ∏ ℓ ∈ ((Finset.univ \ I) \ {ℓ_last}), subrankPair T j ℓ)
    = ∏ p ∈ I ×ˢ (Finset.univ \ I), subrankPair T p.1 p.2 := by
  classical
  rw [Finset.prod_product]
  -- `univ \ I = insert ℓ_last L` with `L = (univ \ I) \ {ℓ_last}`, disjointly.
  have hmem : ℓ_last ∈ (Finset.univ \ I : Finset (Fin k)) := by
    simp [Finset.mem_sdiff, hℓ_last]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j hj => ?_)
  have := Finset.mul_prod_erase (Finset.univ \ I) (fun ℓ => subrankPair T j ℓ) hmem
  rw [Finset.erase_eq] at this
  exact this

/-! ## Complement / leg-swap symmetry substrate (tex:883).

The proof of Theorem 3.2 normalizes `I` so that `|I| ≤ ⌊k/2⌋` (tex:883:
"Since `tensorrank_I = tensorrank_{[k]\I}` we may assume `|I| ≤ ⌊k/2⌋`").  This
requires two symmetries: `flatRank` is complement-invariant (`flatRank_compl_eq`,
the matrix-transpose symmetry) and `subrankPair` is leg-swap-symmetric
(`subrankPair_comm`).  Together they give the product symmetry
`subrankPair_prod_compl_eq` used to transfer the theorem from `I` to `univ \ I`. -/

/-- **Complement-invariance of `flatRank`** (Briët et al. ITCS 2024, tex:844,889:
    "`tensorrank_I = tensorrank_{[k]\I}`").  The `(univ \ I)`-flattening of `T` is
    the transpose of the `I`-flattening up to the canonical reindexings
    `{i // i ∈ univ \ I} ≃ {j // j ∉ I}` and `{j // j ∉ univ \ I} ≃ {i // i ∈ I}`
    (entries are the *same* `T(combine)` since `i ∈ univ \ I ↔ i ∉ I`).  Hence the
    two flattening matrices have equal rank. -/
theorem flatRank_compl_eq {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (I : Finset (Fin k)) :
    flatRank T ((Finset.univ : Finset (Fin k)) \ I) = flatRank T I := by
  classical
  -- Reindex the rows / columns of `(flattenMatrix T I)ᵀ`.
  -- Rows of the transpose are `{j // j ∉ I}`; rows of the complement flattening
  -- are `{i // i ∈ univ \ I}`.  These are the same predicate (`i ∉ I`).
  let esubR : {i : Fin k // i ∈ (Finset.univ : Finset (Fin k)) \ I}
      ≃ {j : Fin k // j ∉ I} :=
    Equiv.subtypeEquivRight (fun x => by simp)
  let esubC : {j : Fin k // j ∉ (Finset.univ : Finset (Fin k)) \ I}
      ≃ {i : Fin k // i ∈ I} :=
    Equiv.subtypeEquivRight (fun x => by simp)
  -- Pi-type reindexings (dimensions agree since `subtypeEquivRight` preserves `.val`).
  let eRow := Equiv.piCongrLeft' (fun i : {i : Fin k // i ∈ (Finset.univ : Finset (Fin k)) \ I}
      => Fin ((d i.val : ℕ))) esubR
  let eCol := Equiv.piCongrLeft' (fun j : {j : Fin k // j ∉ (Finset.univ : Finset (Fin k)) \ I}
      => Fin ((d j.val : ℕ))) esubC
  -- The complement flattening is the reindexed transpose of the `I`-flattening.
  have hmat : flattenMatrix T ((Finset.univ : Finset (Fin k)) \ I)
      = Matrix.reindex eRow.symm eCol.symm (flattenMatrix T I).transpose := by
    funext row col
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.transpose_apply]
    change T (fun i => if h : i ∈ (Finset.univ : Finset (Fin k)) \ I then row ⟨i, h⟩
        else col ⟨i, h⟩)
      = T (fun i => if h : i ∈ I then (eCol col) ⟨i, h⟩ else (eRow row) ⟨i, h⟩)
    congr 1
    funext i
    by_cases hiI : i ∈ I
    · have hcompl : i ∉ (Finset.univ : Finset (Fin k)) \ I := by simp [hiI]
      rw [dif_neg hcompl, dif_pos hiI]
      rfl
    · have hcompl : i ∈ (Finset.univ : Finset (Fin k)) \ I := by simp [hiI]
      rw [dif_pos hcompl, dif_neg hiI]
      rfl
  rw [flatRank_eq_rank, flatRank_eq_rank, hmat, Matrix.rank_reindex,
    Matrix.rank_transpose]

/-- **`naturalPairFormat` is leg-swap symmetric** (tex:836): the pair-unit format
    `d_i = d_j = r`, other legs `1`, does not depend on the order of `i, j`. -/
lemma naturalPairFormat_comm {k : ℕ} (r : ℕ+) (i j : Fin k) :
    naturalPairFormat r i j = naturalPairFormat r j i := by
  funext ℓ
  unfold naturalPairFormat
  by_cases h : ℓ = i ∨ ℓ = j
  · rw [if_pos h, if_pos (Or.symm h)]
  · rw [if_neg h, if_neg (fun hc => h (Or.symm hc))]

/-- **`Restricts` transports along a format equality of the source tensor.**
    If `dS = dS'` then `S ≤ₜ T ↔ (hd ▸ S) ≤ₜ T`. -/
lemma Restricts.format_cast_iff {k : ℕ} {dS dS' dT : Fin k → ℕ+}
    (hd : dS = dS') {S : KTensor F dS} {T : KTensor F dT} :
    Restricts S T ↔ Restricts (hd ▸ S) T := by
  subst hd; exact Iff.rfl

/-- **`⟨r⟩_{i,j}` is leg-swap symmetric** (tex:836): `unitPairTensor r i j` and
    `unitPairTensor r j i` are literally the *same* tensor — same format
    (`naturalPairFormat_comm`) and same values (the entry `[(idx i).val = (idx j).val]`
    is symmetric in `i, j`).  We state the value equality after transporting along
    the format equality. -/
lemma unitPairTensor_comm {k : ℕ} (r : ℕ+) (i j : Fin k) (hij : i ≠ j) :
    (naturalPairFormat_comm r i j) ▸ (unitPairTensor (F := F) r i j hij)
      = unitPairTensor (F := F) r j i hij.symm := by
  classical
  -- Generalize the cast equality so we can reason about the transport pointwise.
  have key : ∀ (d' : Fin k → ℕ+) (hd : naturalPairFormat r i j = d'),
      hd ▸ (unitPairTensor (F := F) r i j hij)
        = fun idx => (unitPairTensor (F := F) r i j hij)
            (fun ℓ => (congrFun hd ℓ).symm ▸ idx ℓ) := by
    intro d' hd; subst hd; rfl
  rw [key (naturalPairFormat r j i) (naturalPairFormat_comm r i j)]
  funext idx
  simp only [unitPairTensor]
  -- The value `[(idx i).val = (idx j).val]` is symmetric.  The `▸`-cast on each
  -- coordinate preserves `.val` (it is a `Fin a = Fin b` re-cast).
  have hval : ∀ (ℓ : Fin k),
      (((congrFun (naturalPairFormat_comm r i j) ℓ).symm ▸ idx ℓ : _)).val
        = (idx ℓ).val := by
    intro ℓ
    rw [eqRec_eq_cast, ← Fin.cast_eq_cast (congrArg (fun m : ℕ+ => (m : ℕ))
      (congrFun (naturalPairFormat_comm r i j) ℓ).symm), Fin.val_cast]
  rw [hval i, hval j]
  by_cases h : (idx i).val = (idx j).val
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hc => h hc.symm)]

/-- **`subrankPair` is leg-swap symmetric** (tex:836): `subrankPair T i j =
    subrankPair T j i`.  Since `unitPairTensor r i j` and `unitPairTensor r j i`
    are the same tensor (`unitPairTensor_comm`), the two `Restricts`-sets defining
    the `sSup` coincide. -/
lemma subrankPair_comm {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (i j : Fin k) :
    subrankPair T i j = subrankPair T j i := by
  classical
  unfold subrankPair
  by_cases hij : i = j
  · subst hij; simp
  · rw [dif_neg hij, dif_neg (Ne.symm hij)]
    congr 1
    ext r
    constructor
    · rintro ⟨hr, hres⟩
      refine ⟨hr, ?_⟩
      rw [← unitPairTensor_comm (F := F) ⟨r, hr⟩ i j hij]
      exact (Restricts.format_cast_iff (naturalPairFormat_comm (⟨r, hr⟩ : ℕ+) i j)).mp hres
    · rintro ⟨hr, hres⟩
      refine ⟨hr, ?_⟩
      rw [← unitPairTensor_comm (F := F) ⟨r, hr⟩ i j hij] at hres
      exact (Restricts.format_cast_iff (naturalPairFormat_comm (⟨r, hr⟩ : ℕ+) i j)).mpr hres

/-- **Complement-symmetry of the full pair-subrank product** (tex:883).  The full
    product `∏_{i∈I, j∈[k]\I} subrank_{i,j}(T)` defining the right-hand side of
    Theorem 3.2 is invariant under replacing `I` by its complement.  Indeed
    `univ \ (univ \ I) = I`, and swapping the two product factors and applying
    `subrankPair_comm` turns the `(univ\I)`-product into the `I`-product.

    This is the right-hand-side half of the tex:883 normalization
    "`tensorrank_I = tensorrank_{[k]\I}` so we may assume `|I| ≤ ⌊k/2⌋`"; the
    left-hand-side half is `flatRank_compl_eq`. -/
theorem subrankPair_prod_compl_eq {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (I : Finset (Fin k)) :
    ∏ p ∈ ((Finset.univ : Finset (Fin k)) \ I) ×ˢ
        ((Finset.univ : Finset (Fin k)) \ ((Finset.univ : Finset (Fin k)) \ I)),
        subrankPair T p.1 p.2
      = ∏ p ∈ I ×ˢ ((Finset.univ : Finset (Fin k)) \ I), subrankPair T p.1 p.2 := by
  classical
  have hcc : (Finset.univ : Finset (Fin k)) \ ((Finset.univ : Finset (Fin k)) \ I) = I := by
    simp
  rw [hcc, Finset.prod_product, Finset.prod_product_right]
  refine Finset.prod_congr rfl (fun j hj => ?_)
  refine Finset.prod_congr rfl (fun i hi => ?_)
  exact subrankPair_comm T j i

/-! ## Theorem 3.2 (tex:840-845): the `Q_{i,j}` bound. -/

/-- **Theorem 3.2** (tex:840-845, `\label{th:Qij}`).

For a `k`-tensor `T` and `I ⊆ [k]` with `1 ≤ |I| ≤ k-1`,
if `|F| > flatRank_I(T)` then

  `∏_{i ∈ I, j ∈ [k]\\I} subrankPair T i j ≥ flatRank_I(T)`. -/
theorem subrankPair_prod_ge_flatRank
    {k : ℕ} {d : Fin k → ℕ+} (T : KTensor F d) (I : Finset (Fin k))
    (hI : 1 ≤ I.card) (hI' : I.card ≤ k - 1)
    (hF : ((flatRank T I : ℕ) : Cardinal) < Cardinal.mk F) :
    flatRank T I ≤
      ∏ p ∈ I ×ˢ ((Finset.univ : Finset (Fin k)) \ I),
        subrankPair T p.1 p.2 := by
  classical
  /- **Strong induction on the order `k` (paper tex:882).**
     "The proof is by induction on the order `k`. ... We now assume that the
     claim holds for the cases `2, …, k-1` and prove it for `k`."

     We expose the induction hypothesis `IH` for all smaller arities `m < k`
     (over arbitrary format `d'`, tensor `T'`, and index set `I'`) by reverting
     the data and running `Nat.strong_induction_on` on `k`. -/
  revert d T I
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro d T
  -- `IH : ∀ m < k, ∀ {d'} (T' : KTensor F d') (I' : Finset (Fin m)),
  --        1 ≤ I'.card → I'.card ≤ m - 1 →
  --        (flatRank T' I' : Cardinal) < #F →
  --        flatRank T' I' ≤ ∏ p ∈ I' ×ˢ (univ \ I'), subrankPair T' p.1 p.2`
  /- **Complement / leg normalization (paper tex:883).**  The block recursion
     applies `IH` to the `(|I|+1)`-tensor `P^{(L)}_i T`, which requires arity
     `|I|+1 < k`, i.e. `I.card ≤ k - 2`.  The theorem hypothesis only gives
     `I.card ≤ k - 1`.  Following tex:883 ("Since `tensorrank_I = tensorrank_{[k]\I}`
     we may assume `|I| ≤ ⌊k/2⌋`"), we prove the *main claim* under the stronger
     `I.card ≤ k - 2`, then transfer the boundary case `I.card = k - 1` to its
     complement `J = univ \ I` (with `J.card = 1 ≤ k - 2` when `k ≥ 3`) via the
     symmetry lemmas `flatRank_compl_eq` and `subrankPair_prod_compl_eq`. -/
  suffices main : ∀ (I : Finset (Fin k)), 1 ≤ I.card → I.card ≤ k - 2 →
      ((flatRank T I : ℕ) : Cardinal) < Cardinal.mk F →
      flatRank T I ≤
        ∏ p ∈ I ×ˢ ((Finset.univ : Finset (Fin k)) \ I), subrankPair T p.1 p.2 by
    intro I hI hI' hF
    -- Base case `k = 2`: handled directly (here `I.card = 1 = k - 1`).
    by_cases hk_two : k = 2
    · subst hk_two
      have hcard : I.card = 1 := le_antisymm (by simpa using hI') hI
      obtain ⟨i, hI_eq⟩ := Finset.card_eq_one.mp hcard
      subst I
      fin_cases i
      · change flatRank T {0} ≤
          ∏ p ∈ ({0} : Finset (Fin 2)) ×ˢ ((Finset.univ : Finset (Fin 2)) \ {0}),
            subrankPair T p.1 p.2
        have hcompl : ((Finset.univ : Finset (Fin 2)) \ {0}) = {1} := by
          ext x; fin_cases x <;> simp
        rw [Finset.prod_product, Finset.prod_singleton,
          show (∏ x ∈ (Finset.univ : Finset (Fin 2)) \ {0}, subrankPair T 0 x)
            = subrankPair T 0 1 from by rw [hcompl]; simp]
        exact subrankPair_ge_flatRank_k2_singleton T 0 1 (by decide)
      · change flatRank T {1} ≤
          ∏ p ∈ ({1} : Finset (Fin 2)) ×ˢ ((Finset.univ : Finset (Fin 2)) \ {1}),
            subrankPair T p.1 p.2
        have hcompl : ((Finset.univ : Finset (Fin 2)) \ {1}) = {0} := by
          ext x; fin_cases x <;> simp
        rw [Finset.prod_product, Finset.prod_singleton,
          show (∏ x ∈ (Finset.univ : Finset (Fin 2)) \ {1}, subrankPair T 1 x)
            = subrankPair T 1 0 from by rw [hcompl]; simp]
        exact subrankPair_ge_flatRank_k2_singleton T 1 0 (by decide)
    · -- `k ≥ 3` (since `k ≠ 2` and `k ≥ I.card + 1 ≥ 2`).
      by_cases hsmall : I.card ≤ k - 2
      · exact main I hI hsmall hF
      · -- `I.card = k - 1`; transfer to the complement `J = univ \ I`.
        push_neg at hsmall
        have hk_ge_three : 3 ≤ k := by
          rcases Nat.lt_or_ge k 3 with h | h
          · interval_cases k <;> omega
          · exact h
        have hIcard : I.card = k - 1 := le_antisymm hI' (by omega)
        set J : Finset (Fin k) := (Finset.univ : Finset (Fin k)) \ I with hJ_def
        have hJcard : J.card = 1 := by
          rw [hJ_def, Finset.card_sdiff_of_subset (Finset.subset_univ I),
            Finset.card_univ, Fintype.card_fin, hIcard]
          omega
        have hJ1 : 1 ≤ J.card := by rw [hJcard]
        have hJsmall : J.card ≤ k - 2 := by rw [hJcard]; omega
        have hFJ : ((flatRank T J : ℕ) : Cardinal) < Cardinal.mk F := by
          rw [hJ_def, flatRank_compl_eq]; exact hF
        have hmain := main J hJ1 hJsmall hFJ
        -- `hmain : flatRank T J ≤ ∏ p ∈ J ×ˢ (univ \ J), subrankPair T p.1 p.2`.
        -- Transfer LHS via `flatRank_compl_eq` (`flatRank T J = flatRank T I`) and
        -- RHS via `subrankPair_prod_compl_eq` (product over `J` = product over `I`).
        rw [hJ_def, flatRank_compl_eq, subrankPair_prod_compl_eq T I] at hmain
        exact hmain
  intro I hI hI' hF
  let P : ℕ :=
    ∏ p ∈ I ×ˢ ((Finset.univ : Finset (Fin k)) \ I),
      subrankPair T p.1 p.2
  /- **Briët et al. ITCS 2024, Thm. 3.2 (paper tex:920-970).**

     Remaining formal bridge, scoped to the exact combined witness package
     used below:

     * normalize `I` by complementing/permuting legs so
       `I = {0, …, m-1}` and the complement is `L ∪ {k-1}`;
     * define `P_last = ∏ i ∈ I, subrankPair T i (k-1)` and
       `P_internal = ∏ i ∈ I, ℓ ∈ L, subrankPair T i ℓ`, whose product embeds
       in the full product `P`;
     * form the block matrices `M_i`, greedy increments `r_i`,
       `rMax = max_i r_i`, and `support = #{i | r_i ≠ 0}`;
     * prove the rank decomposition bound, eq. (1) `rMax ≤ P_last`, and
       eq. (2) `support ≤ P_internal` using the flush lemma and the induction
       hypothesis.

     The witnesses must be produced together: the earlier stand-ins
     `P_last = 1`, `P_internal = P` do not suffice, because eq. (1) would then
     demand `rMax ≤ 1` from no hypothesis controlling the largest rank
     increment. -/
  have paper_tex_920_970_witness_package :
      I.card ≤ k - 2 → ∃ P_last P_internal rMax support : ℕ,
        P_last * P_internal ≤ P ∧
        flatRank T I ≤ rMax * support ∧
        rMax ≤ P_last ∧ support ≤ P_internal := by
    intro hI_small
    /- Paper tex:884-964 supplies the intended witnesses after normalizing
       `I = {0, ..., m-1}` and writing the complement as `L ∪ {k}`:

       * tex:887-893 decomposes `T_I` into blocks `M_i` and defines the rank
         increments `r_i`, with `flatRank_I(T) = ∑ i, r_i`;
       * tex:900-906 names the two bounds
           `∏_{j ∈ I} subrank_{j,k}(T) ≥ max_i r_i`
         and
           `∏_{j ∈ I, ℓ ∈ L} subrank_{j,ℓ}(T) ≥ |{i : r_i ≠ 0}|`;
       * tex:908-914 multiplies these inequalities and uses
           `∑ i, r_i ≤ max_i r_i * |{i : r_i ≠ 0}|`;
       * tex:917-940 proves the first bound by applying the induction
         hypothesis to the `L`-slices `P_i^(L) T`;
       * tex:942-963 proves the second bound by column-flushing the `M_i`
         blocks and applying the induction hypothesis to the first `k`-slice.

       Thus the mathematically correct package is
         `P_last    = ∏_{j ∈ I} subrankPair T j (last leg)`,
         `P_internal = ∏_{j ∈ I, ℓ ∈ L} subrankPair T j ℓ`,
         `rMax      = max_i r_i`,
         `support   = |{i : r_i ≠ 0}|`.

       Formalizing those witnesses here still requires the leg-permutation /
       complement normalization, the block and slice tensors, subrank
       monotonicity under taking slices, and the recursive induction hypothesis.
       Degenerate choices such as `rMax = flatRank T I`, `support = 1` would
       require `flatRank T I ≤ P`, which is exactly the theorem being proved. -/
    /- **Recursive data of the `k ≠ 2` step (Briët et al. ITCS 2024, Thm. 3.2,
       tex:893-969).**  The block decomposition supplies, for some block count
       `c` and block matrices `M : Fin c → Matrix _ _ F` realizing the
       `I`-flattening (`flatRank T I = (concatBlocks M).rank`, tex:887-893):

       * `P_last = ∏_{j ∈ I} subrankPair T j (last leg)`,
       * `P_internal = ∏_{j ∈ I, ℓ ∈ L} subrankPair T j ℓ`,

       together with the two genuinely recursive bounds and the product bound:

       * **(B1)** `univ.sup (rankIncrement M) ≤ P_last`   (tex:917-940, the
         last-leg subrank bound, proved by the induction hypothesis on the
         `L`-slices `P_i^(L) T`);
       * **(B2)** `#{i : rankIncrement M i ≠ 0} ≤ P_internal`   (tex:942-963,
         the flush-support bound, proved by `flush_lemma` on the `M_i` plus the
         induction hypothesis on the first `k`-slice);
       * **(B-prod)** `P_last * P_internal ≤ P`   (tex:900-923, the
         leg-permutation / complement normalization that embeds the two partial
         products into the full pair-subrank product `P`).

       **Available substrate (this file):**
       * the strong-induction hypothesis `IH : ∀ m < k, …` is now in scope (the
         enclosing theorem runs `Nat.strong_induction_on` on the order `k`,
         paper tex:882);
       * `sliceLeg T ℓ v` (tex:868-878) is the `ℓ`-slice fixing leg `ℓ` to `v`;
       * `flatRank_sliceLeg_le` proves the slice-monotonicity fact
         `flatRank (sliceLeg T ℓ v) I ≤ flatRank T I` (a slice flattening is a
         column-submatrix of `T_I`) used in both (B1) (tex:920-921) and (B2)
         (tex:947-949); `flattenMatrix_rank_submatrix_le` is its matrix-level core;
       * `concatBlocks_rank_le_maxIncrement_mul_support` (tex:908-914) and
         `flush_lemma` (tex:858-866) are closed.

       **Witness assembly.**  Concretely:
       (i) realize `flattenMatrix T I` as `concatBlocks M` up to a column-block
       reindex (`b = n_k`, `c = ∏_{m<j<k} n_j`), giving `hflat`;
       (ii) identify each block `M_i` with the `k`-flattening of the `L`-slice and
       the first columns with the `L`-flattening of the first `k`-slice, then apply
       `IH` (at arities `m+1` and `k-1`) through the column-submatrix bridge to get
       (B1)/(B2); (iii) the leg-permutation/complement normalization for (B-prod).
       The blocking sub-tasks are: the `(∀ j∉I, Fin(d j)) ≃ Fin c × Fin b` column
       reindex (dependent-`Fin` equiv), the `sliceLeg`→column-submatrix
       factorization (transport along `Function.update_of_ne`), and subrank
       monotonicity under slicing (`subrankPair (sliceLeg …) ≤ subrankPair …`). -/
    have recursive_block_data :
        ∃ (c a b : ℕ) (M : Fin c → Matrix (Fin a) (Fin b) F)
          (P_last P_internal : ℕ),
          flatRank T I = (concatBlocks M).rank ∧
          P_last * P_internal ≤ P ∧
          (Finset.univ.sup (rankIncrement M)) ≤ P_last ∧
          (Finset.univ.filter (fun i => rankIncrement M i ≠ 0)).card ≤
            P_internal := by
      classical
      -- The complement `univ \ I` is nonempty (since `|I| ≤ k-1 < k`), so we can
      -- single out a "last" complement leg `ℓ_last` and set `L = (univ\I)\{ℓ_last}`.
      have hcompl_ne : (Finset.univ \ I : Finset (Fin k)).Nonempty := by
        rw [← Finset.card_pos, Finset.card_sdiff_of_subset (Finset.subset_univ I),
          Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨ℓ_last, hℓ_last_mem⟩ := hcompl_ne
      have hℓ_last : ℓ_last ∉ I := (Finset.mem_sdiff.mp hℓ_last_mem).2
      set L : Finset (Fin k) := (Finset.univ \ I) \ {ℓ_last} with hL_def
      -- Row / column index types of the `I`-flattening.
      set Rows := (∀ i : {i : Fin k // i ∈ I}, Fin ((d i.val : ℕ))) with hRows
      set Cols := (∀ j : {j : Fin k // j ∉ I}, Fin ((d j.val : ℕ))) with hCols
      -- Column split: separate the `ℓ_last` leg from the internal legs `L`.
      -- Predicate on complement legs: "is an internal leg" (`≠ ℓ_last`).
      let q : {j : Fin k // j ∉ I} → Prop := fun j => (j : Fin k) ≠ ℓ_last
      -- `Cols ≃ (∀ internal legs, Fin d) × (∀ {ℓ_last}, Fin d)`.
      let esplit := Equiv.piEquivPiSubtypeProd q (fun j => Fin ((d j.val : ℕ)))
      -- The "internal" index type, and the "last leg" index type.
      let Internal := (∀ j : {j : {j : Fin k // j ∉ I} // q j}, Fin ((d j.val.val : ℕ)))
      -- The unique element of the `{ℓ_last}`-factor index.
      have hℓ_last_q : ¬ q (⟨ℓ_last, hℓ_last⟩ : {j : Fin k // j ∉ I}) := by
        simp [q]
      let elastNm :
          {j : {j : Fin k // j ∉ I} // ¬ q j} ≃ PUnit.{u + 1} := by
        refine ⟨fun _ => PUnit.unit,
          fun _ => ⟨⟨ℓ_last, hℓ_last⟩, hℓ_last_q⟩, ?_, ?_⟩
        · rintro ⟨⟨x, hx⟩, hx2⟩
          simp only [q, not_not] at hx2
          subst hx2; rfl
        · rintro ⟨⟩; rfl
      -- `{ℓ_last}`-factor is a one-element pi, equiv to `Fin (d ℓ_last)`.
      let elast :
          (∀ j : {j : {j : Fin k // j ∉ I} // ¬ q j}, Fin ((d j.val.val : ℕ)))
            ≃ Fin ((d ℓ_last : ℕ)) :=
        (Equiv.piCongrLeft' (fun j => Fin ((d j.val.val : ℕ))) elastNm).trans
          (Equiv.piUnique _)
      -- Full column split `Cols ≃ Internal × Fin (d ℓ_last)`.
      let ecolSplit : Cols ≃ Internal × Fin ((d ℓ_last : ℕ)) :=
        esplit.trans ((Equiv.refl Internal).prodCongr elast)
      -- Numeric block / row / width counts.
      let c : ℕ := Fintype.card Internal
      let b : ℕ := (d ℓ_last : ℕ)
      let a : ℕ := Fintype.card Rows
      -- Column reindex `Fin c × Fin b ≃ Cols`.
      let colEquiv : Fin c × Fin b ≃ Cols :=
        ((Fintype.equivFin Internal).symm.prodCongr (Equiv.refl (Fin b))).trans
          ecolSplit.symm
      -- Row reindex `Fin a ≃ Rows`.
      let rowEquiv : Fin a ≃ Rows := (Fintype.equivFin Rows).symm
      -- The block matrices: `M i` is the `i`th column-block of the flattening.
      let M : Fin c → Matrix (Fin a) (Fin b) F :=
        fun i row col => flattenMatrix T I (rowEquiv row) (colEquiv (i, col))
      -- `concatBlocks M` is exactly the reindexed `I`-flattening, so equal rank.
      have hflat : flatRank T I = (concatBlocks M).rank := by
        have hsub : concatBlocks M
            = (flattenMatrix T I).submatrix rowEquiv colEquiv := by
          funext row p
          rfl
        rw [flatRank_eq_rank, hsub, Matrix.rank_submatrix]
      -- The two product witnesses (eq:1 factor and eq:2 factor).
      set P_last : ℕ := ∏ j ∈ I, subrankPair T j ℓ_last with hPlast_def
      set P_internal : ℕ := ∏ j ∈ I, ∏ ℓ ∈ L, subrankPair T j ℓ with hPint_def
      -- (B-prod): the product of the two witnesses embeds in the full product `P`.
      have hprod : P_last * P_internal ≤ P := by
        rw [hPlast_def, hPint_def, hL_def]
        exact (subrankPair_prod_split T I ℓ_last hℓ_last).le
      /- **(B1)+(B2), the two recursive bounds (Briët et al. ITCS 2024, Thm. 3.2).**

         * **(B1)** `univ.sup (rankIncrement M) ≤ P_last = ∏_{j∈I} subrank_{j,ℓ_last}(T)`
           (paper tex:917-940):  block `M i` is the `ℓ_last`-flattening of the
           `L`-slice `P^{(L)}_i T`, an `(|I|+1)`-tensor; `r_i ≤ rank(M_i)`; the
           induction hypothesis at arity `|I|+1 < k` with index set `I` and
           complement `{ℓ_last}` gives
           `rank(M_i) ≤ ∏_{j∈I} subrank_{j,ℓ_last}(P^{(L)}_i T)`, and subrank can
           only shrink under slicing, so `≤ ∏_{j∈I} subrank_{j,ℓ_last}(T) = P_last`.

         * **(B2)** `#{i : rankIncrement M i ≠ 0} ≤ P_internal = ∏_{j∈I,ℓ∈L} subrank_{j,ℓ}(T)`
           (paper tex:942-963):  by `flush_lemma` we may assume `T` column-flushed,
           so `M' =` `L`-flattening of the first `k`-slice `P^{(k)}_1 T` (a
           `(k-1)`-tensor) has `rank(M') ≥ #{i : r_i ≠ 0}`; the induction
           hypothesis at arity `k-1` with index set `I` and complement `L` gives
           `rank(M') ≤ ∏_{j∈I,ℓ∈L} subrank_{j,ℓ}(P^{(k)}_1 T) ≤ P_internal`.

         **Mathematical ingredients:**
         (i) *arity-reduction bridge* — `dropLeg` +
         `flatRank_dropLeg` (tex:878, 920, 947): `sliceLeg` keeps the `Fin k` arity
         (it only sets a leg's dimension to `1`), but `IH` is stated at a strictly
         smaller arity `Fin m`, `m < k`.  `flatRank_dropLeg` transports `flatRank`
         of a `Fin (n+1)`-tensor with a dimension-`1` complement leg to the genuine
         `Fin n`-arity tensor `dropLeg`.
         (ii) *subrank-under-slicing monotonicity* —
         `subrankPair_sliceLeg_le` (tex:917-963): the slice is a restriction of `T`
         (`sliceLeg_restricts`), and `subrankPair` is monotone under restriction
         (`subrankPair_mono_of_restricts`), which rests on the general-arity
         `BddAbove` of the `subrankPair` supremum set (`subrankPair_bddAbove`, via
         `pairUnit_restricts_le_flatRank` + `Restricts.flatRank_le`).
         (iii) the *block ↔ slice-flattening identification*
         `(M i).rank = flatRank (iterated L-slice) I` and `M'`'s column
         description (first columns of the `M_i`); the single-leg core is
         `flatRank_sliceLeg_le`/`flattenMatrix_rank_submatrix_le`; the
         multi-leg `L`-slice iteration goes through the `colEquiv`/`ecolSplit`
         block reindex, iterating `dropLeg` over the `|L|` internal legs to land
         at arity `|I|+1` (B1) / `k-1` (B2), and then invokes `IH`. -/
      /- **(B1) per-block recursive bound** (Briët et al. ITCS 2024, Thm. 3.2,
         tex:937-945, `\label{eq:11a}`).  The block `M i` is the `k`-flattening of
         the `i`th `L`-slice `P_i^{(L)} T`, an `(m+1)`-tensor (legs `I ∪ {ℓ_last}`,
         all `L`-legs fixed to the multi-index `i`).  Since `m+1 = |I|+1 < k` and
         `[k]\\L = {ℓ_last}`, the induction hypothesis `IH` applied to `P_i^{(L)} T`
         gives
         `(M i).rank = flatRank_{ℓ_last}(P_i^{(L)} T)`
         `  ≤ ∏_{j∈I} subrank_{j,ℓ_last}(P_i^{(L)} T)`,
         and `subrankPair_sliceLeg_le` (slicing only shrinks subrank) bounds this by
         `∏_{j∈I} subrank_{j,ℓ_last}(T) = P_last`.

         **Multi-leg block identification:** the `L`-slice ↔ block-`M i`
         identification through the `colEquiv`/`ecolSplit` block reindex, then the
         `dropLeg`-iterated arity reduction to `Fin (|I|+1)` and the `IH` call.
         Substrate: the block↔slice rank identity is
         `flatRank_multiSliceL_eq_colBlock` (tex:919-923, eq:11a): for `L` disjoint
         from `I`, `flattenMatrix (multiSliceL T L w) I` is a row-reindex of the
         column-block of `flattenMatrix T I` whose `L`-coordinates are `w`.  With
         `L = (univ\I)\{ℓ_last}` and `w_i` = the coordinates the multi-index `i`
         dictates, this gives `(M i).rank = flatRank (multiSliceL T L w_i) I` once
         the `colEquiv`/`ecolSplit` reindex is matched against `gcol`.  Remaining:
         (a) match the local `colEquiv`/`ecolSplit` block reindex to the lemma's
         `gcol`/`erow`; (b) `dropLeg`-iterate the `|L|` dimension-`1` legs of
         `multiSliceL T L w_i` (via `flatRank_dropLeg`, proved) to reach arity
         `|I|+1 < k`; (c) invoke `IH` and bound subrank back to `T` via
         `subrankPair_sliceLeg_le`. -/
      -- `L` is disjoint from `I` (it is a subset of `univ \ I`).
      have hLI : ∀ ℓ ∈ L, ℓ ∉ I := by
        intro ℓ hℓ
        rw [hL_def, Finset.mem_sdiff, Finset.mem_sdiff] at hℓ
        exact hℓ.1.2
      -- `L`-legs are not `ℓ_last`.
      have hLne : ∀ ℓ ∈ L, ℓ ≠ ℓ_last := by
        intro ℓ hℓ
        rw [hL_def, Finset.mem_sdiff, Finset.mem_singleton] at hℓ
        exact hℓ.2
      have hB1_block : ∀ i : Fin c, (M i).rank ≤ P_last := by
        intro i
        -- The internal multi-index named by `i`.
        set internalIdx : Internal := (Fintype.equivFin Internal).symm i with hint
        -- The `L`-slice values dictated by `internalIdx`.
        set w_i : ∀ ℓ : Fin k, ℓ ∈ L → Fin ((d ℓ : ℕ)) :=
          fun ℓ hℓ => internalIdx ⟨⟨ℓ, hLI ℓ hℓ⟩, hLne ℓ hℓ⟩ with hwi
        -- Multi-slice flattening format `d' j = if j ∈ L then 1 else d j`.
        set d' : Fin k → ℕ+ := fun j => if j ∈ L then (1 : ℕ+) else d j with hd'
        -- Step 1: `(M i).rank = flatRank (multiSliceL T L w_i) I`.
        -- Column equiv `Fin b ≃ {j ∉ I, Fin (d' j)}`: the `L`-legs are dim 1
        -- (forced to 0), the single surviving complement leg `ℓ_last` carries `col`.
        have hbcol : ∀ (j : {j : Fin k // j ∉ I}), j.val ∉ L → j.val = ℓ_last := by
          intro j hjL
          have hjcompl : j.val ∈ (Finset.univ \ I : Finset (Fin k)) := by
            simp [Finset.mem_sdiff, j.2]
          by_contra hne
          apply hjL
          rw [hL_def, Finset.mem_sdiff, Finset.mem_singleton]
          exact ⟨hjcompl, hne⟩
        -- Row format on `I` is unchanged (`I` disjoint from `L`).
        have hfmt_row : ∀ (ii : {ii : Fin k // ii ∈ I}),
            ((fun jj => if jj ∈ L then (1 : ℕ+) else d jj) ii.val : ℕ) = (d ii.val : ℕ) := by
          intro ii
          have : ii.val ∉ L := fun hc => hLI ii.val hc ii.2
          simp only [if_neg this]
        -- Column format of a non-`L` complement leg agrees with `b = d ℓ_last`.
        have hfmt_last : ∀ (j : {j : Fin k // j ∉ I}) (h : j.val ∉ L),
            ((fun jj => if jj ∈ L then (1 : ℕ+) else d jj) j.val : ℕ) = b := by
          intro j h
          simp only [if_neg h]
          rw [hbcol j h]
        -- Explicit value of `colEquiv (i, col)` at a complement leg.
        have hcolEquiv : ∀ (col : Fin b) (j : {j : Fin k // j ∉ I}),
            (colEquiv (i, col) j).val
              = if hq : (j.val ≠ ℓ_last) then (internalIdx ⟨j, hq⟩).val
                else col.val := by
          intro col j
          change (esplit.symm (internalIdx, elast.symm col) j).val = _
          rw [Equiv.piEquivPiSubtypeProd_symm_apply]
          by_cases hq : (j.val ≠ ℓ_last)
          · rw [dif_pos hq, dif_pos hq]
          · rw [dif_neg hq, dif_neg hq]
            -- `j = ℓ_last`; `elast.symm col` at this index is `col` (cast).
            change ((elast.symm col) ⟨j, hq⟩).val = col.val
            simp only [elast, Equiv.symm_trans_apply, Equiv.piCongrLeft'_symm_apply]
            -- The remaining `eqRec`/`piUnique.symm` reduces to `col` (same `.val`).
            apply Fin.val_eq_val_of_heq
            exact eqRec_heq_self _ _
        -- Row equiv `Rows ≃ {ii ∈ I, Fin (d' ii)}`.
        let rEq : Rows ≃ (∀ ii : {ii : Fin k // ii ∈ I},
            Fin ((fun jj => if jj ∈ L then (1 : ℕ+) else d jj) ii.val)) :=
          Equiv.piCongrRight (fun ii => finCongr (hfmt_row ii).symm)
        -- Column equiv `Fin b ≃ {j ∉ I, Fin (d' j)}` (`L`-legs dim 1, `ℓ_last` carries `col`).
        let cEq : Fin b ≃ (∀ j : {j : Fin k // j ∉ I},
            Fin ((fun jj => if jj ∈ L then (1 : ℕ+) else d jj) j.val)) :=
          { toFun := fun col j =>
              if h : j.val ∈ L then
                (by simp only [if_pos h]; exact (0 : Fin 1))
              else Fin.cast (hfmt_last j h).symm col
            invFun := fun col' =>
              Fin.cast (hfmt_last ⟨ℓ_last, hℓ_last⟩ (by simp [hL_def]))
                (col' ⟨ℓ_last, hℓ_last⟩)
            left_inv := by
              intro col
              have hℓL : ℓ_last ∉ L := by simp [hL_def]
              apply Fin.ext
              simp only [dif_neg hℓL, Fin.val_cast]
            right_inv := by
              intro col'
              funext j
              by_cases h : j.val ∈ L
              · simp only [dif_pos h]
                have hcard : ((fun jj => if jj ∈ L then (1 : ℕ+) else d jj) j.val : ℕ) = 1 := by
                  simp only [if_pos h]; rfl
                have : Subsingleton
                    (Fin ((fun jj => if jj ∈ L then (1 : ℕ+) else d jj) j.val)) := by
                  rw [hcard]; infer_instance
                exact this.elim _ _
              · simp only [dif_neg h]
                have hjeq : j = ⟨ℓ_last, hℓ_last⟩ := Subtype.ext (hbcol j h)
                apply Fin.ext
                rw [Fin.val_cast, Fin.val_cast, hjeq] }
        have key1 : (M i).rank = flatRank (multiSliceL T L w_i) I := by
          have hMfact : M i
              = (flattenMatrix (multiSliceL T L w_i) I).submatrix
                  (rowEquiv.trans rEq) cEq := by
            funext row col
            simp only [Matrix.submatrix_apply]
            change T (fun ℓ => if h : ℓ ∈ I then (rowEquiv row) ⟨ℓ, h⟩
                else colEquiv (i, col) ⟨ℓ, h⟩)
              = multiSliceL T L w_i (fun ℓ => if h : ℓ ∈ I
                  then (rEq (rowEquiv row)) ⟨ℓ, h⟩ else (cEq col) ⟨ℓ, h⟩)
            unfold multiSliceL
            congr 1
            funext ℓ
            by_cases hℓL : ℓ ∈ L
            · -- Internal leg `ℓ ∈ L`: RHS picks `w_i ℓ`; LHS is `colEquiv` at this leg.
              have hℓI : ℓ ∉ I := hLI ℓ hℓL
              rw [dif_neg hℓI, dif_pos hℓL]
              have hq : (⟨ℓ, hℓI⟩ : {j : Fin k // j ∉ I}).val ≠ ℓ_last := hLne ℓ hℓL
              apply Fin.ext
              rw [hcolEquiv col ⟨ℓ, hℓI⟩, dif_pos hq]
            · -- `ℓ ∉ L`: RHS is `eqRec (idx ℓ)` with `idx ℓ = if ℓ∈I then rEq.. else cEq..`.
              rw [dif_neg hℓL]
              apply Fin.ext
              -- Strip the `eqRec` cast on the RHS (preserves `.val`).
              rw [eqRec_eq_cast, Fin.val_eq_val_of_heq (cast_heq _ _)]
              simp only []
              by_cases hℓI : ℓ ∈ I
              · -- Row leg `ℓ ∈ I`.
                rw [dif_pos hℓI, dif_pos hℓI]
                change ((rowEquiv row) ⟨ℓ, hℓI⟩).val = ((rEq (rowEquiv row)) ⟨ℓ, hℓI⟩).val
                rw [Equiv.piCongrRight_apply]
                simp [finCongr_apply]
              · -- Last leg `ℓ = ℓ_last`.
                rw [dif_neg hℓI, dif_neg hℓI]
                have hq : ¬ (⟨ℓ, hℓI⟩ : {j : Fin k // j ∉ I}).val ≠ ℓ_last := by
                  simp only [not_not]; exact hbcol ⟨ℓ, hℓI⟩ hℓL
                rw [hcolEquiv col ⟨ℓ, hℓI⟩, dif_neg hq]
                change col.val = ((cEq col) ⟨ℓ, hℓI⟩).val
                simp only [cEq, Equiv.coe_fn_mk, dif_neg hℓL, Fin.val_cast]
          rw [hMfact, flatRank_eq_rank, Matrix.rank_submatrix]
        -- Step 2: reduce arity via `dropLegs`, apply `IH`, bound subrank back to `T`.
        rw [key1]
        -- `L`-legs of the multi-slice are dimension `1`.
        have hLone : ∀ ℓ ∈ L, (fun jj => if jj ∈ L then (1 : ℕ+) else d jj) ℓ = 1 := by
          intro ℓ hℓ; simp only [if_pos hℓ]
        -- The surviving legs `{i // i ∉ L}` have cardinality `n := I.card + 1`.
        set n : ℕ := I.card + 1 with hn
        have hLcard : L.card = k - I.card - 1 := by
          rw [hL_def, Finset.card_sdiff_of_subset, Finset.card_sdiff_of_subset
                (Finset.subset_univ I), Finset.card_univ, Fintype.card_fin]
          · simp [Finset.card_singleton]
          · intro x hx
            rw [Finset.mem_singleton] at hx; subst hx
            exact hℓ_last_mem
        have hcardnotL : Fintype.card {i : Fin k // i ∉ L} = n := by
          rw [Fintype.card_subtype_compl, Fintype.card_fin, hn,
            show Fintype.card {x : Fin k // x ∈ L} = L.card from Fintype.card_coe L, hLcard]
          have hIle : I.card ≤ k - 1 := by
            have := hI'; omega
          omega
        -- Enumerate the surviving legs.
        let e : Fin n ≃ {i : Fin k // i ∉ L} :=
          (Fintype.equivFinOfCardEq hcardnotL).symm
        set I'' : Finset (Fin n) := Finset.univ.filter (fun a => (e a).val ∈ I) with hI''
        -- `dropLegs` rank equals the multi-slice rank.
        have hIL : ∀ i ∈ I, i ∉ L := fun i hi hc => hLI i hc hi
        have hdrop := flatRank_dropLegs (multiSliceL T L w_i) L hLone e I hIL
        rw [← hdrop]
        set D := dropLegs (multiSliceL T L w_i) L hLone e with hD
        -- `e` restricts to a bijection `I'' ≃ I` on the `I`-legs.
        have heI : ∀ a : Fin n, a ∈ I'' ↔ (e a).val ∈ I := by
          intro a; simp [hI'']
        -- `I''.card = I.card`.
        have hI''card : I''.card = I.card := by
          rw [hI'']
          apply Finset.card_bij (fun a _ => (e a).val)
          · intro a ha; simp only [Finset.mem_filter] at ha; exact ha.2
          · intro a ha a' ha' heq
            exact e.injective (Subtype.ext heq)
          · intro j hj
            refine ⟨e.symm ⟨j, hIL j hj⟩, ?_, ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                Equiv.apply_symm_apply]; exact hj
            · simp [Equiv.apply_symm_apply]
        -- Side conditions for `IH`.
        have hI''pos : 1 ≤ I''.card := by rw [hI''card]; exact hI
        have hI''le : I''.card ≤ n - 1 := by rw [hI''card, hn]; omega
        have hDF : ((flatRank D I'' : ℕ) : Cardinal) < Cardinal.mk F := by
          have hle : flatRank D I'' ≤ flatRank T I := by
            rw [hI'', hD, hdrop]
            exact flatRank_multiSliceL_le T I L hLI w_i
          exact lt_of_le_of_lt (by exact_mod_cast hle) hF
        have hIHbound := IH n (by rw [hn]; omega) D I'' hI''pos hI''le hDF
        -- `IH` gives the product bound; now reindex it to `P_last`.
        refine hIHbound.trans ?_
        -- `ℓ_last ∉ L`.
        have hℓ_lastL : ℓ_last ∉ L := by simp [hL_def]
        -- The complement leg in arity `n` is the unique preimage of `ℓ_last`.
        set ℓpre : Fin n := e.symm ⟨ℓ_last, hℓ_lastL⟩ with hℓpre
        have hℓpre_e : (e ℓpre).val = ℓ_last := by
          rw [hℓpre, Equiv.apply_symm_apply]
        have hcompl : (Finset.univ \ I'' : Finset (Fin n)) = {ℓpre} := by
          ext a
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, heI, Finset.mem_singleton]
          constructor
          · intro haI
            -- `(e a).val ∉ I` and `(e a).val ∉ L` ⇒ `(e a).val = ℓ_last` ⇒ `a = ℓpre`.
            have hnL : (e a).val ∉ L := (e a).2
            have hval : (e a).val = ℓ_last := by
              by_contra hne
              apply hnL
              have hmemL : (e a).val ∈ (Finset.univ \ I) \ {ℓ_last} := by
                rw [Finset.mem_sdiff, Finset.mem_singleton]
                exact ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, haI⟩, hne⟩
              rwa [← hL_def] at hmemL
            have hae : e a = ⟨ℓ_last, hℓ_lastL⟩ := Subtype.ext hval
            rw [hℓpre, ← hae, Equiv.symm_apply_apply]
          · intro ha; subst ha
            rw [hℓpre_e]; exact hℓ_last
        -- Factor the product: complement is the singleton `{ℓpre}`.
        rw [Finset.prod_product, hcompl]
        simp only [Finset.prod_singleton]
        -- Reindex `∏ j'' ∈ I''` to `∏ j ∈ I` via `e`, bounding each factor.
        rw [hPlast_def]
        rw [show (∏ j ∈ I, subrankPair T j ℓ_last)
              = ∏ a ∈ I'', subrankPair T (e a).val ℓ_last from ?_]
        · refine Finset.prod_le_prod' (fun a ha => ?_)
          -- `subrankPair D a ℓpre ≤ subrankPair T (e a) ℓ_last`.
          calc subrankPair D a ℓpre
              ≤ subrankPair (multiSliceL T L w_i) (e a).val (e ℓpre).val :=
                subrankPair_dropLegs (multiSliceL T L w_i) L hLone e a ℓpre
            _ ≤ subrankPair T (e a).val (e ℓpre).val :=
                subrankPair_multiSliceL_le T L w_i (e a).val (e ℓpre).val
            _ = subrankPair T (e a).val ℓ_last := by rw [hℓpre_e]
        · -- `∏ j ∈ I = ∏ a ∈ I''` via the bijection `a ↦ (e a).val`.
          symm
          refine Finset.prod_bij (fun a _ => (e a).val) ?_ ?_ ?_ (fun a _ => rfl)
          · intro a ha; exact (heI a).mp ha
          · intro a ha a' ha' heq; exact e.injective (Subtype.ext heq)
          · intro j hj
            refine ⟨e.symm ⟨j, hIL j hj⟩, ?_, ?_⟩
            · rw [heI, Equiv.apply_symm_apply]; exact hj
            · simp [Equiv.apply_symm_apply]
      /- **(B2)** `#{i : rankIncrement M i ≠ 0} ≤ P_internal` (Briët et al. ITCS
         2024, Thm. 3.2, tex:948-969, `\label{eq:12a}`,`\label{eq:12b}`).  By
         `flush_lemma` we may assume `T` column-flushed, so the `L`-flattening `M'`
         of the first `k`-slice `P_1^{(k)} T` (a `(k-1)`-tensor) has columns equal
         to the first columns of each block `M i`, whence
         `#{i : r_i ≠ 0} ≤ M'.rank`.  Since `[k-1]\\I = L`, the induction hypothesis
         at arity `k-1` gives
         `M'.rank = flatRank_L(P_1^{(k)} T)`
         `  ≤ ∏_{j∈I,ℓ∈L} subrank_{j,ℓ}(P_1^{(k)} T) ≤ P_internal`.

         **Flush-support count:** the flush lemma
         (`flush_lemma` + first-column identification) and the multi-leg `L`-slice
         ↔ `M'` identification with the arity-`(k-1)` `IH` call.  For B2 the relevant
         slice is the first `ℓ_last`-slice `multiSliceL T {ℓ_last} w` (fixing only
         the last leg), whose I-flattening is identified with `M'` (columns = first
         columns of the `M_i`) by `flatRank_multiSliceL_eq_colBlock` with
         `L := {ℓ_last}`; then `dropLeg` drops the lone dim-`1` leg to reach
         arity `k-1` for the `IH` call, as in (B1). -/
      have hB2 : (Finset.univ.filter (fun i => rankIncrement M i ≠ 0)).card ≤
          P_internal := by
        have hb0 : 0 < b := (d ℓ_last).2
        /- **PART A (eq:12a, the IH side).**  For *any* fixed value `w0` of the
           single sliced leg `ℓ_last`, the `I`-flattening of the first-`ℓ_last`-slice
           `multiSliceL T {ℓ_last} w0` (a tensor whose `ℓ_last`-leg is dim `1`,
           i.e. the `(k-1)`-tensor `P^{(k)}_1 T`) has
           `flatRank (multiSliceL T {ℓ_last} w0) I ≤ P_internal`.
           Proved by the induction hypothesis at arity `k-1` with `[k-1]∖I = L`
           (paper tex:951-961, eq:12a), then bounding each subrank factor back to
           `T` via `subrankPair_dropLegs` + `subrankPair_multiSliceL_le`.  Mirrors
           `hB1_block` with the sliced leg set `{ℓ_last}` in place of `L`. -/
        /- **PART A, generalized.**  For *any* tensor `S` whose `ℓ_last`-leg is
           dim `1` (format `fun jj => if jj ∈ {ℓ_last} then 1 else d jj`), if
           `flatRank S I ≤ flatRank T I` and every pair-subrank of `S` is bounded
           by that of `T`, then `flatRank S I ≤ P_internal`.  The proof is the
           eq:12a induction-hypothesis argument: drop the dim-`1` `ℓ_last`-leg to
           reach arity `k-1`, apply `IH` with `[k-1]∖I = L`, and bound each subrank
           factor back to `T`.  This covers both the coordinate slice
           `multiSliceL T {ℓ_last} w0` (eq:12a) and the vector slice
           `sliceVec T ℓ_last u` (eq:12b, paper tex:955-957). -/
        have keyA_gen : ∀ (Ls : Finset (Fin k)) (hLs : Ls = {ℓ_last})
            (S : KTensor F (fun jj => if jj ∈ Ls then (1 : ℕ+) else d jj)),
            flatRank S I ≤ flatRank T I →
            (∀ i j, subrankPair S i j ≤ subrankPair T i j) →
            flatRank S I ≤ P_internal := by
          intro Ls hLs S hSflat hSsub
          -- `Ls` is disjoint from `I` (`ℓ_last ∉ I`).
          have hLsI : ∀ ℓ ∈ Ls, ℓ ∉ I := by
            intro ℓ hℓ; rw [hLs, Finset.mem_singleton] at hℓ; subst hℓ; exact hℓ_last
          -- `Ls`-legs of the slice are dimension `1`.
          have hLsone : ∀ ℓ ∈ Ls,
              (fun jj => if jj ∈ Ls then (1 : ℕ+) else d jj) ℓ = 1 := by
            intro ℓ hℓ; simp only [if_pos hℓ]
          -- The surviving legs `{i // i ∉ {ℓ_last}}` have cardinality `n' := k - 1`.
          set n' : ℕ := k - 1 with hn'
          have hcardnotLs : Fintype.card {i : Fin k // i ∉ Ls} = n' := by
            rw [Fintype.card_subtype_compl, Fintype.card_fin, hn',
              show Fintype.card {x : Fin k // x ∈ Ls} = Ls.card from Fintype.card_coe Ls,
              hLs, Finset.card_singleton]
          -- Enumerate the surviving legs.
          let e' : Fin n' ≃ {i : Fin k // i ∉ Ls} :=
            (Fintype.equivFinOfCardEq hcardnotLs).symm
          set I'' : Finset (Fin n') := Finset.univ.filter (fun a => (e' a).val ∈ I)
            with hI''
          have hILs : ∀ i ∈ I, i ∉ Ls := fun i hi hc => hLsI i hc hi
          have hILs' : ∀ ℓ ∈ L, ℓ ∉ Ls := by
            intro ℓ hℓ; rw [hLs, Finset.mem_singleton]; exact hLne ℓ hℓ
          have hdrop := flatRank_dropLegs S Ls hLsone e' I hILs
          rw [← hdrop]
          set D := dropLegs S Ls hLsone e' with hD
          -- `e'` restricts to a bijection `I'' ≃ I` on the `I`-legs.
          have heI : ∀ a : Fin n', a ∈ I'' ↔ (e' a).val ∈ I := by
            intro a; simp [hI'']
          have hI''card : I''.card = I.card := by
            rw [hI'']
            apply Finset.card_bij (fun a _ => (e' a).val)
            · intro a ha; simp only [Finset.mem_filter] at ha; exact ha.2
            · intro a ha a' ha' heq; exact e'.injective (Subtype.ext heq)
            · intro j hj
              refine ⟨e'.symm ⟨j, hILs j hj⟩, ?_, ?_⟩
              · simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                  Equiv.apply_symm_apply]; exact hj
              · simp [Equiv.apply_symm_apply]
          have hI''pos : 1 ≤ I''.card := by rw [hI''card]; exact hI
          have hkpos : 1 ≤ k := by omega
          have hI''le : I''.card ≤ n' - 1 := by rw [hI''card, hn']; omega
          have hn'lt : n' < k := by rw [hn']; omega
          have hDF : ((flatRank D I'' : ℕ) : Cardinal) < Cardinal.mk F := by
            have hle : flatRank D I'' ≤ flatRank T I := by
              rw [hI'', hD, hdrop]
              exact hSflat
            exact lt_of_le_of_lt (by exact_mod_cast hle) hF
          have hIHbound := IH n' hn'lt D I'' hI''pos hI''le hDF
          refine hIHbound.trans ?_
          -- `univ \ I''` maps under `e'` to `L`.
          rw [hPint_def, Finset.prod_product]
          -- Reindex `∏ j'' ∈ I''` to `∏ j ∈ I`, and `∏ ℓ'' ∈ univ\I''` to `∏ ℓ ∈ L`.
          -- `univ \ I''` is exactly the preimage of `L` under `e'`.
          have hcomplL : (Finset.univ \ I'' : Finset (Fin n'))
              = Finset.univ.filter (fun a => (e' a).val ∈ L) := by
            ext a
            simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, heI, Finset.mem_filter]
            constructor
            · intro haI
              have hnLs : (e' a).val ≠ ℓ_last := by
                have hmem := (e' a).2
                simp only [hLs, Finset.mem_singleton] at hmem
                exact hmem
              rw [hL_def, Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_singleton]
              exact ⟨⟨Finset.mem_univ _, haI⟩, hnLs⟩
            · intro hL hcI
              exact hLI _ hL hcI
          -- Rewrite RHS `∏ j∈I ∏ ℓ∈L` as the nested product over `I''` and `univ\I''`.
          rw [show (∏ j ∈ I, ∏ ℓ ∈ L, subrankPair T j ℓ)
                = ∏ j'' ∈ I'', ∏ ℓ'' ∈ (Finset.univ \ I'' : Finset (Fin n')),
                    subrankPair T (e' j'').val (e' ℓ'').val from ?_]
          · -- LHS is already the nested product; bound each factor.
            refine Finset.prod_le_prod' (fun j'' _ => Finset.prod_le_prod' (fun ℓ'' _ => ?_))
            calc subrankPair D j'' ℓ''
                ≤ subrankPair S (e' j'').val (e' ℓ'').val :=
                  subrankPair_dropLegs S Ls hLsone e' j'' ℓ''
              _ ≤ subrankPair T (e' j'').val (e' ℓ'').val :=
                  hSsub (e' j'').val (e' ℓ'').val
          · -- Outer bijection `I'' ≃ I` (value: inner product reindexed by `e'`).
            symm
            refine Finset.prod_bij (fun a _ => (e' a).val) ?_ ?_ ?_ ?_
            · intro a ha; exact (heI a).mp ha
            · intro a ha a' ha' heq; exact e'.injective (Subtype.ext heq)
            · intro j hj
              refine ⟨e'.symm ⟨j, hILs j hj⟩, ?_, ?_⟩
              · rw [heI, Equiv.apply_symm_apply]; exact hj
              · simp [Equiv.apply_symm_apply]
            · intro a ha
              -- Inner bijection `(univ\I'') ≃ L`.
              refine Finset.prod_bij (fun b _ => (e' b).val) ?_ ?_ ?_ ?_
              · intro b hb
                rw [hcomplL, Finset.mem_filter] at hb; exact hb.2
              · intro b hb b' hb' heq; exact e'.injective (Subtype.ext heq)
              · intro ℓ hℓ
                refine ⟨e'.symm ⟨ℓ, hILs' ℓ hℓ⟩, ?_, ?_⟩
                · rw [hcomplL, Finset.mem_filter, Equiv.apply_symm_apply]
                  exact ⟨Finset.mem_univ _, hℓ⟩
                · simp [Equiv.apply_symm_apply]
              · intro b hb; rfl
        /- **PART B (eq:12b, paper tex:945-963).**  Apply `flush_support_le_rank`
           to the blocks `M_i`: it produces a covector `u : Fin b → F` (the first
           column of the flush matrix) with `support ≤ rank(M'_u)`, where
           `M'_u row i = ∑ l, M_i row l · u l` is the `u`-contraction of the blocks.
           We identify `rank(M'_u) = flatRank (sliceVec T ℓ_last u) I` (the
           `I`-flattening of the vector slice; tex:955-957 "the columns of `M'`
           are the `u`-contractions of the `M_i`"), then bound it by `P_internal`
           via `keyA_gen` (the eq:12a induction-hypothesis argument applied to the
           dim-`1`-`ℓ_last`-leg tensor `sliceVec T ℓ_last u`). -/
        -- `flush_support_le_rank` on the blocks `M_i` (using `(concatBlocks M).rank
        -- = flatRank T I < #F`).
        have hMF : ((concatBlocks M).rank : Cardinal) < Cardinal.mk F := by
          rw [← hflat]; exact hF
        obtain ⟨u, hu_supp⟩ := flush_support_le_rank M hMF
        -- `b = d ℓ_last`, so `u : Fin b → F` is a covector on leg `ℓ_last`.
        -- Identify `rank(M'_u) = flatRank (sliceVec T ℓ_last (u ∘ cast)) I`.
        set uV : Fin ((d ℓ_last : ℕ)) → F := fun j => u (Fin.cast rfl j) with huV
        -- The vector slice's `ℓ_last`-leg is dim `1`.
        -- Column reindex `Internal ≃ Cols'` for the vector-slice flattening:
        -- internal legs keep their coordinate, the `ℓ_last` leg collapses to `Fin 1`.
        set Cols' := (∀ j : {j : Fin k // j ∉ I},
            Fin ((fun jj => if jj ∈ ({ℓ_last} : Finset (Fin k)) then (1 : ℕ+) else d jj) j.val))
          with hCols'
        -- Helper: for a complement leg `j_leg ≠ ℓ_last`, the format collapses to `d`.
        have hfmtV_int : ∀ (j_leg : {j : Fin k // j ∉ I}), q j_leg →
            ((fun jj => if jj ∈ ({ℓ_last} : Finset (Fin k)) then (1 : ℕ+) else d jj) j_leg.val : ℕ)
              = (d j_leg.val : ℕ) := by
          intro j_leg hq
          have : j_leg.val ∉ ({ℓ_last} : Finset (Fin k)) := by
            simp only [Finset.mem_singleton]; exact hq
          simp only [if_neg this]
        have hfmtV_last : ((fun jj => if jj ∈ ({ℓ_last} : Finset (Fin k)) then (1 : ℕ+) else d jj)
            ℓ_last : ℕ) = 1 := by simp only [Finset.mem_singleton]; rfl
        -- The column reindex `Internal ≃ Cols'`.
        let colReindexV : Internal ≃ Cols' :=
          { toFun := fun internalIdx j_leg =>
              if h : q j_leg then
                Fin.cast (hfmtV_int j_leg h).symm (internalIdx ⟨j_leg, h⟩)
              else
                (Fin.cast (by
                  have hjl : j_leg.val = ℓ_last := by
                    simp only [q, not_not] at h; exact h
                  rw [hjl]; exact hfmtV_last.symm) (0 : Fin 1))
            invFun := fun c' jj =>
              Fin.cast (hfmtV_int jj.val jj.2) (c' jj.val)
            left_inv := by
              intro internalIdx
              funext jj
              simp only [dif_pos jj.2]
              apply Fin.ext; simp
            right_inv := by
              intro c'
              funext j_leg
              by_cases h : q j_leg
              · simp only [dif_pos h]
                apply Fin.ext; simp
              · simp only [dif_neg h]
                have hsub : Subsingleton (Fin ((fun jj => if jj ∈ ({ℓ_last} : Finset (Fin k))
                    then (1 : ℕ+) else d jj) j_leg.val)) := by
                  have hjl : j_leg.val = ℓ_last := by
                    simp only [q, not_not] at h; exact h
                  rw [show ((fun jj => if jj ∈ ({ℓ_last} : Finset (Fin k)) then (1 : ℕ+)
                      else d jj) j_leg.val : ℕ) = 1 by rw [hjl]; exact hfmtV_last]
                  infer_instance
                exact hsub.elim _ _ }
        -- The column equiv `Fin c ≃ Cols'`.
        let cEqV : Fin c ≃ Cols' :=
          (Fintype.equivFin Internal).symm.trans colReindexV
        -- Row format: a row leg `i ∈ I` is `≠ ℓ_last`, so the slice format agrees with `d`.
        have hfmtV_row : ∀ (ii : {ii : Fin k // ii ∈ I}),
            ((fun jj => if jj ∈ ({ℓ_last} : Finset (Fin k)) then (1 : ℕ+) else d jj) ii.val : ℕ)
              = (d ii.val : ℕ) := by
          intro ii
          have : ii.val ∉ ({ℓ_last} : Finset (Fin k)) := by
            simp only [Finset.mem_singleton]
            intro hc; exact hℓ_last (hc ▸ ii.2)
          simp only [if_neg this]
        -- Row reindex `Rows ≃ (sliceVec row index)`.
        let rEqV : Rows ≃ (∀ ii : {ii : Fin k // ii ∈ I},
            Fin ((fun jj => if jj ∈ ({ℓ_last} : Finset (Fin k)) then (1 : ℕ+) else d jj) ii.val)) :=
          Equiv.piCongrRight (fun ii => finCongr (hfmtV_row ii).symm)
        -- The full row equiv `Fin a ≃ (sliceVec row index)`.
        let rowEqV : Fin a ≃ (∀ ii : {ii : Fin k // ii ∈ I},
            Fin ((fun jj => if jj ∈ ({ℓ_last} : Finset (Fin k)) then (1 : ℕ+) else d jj) ii.val)) :=
          rowEquiv.trans rEqV
        -- `internalIdxOf i` = the internal multi-index named by block `i`.
        set internalIdxOf : Fin c → Internal := fun i => (Fintype.equivFin Internal).symm i
          with hinternalIdxOf
        -- `colEquiv (i, j)` at a complement leg: internal legs read off `internalIdxOf i`,
        -- the `ℓ_last` leg reads off `j`.  (In-scope analogue of `hB1_block`'s `hcolEquiv`.)
        have hcolEqV : ∀ (i : Fin c) (j : Fin b) (jl : {j : Fin k // j ∉ I}),
            (colEquiv (i, j) jl).val
              = if hq : (jl.val ≠ ℓ_last) then (internalIdxOf i ⟨jl, hq⟩).val
                else j.val := by
          intro i j jl
          change (esplit.symm (internalIdxOf i, elast.symm j) jl).val = _
          rw [Equiv.piEquivPiSubtypeProd_symm_apply]
          by_cases hq : (jl.val ≠ ℓ_last)
          · rw [dif_pos hq, dif_pos hq]
          · rw [dif_neg hq, dif_neg hq]
            change ((elast.symm j) ⟨jl, hq⟩).val = j.val
            simp only [elast, Equiv.symm_trans_apply, Equiv.piCongrLeft'_symm_apply]
            apply Fin.val_eq_val_of_heq
            exact eqRec_heq_self _ _
        -- `cEqV i` at a complement leg: internal legs read off `internalIdxOf i`.
        have hcEqV_int : ∀ (i : Fin c) (jl : {j : Fin k // j ∉ I}) (hq : jl.val ≠ ℓ_last),
            ((cEqV i) jl).val = (internalIdxOf i ⟨jl, hq⟩).val := by
          intro i jl hq
          change ((colReindexV (internalIdxOf i)) jl).val = _
          simp only [colReindexV, Equiv.coe_fn_mk, dif_pos (show q jl from hq)]
          rw [Fin.val_cast]
        -- `rowEqV row` agrees with `rowEquiv row` (in value) at every row leg `i ∈ I`.
        have hrowEqV_val : ∀ (row : Fin a) (ii : {ii : Fin k // ii ∈ I}),
            ((rowEqV row) ii).val = ((rowEquiv row) ii).val := by
          intro row ii
          change ((rEqV (rowEquiv row)) ii).val = _
          rw [show rEqV (rowEquiv row) = Equiv.piCongrRight
                (fun ii => finCongr (hfmtV_row ii).symm) (rowEquiv row) from rfl,
            Equiv.piCongrRight_apply]
          simp [finCongr_apply]
        -- Entry identity: `M'_u row i = flattenMatrix (sliceVec T ℓ_last uV) I (rowEqV row) (cEqV
        -- i)`.
        have hentry : (Matrix.of (fun (row : Fin a) (i : Fin c) => ∑ l, M i row l * u l))
            = (flattenMatrix (sliceVec T ℓ_last uV) I).submatrix rowEqV cEqV := by
          funext row i
          simp only [Matrix.submatrix_apply, Matrix.of_apply]
          change (∑ l, M i row l * u l)
            = flattenMatrix (sliceVec T ℓ_last uV) I (rowEqV row) (cEqV i)
          rw [show flattenMatrix (sliceVec T ℓ_last uV) I (rowEqV row) (cEqV i)
              = sliceVec T ℓ_last uV (fun ii => if h : ii ∈ I then (rowEqV row) ⟨ii, h⟩
                  else (cEqV i) ⟨ii, h⟩) from rfl]
          unfold sliceVec
          -- Rewrite `M'_u`'s sum (over `Fin b`) as the `colEquiv`-indexed contraction.
          rw [show (∑ l, M i row l * u l)
                = ∑ j : Fin ((d ℓ_last : ℕ)), uV j *
                    T (fun ii => if h : ii ∈ I then (rowEquiv row) ⟨ii, h⟩
                      else colEquiv (i, j) ⟨ii, h⟩) from ?_]
          · -- Termwise: the `j`-th `sliceVec` index equals `flattenMatrix`'s
            -- `colEquiv (i,j)` index.
            refine Finset.sum_congr rfl (fun j _ => ?_)
            congr 1
            apply congrArg
            funext ii
            by_cases hiI : ii ∈ I
            · -- Row leg `ii ∈ I`: `ii ≠ ℓ_last`, so the slice `if` takes the else branch,
              -- and `rowEqV` and `rowEquiv` agree in value.
              have hilne : ii ≠ ℓ_last := fun hc => hℓ_last (hc ▸ hiI)
              rw [dif_pos hiI, dif_neg hilne]
              apply Fin.ext
              rw [eqRec_eq_cast, Fin.val_eq_val_of_heq (cast_heq _ _)]
              simp only [dif_pos hiI]
              rw [hrowEqV_val row ⟨ii, hiI⟩]
            · simp only [dif_neg hiI]
              by_cases hil : ii = ℓ_last
              · -- The `ℓ_last` leg: both sides pick coordinate `j`.
                subst hil
                rw [dif_pos rfl]
                apply Fin.ext
                rw [hcolEqV i j ⟨ii, hiI⟩,
                  dif_neg (by simp : ¬ ((⟨ii, hiI⟩ : {j // j ∉ I}).val ≠ ii))]
              · -- An internal leg `≠ ℓ_last`: both sides equal `internalIdxOf i`'s coordinate.
                rw [dif_neg hil]
                apply Fin.ext
                have hq : (⟨ii, hiI⟩ : {j : Fin k // j ∉ I}).val ≠ ℓ_last := hil
                rw [eqRec_eq_cast,
                  Fin.val_eq_val_of_heq (cast_heq _ _),
                  hcolEqV i j ⟨ii, hiI⟩, dif_pos hq, hcEqV_int i ⟨ii, hiI⟩ hq]
          · -- `M i row l = flattenMatrix T I (rowEquiv row) (colEquiv (i,l))`; `uV j = u (cast j)`.
            symm
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [huV, mul_comm]
            rfl
        -- Conclude: `support ≤ rank(M'_u) = flatRank (sliceVec T ℓ_last uV) I ≤ P_internal`.
        calc (Finset.univ.filter (fun i => rankIncrement M i ≠ 0)).card
            ≤ (Matrix.of (fun (row : Fin a) (i : Fin c) => ∑ l, M i row l * u l)).rank :=
              hu_supp
          _ = flatRank (sliceVec T ℓ_last uV) I := by
              rw [hentry, flatRank_eq_rank, Matrix.rank_submatrix]
          _ ≤ P_internal :=
              keyA_gen {ℓ_last} rfl (sliceVec T ℓ_last uV)
                ((sliceVec_restricts T ℓ_last uV).flatRank_le I)
                (fun i j => subrankPair_sliceVec_le T ℓ_last uV i j)
      -- **(B1)** `univ.sup (rankIncrement M) ≤ P_last` (Briët et al. ITCS 2024,
      -- Thm. 3.2, tex:923-946).  By `Finset.sup_le` it suffices to bound each
      -- `rankIncrement M i`, and `rankIncrement_le_block_rank` (tex:937, eq:11b)
      -- bounds it by the full block rank `(M i).rank`.  The remaining per-block
      -- recursive bound `(M i).rank ≤ P_last` is `hB1_block`.
      have hB1 : Finset.univ.sup (rankIncrement M) ≤ P_last := by
        refine Finset.sup_le (fun i _ => ?_)
        exact le_trans (rankIncrement_le_block_rank M i) (hB1_block i)
      exact ⟨c, a, b, M, P_last, P_internal, hflat, hprod, hB1, hB2⟩
    obtain ⟨c, a, b, M, P_last, P_internal, hflat, hprod, hB1, hB2⟩ :=
      recursive_block_data
    /- (B0)+(B-arith) use the extracted helper:
       with `rMax = max_i r_i` and `support = #{i : r_i ≠ 0}`,
       `flatRank T I = rank([M_0;⋯]) ≤ rMax * support`. -/
    refine ⟨P_last, P_internal,
      Finset.univ.sup (rankIncrement M),
      (Finset.univ.filter (fun i => rankIncrement M i ≠ 0)).card,
      hprod, ?_, hB1, hB2⟩
    rw [hflat]
    exact concatBlocks_rank_le_maxIncrement_mul_support M
  /- **Final assembly (paper tex:908-914).**  With `I.card ≤ k - 2` (`hI'`) the
     block witness package supplies `rMax ≤ P_last`, `support ≤ P_internal`,
     `P_last * P_internal ≤ P`, and `flatRank T I ≤ rMax * support`, so
     `flatRank T I ≤ rMax * support ≤ P_last * P_internal ≤ P`. -/
  obtain ⟨P_last, P_internal, rMax, support, hfactor, hblocks, hrMax, hsupport⟩ :=
    paper_tex_920_970_witness_package hI'
  have hmul : rMax * support ≤ P_last * P_internal :=
    Nat.mul_le_mul hrMax hsupport
  exact le_trans hblocks (le_trans hmul (by simpa [P] using hfactor))

/-! ## Corollary 3.3 (tex:849-854). -/

private lemma exists_rpow_card_le_of_le_prod
    {ι : Type*} (s : Finset ι) {N : ℕ} (hN : 0 < N)
    (f : ι → ℕ) (hs : s.Nonempty) (hprod : N ≤ ∏ x ∈ s, f x) :
    ∃ x ∈ s, (N : ℝ) ^ ((1 : ℝ) / (s.card : ℝ)) ≤ f x := by
  classical
  by_contra h
  push_neg at h
  have hprod_pos : 0 < ∏ x ∈ s, f x := lt_of_lt_of_le hN hprod
  have hf_pos : ∀ x ∈ s, 0 < f x := by
    intro x hx
    by_contra hxpos
    have hxzero : f x = 0 := Nat.eq_zero_of_not_pos hxpos
    have hzero : ∏ y ∈ s, f y = 0 := Finset.prod_eq_zero hx hxzero
    rw [hzero] at hprod_pos
    exact (Nat.lt_irrefl 0) hprod_pos
  have hNreal_pos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hroot_pow :
      ((N : ℝ) ^ ((1 : ℝ) / (s.card : ℝ))) ^ s.card = (N : ℝ) := by
    have hcard_ne : (s.card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr hs)
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hNreal_pos.le]
    have hmul : (1 : ℝ) / (s.card : ℝ) * (s.card : ℝ) = 1 := by
      field_simp [hcard_ne]
    rw [hmul, Real.rpow_one]
  have hlt_prod :
      (∏ x ∈ s, (f x : ℝ)) <
        ∏ x ∈ s, (N : ℝ) ^ ((1 : ℝ) / (s.card : ℝ)) := by
    refine Finset.prod_lt_prod (fun x hx => ?_) (fun x hx => ?_) ?_
    · exact_mod_cast hf_pos x hx
    · exact (h x hx).le
    · obtain ⟨x, hx⟩ := hs
      exact ⟨x, hx, h x hx⟩
  rw [Finset.prod_const, hroot_pow] at hlt_prod
  have hprod_real : (N : ℝ) ≤ ∏ x ∈ s, (f x : ℝ) := by
    exact_mod_cast hprod
  linarith

/-- **Corollary 3.3** (tex:849-854, `\label{cor:Qij}`).

For any `k`-tensor `T` (with `k ≥ 2`) and any leg `i`, assuming `|F| > flatRank_i(T)`,
there is a `j ≠ i` such that `subrankPair T i j ≥ flatRank_i(T)^{1/(k-1)}`. -/
theorem exists_large_subrankPair
    {k : ℕ} (hk : 2 ≤ k) {d : Fin k → ℕ+} (T : KTensor F d) (i : Fin k)
    (hF : ((flatRank T {i} : ℕ) : Cardinal) < Cardinal.mk F) :
    ∃ j : Fin k, i ≠ j ∧
      (flatRank T {i} : ℝ) ^ ((1 : ℝ) / ((k : ℝ) - 1)) ≤ subrankPair T i j := by
  classical
  let s : Finset (Fin k) := (Finset.univ : Finset (Fin k)) \ {i}
  have hcard_s : s.card = k - 1 := by
    dsimp [s]
    rw [Finset.card_sdiff_of_subset]
    · simp
    · intro j hj
      simp
  have hs : s.Nonempty := by
    refine Finset.card_pos.mp ?_
    rw [hcard_s]
    omega
  have hprod_pair :
      flatRank T {i} ≤
        ∏ p ∈ ({i} : Finset (Fin k)) ×ˢ ((Finset.univ : Finset (Fin k)) \ {i}),
          subrankPair T p.1 p.2 := by
    refine subrankPair_prod_ge_flatRank T ({i} : Finset (Fin k)) ?_ ?_ hF
    · simp
    · simp
      omega
  have hprod :
      flatRank T {i} ≤ ∏ j ∈ s, subrankPair T i j := by
    have hrewrite :
        (∏ p ∈ ({i} : Finset (Fin k)) ×ˢ ((Finset.univ : Finset (Fin k)) \ {i}),
          subrankPair T p.1 p.2)
          = ∏ j ∈ s, subrankPair T i j := by
      dsimp [s]
      rw [Finset.prod_product, Finset.prod_singleton]
    simpa [hrewrite]
      using hprod_pair
  by_cases hzero : flatRank T {i} = 0
  · obtain ⟨j, hj⟩ := hs
    refine ⟨j, ?_, ?_⟩
    · have hj_not_mem : j ∉ ({i} : Finset (Fin k)) := (Finset.mem_sdiff.mp hj).2
      intro hij
      exact hj_not_mem (by simp [hij])
    · have hexp_ne : (1 : ℝ) / ((k : ℝ) - 1) ≠ 0 := by
        refine div_ne_zero one_ne_zero ?_
        have hk_real : (2 : ℝ) ≤ k := by exact_mod_cast hk
        nlinarith
      have hexp_ne' : ((k : ℝ) - 1)⁻¹ ≠ 0 := by
        simpa [one_div] using hexp_ne
      have hnonneg : (0 : ℝ) ≤ (subrankPair T i j : ℝ) := by exact_mod_cast Nat.zero_le _
      simp [hzero, one_div, Real.zero_rpow hexp_ne']
  · have hpos : 0 < flatRank T {i} := Nat.pos_of_ne_zero hzero
    obtain ⟨j, hj, hlarge⟩ :=
      exists_rpow_card_le_of_le_prod s hpos (fun j => subrankPair T i j) hs hprod
    refine ⟨j, ?_, ?_⟩
    · have hj_not_mem : j ∉ ({i} : Finset (Fin k)) := (Finset.mem_sdiff.mp hj).2
      intro hij
      exact hj_not_mem (by simp [hij])
    · have hcard_real : (s.card : ℝ) = (k : ℝ) - 1 := by
        rw [hcard_s]
        norm_num [Nat.cast_sub (by omega : 1 ≤ k)]
      simpa [hcard_real] using hlarge

/-! ## Corollary 3.5 (tex:976-996): asymptotic subrank lower bound. -/

/-- **Subrank** `subrank(T)` (tex:974): largest `r` with `T ≥ ⟨r⟩`.

    Realized as the `sSup` (over `ℕ`) of the set of positive `r` for which the
    rank-`r` unit `k`-tensor restricts to `T`. Bounded above by `min_i (d i)`. -/
noncomputable def subrank {k : ℕ} {d : Fin k → ℕ+} (T : KTensor F d) : ℕ :=
  sSup { r : ℕ | ∃ hr : 0 < r,
    Restricts (unitTensor F (k := k) ⟨r, hr⟩) T }

/-- Dimension format for the n-fold Kronecker power of a KTensor with dimensions d. -/
noncomputable def kronPowFormat {k : ℕ} (d : Fin k → ℕ+) : ℕ → Fin k → ℕ+
  | 0 => d
  | n + 1 => fun i => kronPowFormat d n i * d i

/-- n-fold Kronecker power: kronPowNat T 0 = T, kronPowNat T (n+1) = kroneckerTensor (kronPowNat T
    n) T. -/
noncomputable def kronPowNat {k : ℕ} {d : Fin k → ℕ+} (T : KTensor F d) :
    (n : ℕ) → KTensor F (kronPowFormat d n)
  | 0 => T
  | n + 1 => kroneckerTensor (kronPowNat T n) T

/-- **Asymptotic subrank** Q̃(T) = sup_{j≥1} subrank(T^{⊠j})^{1/j} (paper tex:974).
    By Fekete lemma this equals lim_{j→∞} subrank(T^{⊠j})^{1/j}.

    Implementation note: `kronPowNat T n = T^{⊠(n+1)}` (its base case is
    `kronPowNat T 0 = T`), so the `j`-th power `T^{⊠j}` (`j ≥ 1`) is
    `kronPowNat T (j-1)`, and the `j`-th root uses exponent `1/(n+1)` where
    `n = j-1` ranges over all of `ℕ`. Taking the `1/n`-th root of
    `kronPowNat T n = T^{⊠(n+1)}` (the previous form) computed the *(n+1)*-th
    power's *n*-th root, which overestimates: e.g. it gave `Q̃(⟨2⟩) = 4 ≠ 2`. -/
noncomputable def asympSubrank {k : ℕ} {d : Fin k → ℕ+} (T : KTensor F d) : ℝ :=
  sSup (Set.range (fun n : ℕ =>
    (subrank (kronPowNat T n) : ℝ) ^ ((1 : ℝ) / ((n : ℝ) + 1))))

/- **Corollary 3.5** (tex:976-996, unlabeled) is proved in
`AsymptoticSubrank/Main.lean` as
`Semicontinuity.minCut_flatRank_le_asympSubrank_of_infinite`, in the
`Finset.inf'`-over-`MinCut.admissibleCuts` form
`(min_{∅≠I⊊[k]} flatRank_I T)^{2/(k(k-1))} ≤ asympSubrank T`.

It is not stated in this file: its proof needs the weighted Vrana–Christandl
formula (tex:993-996, MR3627407) and field invariance (Strassen 1988
Thm 3.10, tex:991-992), both formalized in `AsymptoticSubrank/`, which
imports this file. Beware that the `⨅ I ∈ {set}` idiom for the minimum is
vacuous over `ℝ` (the excluded empty cut contributes an empty-membership
infimum `= 0`); the `Finset.inf'` form is the meaningful statement. -/

end Semicontinuity
