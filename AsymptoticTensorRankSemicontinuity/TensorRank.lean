/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.MaxRankBound
import Mathlib.LinearAlgebra.TensorPower.Basic

/-!
# Tensor rank of `k`-tensors and the admissible functional

Source: tex:396 (tensor rank def), tex:564-566 (asymp tensor rank as
admissible functional).

* `simpleTensor u`: the simple `k`-tensor `u_1 ⊗ ⋯ ⊗ u_k` (`u_i : Fin (d_i) → F`).
* `tensorRank T`: smallest `r` such that `T` is a sum of `r` simple tensors.
* `tensorRankAdmissible F d`: the `AdmissibleFunctional F (KTensor F d)` whose
  `F_n` is tensor rank on the regrouped Kronecker product (paper tex:564).
-/

namespace Semicontinuity

universe u

variable {F : Type u} [Field F]

/-! ## A.6.1 — simple tensors and tensor rank -/

/-- The simple `k`-tensor `u_1 ⊗ ⋯ ⊗ u_k` from leg-wise vectors `u_i : Fin (d_i) → F`.

    On indices `(idx i)` it evaluates to `∏ i, u i (idx i)`. -/
def simpleTensor {k : ℕ} {d : Fin k → ℕ+}
    (u : (i : Fin k) → Fin (d i) → F) : KTensor F d :=
  fun idx => ∏ i, u i (idx i)

/-- A `k`-tensor is **simple** if it is `u_1 ⊗ ⋯ ⊗ u_k` for some leg-wise vectors. -/
def IsSimpleTensor {k : ℕ} {d : Fin k → ℕ+} (T : KTensor F d) : Prop :=
  ∃ u : (i : Fin k) → Fin (d i) → F, T = simpleTensor u

/-- **Tensor rank** `R(T)` (tex:396): smallest `r ∈ ℕ` such that `T` is a sum of
    `r` simple tensors. Defaults to `0` when `T = 0`. -/
noncomputable def tensorRank {k : ℕ} {d : Fin k → ℕ+} (T : KTensor F d) : ℕ :=
  sInf { r : ℕ | ∃ s : Fin r → KTensor F d,
      (∀ i, IsSimpleTensor (s i)) ∧ T = ∑ i, s i }

/-- `tensorRank 0 = 0`: the empty sum (over `Fin 0`) realizes rank 0. -/
@[simp]
lemma tensorRank_zero {k : ℕ} {d : Fin k → ℕ+} :
    tensorRank (F := F) (d := d) (0 : KTensor F d) = 0 := by
  unfold tensorRank
  apply Nat.sInf_eq_zero.mpr
  left
  refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
  simp [Finset.sum_empty]

/-! ### Helper: scalar absorption into the first leg of a simple tensor.

For `k ≥ 1`, scaling a simple tensor by `α : F` yields a simple tensor: absorb
`α` into leg 0 by replacing `u 0 ↦ α • u 0`. Below we package this for the case
where `u i j = if j = idx i then 1 else 0`. -/

/-- The "scaled standard-basis" simple tensor at `idx`, scaling factor `α`,
    absorbing the scalar into leg `⟨0, hk⟩`. Concretely:
    leg `⟨0, hk⟩` is `j ↦ if j = idx ⟨0, hk⟩ then α else 0`;
    each other leg `i` is `j ↦ if j = idx i then 1 else 0`. -/
private def stdBasisSimpleScaled {k : ℕ} (hk : 1 ≤ k) {d : Fin k → ℕ+}
    (α : F) (idx : ∀ i : Fin k, Fin (d i)) :
    (i : Fin k) → Fin (d i) → F :=
  fun i j =>
    if i = ⟨0, hk⟩ then (if j = idx i then α else 0)
                   else (if j = idx i then 1 else 0)

/-- The "scaled standard basis" simple tensor as a `KTensor`, equal to
    `fun jdx => if jdx = idx then α else 0`. -/
private lemma simpleTensor_stdBasisSimpleScaled
    {k : ℕ} (hk : 1 ≤ k) {d : Fin k → ℕ+}
    (α : F) (idx : ∀ i : Fin k, Fin (d i)) :
    simpleTensor (F := F) (d := d) (stdBasisSimpleScaled hk α idx) =
      fun jdx => if jdx = idx then α else 0 := by
  funext jdx
  simp only [simpleTensor, stdBasisSimpleScaled]
  -- Product expression: at i = ⟨0, hk⟩ we get `if jdx i = idx i then α else 0`,
  -- elsewhere `if jdx i = idx i then 1 else 0`. Both branches equal `0` unless
  -- `jdx i = idx i` for every i; in that case the product is `α · 1 · ⋯ · 1 = α`.
  by_cases h : jdx = idx
  · subst h
    -- Every factor reduces to `α` (at i=⟨0,hk⟩) or `1` (otherwise).
    rw [if_pos rfl]
    classical
    rw [show (∏ i, if i = (⟨0, hk⟩ : Fin k)
                  then (if jdx i = jdx i then α else 0)
                  else (if jdx i = jdx i then 1 else 0))
            = ∏ i, if i = (⟨0, hk⟩ : Fin k) then α else 1 from
        Finset.prod_congr rfl (fun i _ => by simp)]
    rw [Finset.prod_ite_eq' (Finset.univ) (⟨0, hk⟩ : Fin k) (fun _ => α)]
    simp
  · rw [if_neg h]
    -- There exists i₀ with jdx i₀ ≠ idx i₀; the factor at i₀ is 0.
    have hex : ∃ i₀ : Fin k, jdx i₀ ≠ idx i₀ := by
      by_contra hne
      push_neg at hne
      exact h (funext hne)
    obtain ⟨i₀, hi₀⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ i₀)
    by_cases hi : i₀ = ⟨0, hk⟩ <;> simp [hi, hi₀]

/-- Each `KTensor F d` has finite tensor rank: every tensor has SOME decomposition
    into simple tensors (in particular the standard-basis decomposition).
    Requires `1 ≤ k` (for `k = 0` only scalars expressible as `n · 1` are reachable). -/
lemma exists_tensorRank_decomp {k : ℕ} (hk : 1 ≤ k) {d : Fin k → ℕ+}
    (T : KTensor F d) :
    ∃ r : ℕ, ∃ s : Fin r → KTensor F d,
      (∀ i, IsSimpleTensor (s i)) ∧ T = ∑ i, s i := by
  classical
  -- Enumerate the finite index set ∀ i, Fin (d i) by `Fin (∏ d_i)`.
  set Idx := ∀ i : Fin k, Fin (d i)
  let n : ℕ := Fintype.card Idx
  let e : Fin n ≃ Idx := (Fintype.equivFin Idx).symm
  -- Standard-basis decomposition: T = ∑_j (T (e j)) • (delta-at-(e j)).
  refine ⟨n,
    fun j => simpleTensor (F := F) (d := d) (stdBasisSimpleScaled hk (T (e j)) (e j)),
    ?_, ?_⟩
  · intro j; exact ⟨_, rfl⟩
  · -- Pointwise: at jdx, ∑_j (if jdx = e j then T (e j) else 0) = T jdx.
    funext jdx
    have hsum : (∑ j : Fin n,
        simpleTensor (F := F) (d := d)
          (stdBasisSimpleScaled hk (T (e j)) (e j))) jdx =
        ∑ j : Fin n, (if jdx = e j then T (e j) else 0) := by
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [simpleTensor_stdBasisSimpleScaled hk (T (e j)) (e j)]
    rw [hsum]
    symm
    -- The sum picks out the unique j with e j = jdx, namely j = e.symm jdx.
    have hpick :
        ∑ j : Fin n, (if jdx = e j then T (e j) else 0) = T jdx := by
      have : ∀ j : Fin n, (if jdx = e j then T (e j) else 0) =
             (if e.symm jdx = j then T jdx else 0) := by
        intro j
        by_cases hj : e.symm jdx = j
        · have hje : e j = jdx := by
            rw [← hj, Equiv.apply_symm_apply]
          simp [hj, hje]
        · have hne_jdx : jdx ≠ e j := by
            intro heq
            apply hj
            rw [heq, Equiv.symm_apply_apply]
          simp [hne_jdx, hj]
      simp_rw [this]
      rw [Finset.sum_ite_eq Finset.univ (e.symm jdx) (fun _ => T jdx)]
      simp
    exact hpick

/-! ## A.6.3 — Subadditivity of tensorRank under `+`. -/

/-- **Subadditivity** of tensor rank: `R(T + S) ≤ R(T) + R(S)`.
    By concatenating decompositions of `T` and `S`. Requires `1 ≤ k` to ensure
    `R(T)` and `R(S)` are achieved by some decomposition (`exists_tensorRank_decomp`). -/
lemma tensorRank_add_le {k : ℕ} (hk : 1 ≤ k) {d : Fin k → ℕ+} (T S : KTensor F d) :
    tensorRank (T + S) ≤ tensorRank T + tensorRank S := by
  classical
  -- The decomposition set for any tensor is a nonempty subset of `ℕ` bounded below
  -- by `tensorRank`, with `Nat.sInf_mem`.
  -- Set membership of `tensorRank T` and `tensorRank S` follows from
  -- `exists_tensorRank_decomp` (nonempty) + `Nat.sInf_mem`.
  have hT_mem : tensorRank T ∈
      { r : ℕ | ∃ s : Fin r → KTensor F d,
          (∀ i, IsSimpleTensor (s i)) ∧ T = ∑ i, s i } := by
    apply Nat.sInf_mem
    obtain ⟨rT, sT, hsT, hT⟩ := exists_tensorRank_decomp hk T
    exact ⟨rT, sT, hsT, hT⟩
  have hS_mem : tensorRank S ∈
      { r : ℕ | ∃ s : Fin r → KTensor F d,
          (∀ i, IsSimpleTensor (s i)) ∧ S = ∑ i, s i } := by
    apply Nat.sInf_mem
    obtain ⟨rS, sS, hsS, hS⟩ := exists_tensorRank_decomp hk S
    exact ⟨rS, sS, hsS, hS⟩
  obtain ⟨sT, hsT, hT⟩ := hT_mem
  obtain ⟨sS, hsS, hS⟩ := hS_mem
  -- Build the concatenated decomposition of size `tensorRank T + tensorRank S`.
  refine Nat.sInf_le ?_
  refine ⟨Fin.append sT sS, ?_, ?_⟩
  · -- Each summand is simple.
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [Fin.append_left]
      exact hsT j
    · intro j
      simp only [Fin.append_right]
      exact hsS j
  · -- Sum reorders as `∑ T + ∑ S` by `Fin.sum_univ_add`.
    have hsplit : (∑ i, Fin.append sT sS i)
        = (∑ i : Fin (tensorRank T), sT i) + ∑ i : Fin (tensorRank S), sS i := by
      rw [Fin.sum_univ_add]
      refine congr_arg₂ (· + ·) ?_ ?_
      · refine Finset.sum_congr rfl ?_
        intro j _; rw [Fin.append_left]
      · refine Finset.sum_congr rfl ?_
        intro j _; rw [Fin.append_right]
    rw [hsplit, ← hT, ← hS]

/-! ## A.6.6 — Scalar invariance: `R(α • T) = R(T)` for `α ≠ 0`. -/

/-- **Helper**: `α • simpleTensor u = simpleTensor (Function.update u i₀ (α • u i₀))`
    for any `i₀ : Fin k`. Absorbs the scalar into leg `i₀`. -/
private lemma smul_simpleTensor_eq_update {k : ℕ} {d : Fin k → ℕ+}
    (α : F) (u : (i : Fin k) → Fin (d i) → F) (i₀ : Fin k) :
    α • simpleTensor (F := F) (d := d) u =
      simpleTensor (F := F) (d := d)
        (Function.update u i₀ (α • u i₀)) := by
  classical
  funext jdx
  simp only [simpleTensor, Pi.smul_apply, smul_eq_mul]
  -- Split the products at index i₀ using `Finset.prod_eq_prod_diff_singleton_mul`.
  have h_split_u :
      (∏ i, u i (jdx i)) =
        u i₀ (jdx i₀) * ∏ i ∈ (Finset.univ : Finset (Fin k)) \ {i₀}, u i (jdx i) :=
    Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ i₀) _
  have h_split_upd :
      (∏ i, Function.update u i₀ (α • u i₀) i (jdx i)) =
        Function.update u i₀ (α • u i₀) i₀ (jdx i₀) *
          ∏ i ∈ (Finset.univ : Finset (Fin k)) \ {i₀},
            Function.update u i₀ (α • u i₀) i (jdx i) :=
    Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ i₀) _
  rw [h_split_u, h_split_upd]
  -- Simplify the update at i₀ and outside i₀.
  have heq_outside :
      ∀ i ∈ (Finset.univ : Finset (Fin k)) \ {i₀},
        Function.update u i₀ (α • u i₀) i (jdx i) = u i (jdx i) := by
    intro i hi
    have : i ≠ i₀ := by
      intro h; rw [h] at hi; simp at hi
    rw [Function.update_of_ne this]
  rw [Finset.prod_congr rfl heq_outside]
  rw [Function.update_self]
  change α * (u i₀ (jdx i₀) * _) = α • u i₀ (jdx i₀) * _
  rw [smul_eq_mul, ← mul_assoc]

/-- **Scalar invariance** of tensor rank: `R(α • T) = R(T)` for nonzero `α`.
    Requires `1 ≤ k` (for `k = 0`, simpleTensors are all `1`, so the only
    achievable values are `ℕ`-image, and scaling by α changes the achievable set).

    Scaling absorbs into one of the leg-vectors of each simple summand. -/
lemma tensorRank_smul_of_ne_zero {k : ℕ} (hk : 1 ≤ k) {d : Fin k → ℕ+}
    (α : F) (hα : α ≠ 0) (T : KTensor F d) :
    tensorRank (α • T) = tensorRank T := by
  classical
  -- One direction: R(α • T) ≤ R(T).
  have one_dir : ∀ (β : F) (_hβ : β ≠ 0) (S : KTensor F d),
      tensorRank (β • S) ≤ tensorRank S := by
    intro β _ S
    -- Pull a decomposition of S out via `exists_tensorRank_decomp`.
    have hS_mem : tensorRank S ∈
        { r : ℕ | ∃ s : Fin r → KTensor F d,
            (∀ i, IsSimpleTensor (s i)) ∧ S = ∑ i, s i } := by
      apply Nat.sInf_mem
      obtain ⟨rS, sS, hsS, hS⟩ := exists_tensorRank_decomp hk S
      exact ⟨rS, sS, hsS, hS⟩
    obtain ⟨sS, hsS, hS⟩ := hS_mem
    -- Build decomposition of β • S of the same size by absorbing β into each summand.
    refine Nat.sInf_le ?_
    refine ⟨fun i => β • sS i, ?_, ?_⟩
    · intro i
      obtain ⟨u, hu⟩ := hsS i
      refine ⟨Function.update u ⟨0, hk⟩ (β • u ⟨0, hk⟩), ?_⟩
      change β • sS i = _
      rw [hu]
      exact smul_simpleTensor_eq_update β u ⟨0, hk⟩
    · change β • S = ∑ i, β • sS i
      rw [← Finset.smul_sum, ← hS]
  -- Apply with β = α to get R(α • T) ≤ R(T).
  have h1 : tensorRank (α • T) ≤ tensorRank T := one_dir α hα T
  -- Apply with β = α⁻¹ to (α • T) to get R(T) = R(α⁻¹ • (α • T)) ≤ R(α • T).
  have h2 : tensorRank T ≤ tensorRank (α • T) := by
    have hαinv : α⁻¹ ≠ 0 := inv_ne_zero hα
    have key : α⁻¹ • (α • T) = T := by
      rw [smul_smul, inv_mul_cancel₀ hα, one_smul]
    calc tensorRank T = tensorRank (α⁻¹ • (α • T)) := by rw [key]
      _ ≤ tensorRank (α • T) := one_dir α⁻¹ hαinv (α • T)
  exact le_antisymm h1 h2

/-! ## A.6.7 — F_1 boundedness for `KTensor F d`. -/

/-- **F_1 bound**: For any `T : KTensor F d` (with `1 ≤ k`), `R(T) ≤ ∏ d_i`
    (the trivial bound via the standard-basis decomposition). -/
lemma tensorRank_le_prod_dims {k : ℕ} (hk : 1 ≤ k) {d : Fin k → ℕ+}
    (T : KTensor F d) :
    tensorRank T ≤ ∏ i, (d i : ℕ) := by
  classical
  -- The proof from `exists_tensorRank_decomp`: that decomposition has size
  -- `Fintype.card (∀ i, Fin (d i)) = ∏ d_i`.
  set Idx := ∀ i : Fin k, Fin (d i)
  have hcard : Fintype.card Idx = ∏ i, (d i : ℕ) := by
    simp [Idx, Fintype.card_pi]
  -- Reproduce the explicit decomposition from `exists_tensorRank_decomp`.
  let n : ℕ := Fintype.card Idx
  let e : Fin n ≃ Idx := (Fintype.equivFin Idx).symm
  have hdecomp :
      ∃ s : Fin n → KTensor F d,
        (∀ i, IsSimpleTensor (s i)) ∧ T = ∑ i, s i := by
    refine ⟨fun j => simpleTensor (F := F) (d := d)
      (stdBasisSimpleScaled hk (T (e j)) (e j)), ?_, ?_⟩
    · intro j; exact ⟨_, rfl⟩
    · funext jdx
      have hsum : (∑ j : Fin n,
          simpleTensor (F := F) (d := d)
            (stdBasisSimpleScaled hk (T (e j)) (e j))) jdx =
          ∑ j : Fin n, (if jdx = e j then T (e j) else 0) := by
        rw [Finset.sum_apply]
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [simpleTensor_stdBasisSimpleScaled hk (T (e j)) (e j)]
      rw [hsum]
      symm
      have : ∀ j : Fin n, (if jdx = e j then T (e j) else 0) =
             (if e.symm jdx = j then T jdx else 0) := by
        intro j
        by_cases hj : e.symm jdx = j
        · have hje : e j = jdx := by
            rw [← hj, Equiv.apply_symm_apply]
          simp [hj, hje]
        · have hne_jdx : jdx ≠ e j := by
            intro heq
            apply hj
            rw [heq, Equiv.symm_apply_apply]
          simp [hne_jdx, hj]
      simp_rw [this]
      rw [Finset.sum_ite_eq Finset.univ (e.symm jdx) (fun _ => T jdx)]
      simp
  rw [← hcard]
  exact Nat.sInf_le hdecomp

/-! ## A.6.2 — `regroupingMap` from `TensorPower F n V` to `KTensor F (d^n)` -/

/-- Entrywise `n`-th power of a format `d : Fin k → ℕ+`: `(d^n) i = (d i)^n`. -/
def formatPow {k : ℕ} (d : Fin k → ℕ+) (n : ℕ+) : Fin k → ℕ+ :=
  fun i => d i ^ (n : ℕ)

/-- An index of `Fin (d^n)` as an `n`-tuple of indices in `Fin d`.

    Defined via Mathlib's computable mixed-base enumeration
    `finFunctionFinEquiv : (Fin n → Fin d) ≃ Fin (d^n)` (see
    `Mathlib.Algebra.BigOperators.Fin` line 580) composed with `Fin.rev` so that
    the *low* positions of the resulting `Fin n → Fin d` tuple correspond to the
    *high* digits of the underlying index. This convention is forced by the
    `Fin.append` / `kronLeftIndex` decomposition: `kronLeftIndex idx i = idx / d^n'`
    (the high `n` digits, see `MaxRankBound.lean` line 99). With the `Fin.rev`
    convention, the digit-decomposition lemmas `sliceFun_split_left` and
    `sliceFun_split_right` (Christandl-Hoeberechts-Nieuwboer-Vrana-Zuiddam tex:570)
    hold by routine arithmetic.

    Concretely: `powIndexEquiv d n a j = finFunctionFinEquiv.symm a (Fin.rev j) =
    a / d^(n-1-j) % d` — big-endian, position 0 = most significant digit. -/
def powIndexEquiv (d n : ℕ+) :
    Fin ((d : ℕ) ^ (n : ℕ)) ≃ (Fin (n : ℕ) → Fin (d : ℕ)) where
  toFun a j := finFunctionFinEquiv.symm a (Fin.rev j)
  invFun f := finFunctionFinEquiv (fun j => f (Fin.rev j))
  left_inv a := by
    -- finFunctionFinEquiv (fun j => finFunctionFinEquiv.symm a (Fin.rev (Fin.rev j))) = a
    simp only [Fin.rev_rev]
    exact finFunctionFinEquiv.apply_symm_apply a
  right_inv f := by
    funext j
    change finFunctionFinEquiv.symm
        (finFunctionFinEquiv (fun j' => f (Fin.rev j'))) (Fin.rev j) = f j
    rw [finFunctionFinEquiv.symm_apply_apply]
    simp [Fin.rev_rev]

/-- **`powIndexEquiv` at `n = 1` is the identity on values** (Christandl-Hoeberechts-
    Nieuwboer-Vrana-Zuiddam tex:570). For `a : Fin (d^1)` and the unique `j : Fin 1`,
    the single-digit base-`d` decomposition `powIndexEquiv d 1 a j` has underlying
    `Nat` value `a.val`.

    Paper tex:564: `regroupingMap` is the linear extension of `v_1 ⊗ ⋯ ⊗ v_n ↦
    v_1 ⊠ ⋯ ⊠ v_n`; for `n = 1` the single Kronecker factor is the tensor itself,
    so the index decomposition is the identity. Concretely `powIndexEquiv d 1 a j =
    finFunctionFinEquiv.symm a (Fin.rev j) = a / d^0 % d = a % d = a` (since
    `a.val < d^1 = d`). -/
lemma powIndexEquiv_one (d : ℕ+) (a : Fin ((d : ℕ) ^ (1 : ℕ))) (j : Fin 1) :
    (powIndexEquiv d 1 a j).val = a.val := by
  fin_cases j
  have ha : a.val < (d : ℕ) := by have := a.isLt; simpa using this
  simp only [powIndexEquiv, Equiv.coe_fn_mk]
  simp [finFunctionFinEquiv, Nat.mod_eq_of_lt ha]

/-- Evaluation of a `KTensor` at a fixed multi-index, as a linear functional. -/
def kTensorEval {k : ℕ} {d : Fin k → ℕ+}
    (idx : ∀ i : Fin k, Fin (d i)) : KTensor F d →ₗ[F] F where
  toFun T := T idx
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

/-- The `j`-th slice of a grouped format-`d^n` index. -/
noncomputable def sliceFun {k : ℕ} (d : Fin k → ℕ+) (n : ℕ+)
    (idx : ∀ i : Fin k, Fin (formatPow d n i)) (j : Fin (n : ℕ)) :
    ∀ i : Fin k, Fin (d i) :=
  fun i => powIndexEquiv (d i) n (by simpa [formatPow] using idx i) j

/-- **A.6.2** Regrouping map: linearly extends the multilinear assignment
    `v_1, …, v_n ↦ v_1 ⊠ ⋯ ⊠ v_n`. Paper tex:564.

    Defined via `PiTensorProduct.lift` applied to the multilinear Kronecker product. -/
noncomputable def regroupingMap {k : ℕ} (d : Fin k → ℕ+) (n : ℕ+) :
    TensorPower F (n : ℕ) (KTensor F d) →ₗ[F] KTensor F (formatPow d n) :=
  PiTensorProduct.lift <|
    MultilinearMap.pi fun idx =>
      (MultilinearMap.mkPiRing F (Fin (n : ℕ)) (1 : F)).compLinearMap
        fun j => kTensorEval (F := F) (d := d) (sliceFun d n idx j)

/-! ## A.6.4 — Submultiplicativity of tensor rank under Kronecker product. -/

/-- Leg-wise factors witnessing that the Kronecker product of simple tensors is simple. -/
private def kronSimpleFactors {k : ℕ} {dT dS : Fin k → ℕ+}
    (u : (i : Fin k) → Fin (dT i) → F)
    (v : (i : Fin k) → Fin (dS i) → F) :
    (i : Fin k) → Fin (dT i * dS i) → F :=
  fun i a =>
    u i ((finProdFinEquiv.symm (by simpa [PNat.mul_coe] using a)).1) *
      v i ((finProdFinEquiv.symm (by simpa [PNat.mul_coe] using a)).2)

/-- The grouped Kronecker product of two simple tensors is simple. -/
private lemma simpleTensor_kroneckerTensor {k : ℕ} {dT dS : Fin k → ℕ+}
    (u : (i : Fin k) → Fin (dT i) → F)
    (v : (i : Fin k) → Fin (dS i) → F) :
    simpleTensor (F := F) (d := dT) u ⊠ simpleTensor (F := F) (d := dS) v =
      simpleTensor (F := F) (d := fun i => dT i * dS i) (kronSimpleFactors u v) := by
  funext idx
  simp [kroneckerTensor, simpleTensor, kronSimpleFactors, kronLeftIndex, kronRightIndex,
    Finset.prod_mul_distrib]

/-- A simple tensor decomposition of a Kronecker product is obtained by multiplying
    all pairs of summands. -/
private lemma kroneckerTensor_sum_sum {k rT rS : ℕ} {dT dS : Fin k → ℕ+}
    (sT : Fin rT → KTensor F dT) (sS : Fin rS → KTensor F dS) :
    (∑ i, sT i) ⊠ (∑ j, sS j) =
      ∑ q : Fin (rT * rS),
        (sT (finProdFinEquiv.symm q).1) ⊠ (sS (finProdFinEquiv.symm q).2) := by
  funext idx
  simp only [kroneckerTensor, Finset.sum_apply]
  rw [Fintype.sum_mul_sum]
  rw [← Finset.sum_product' (s := Finset.univ) (t := Finset.univ)]
  exact (by
    simpa using (Fintype.sum_equiv finProdFinEquiv
      (fun p : Fin rT × Fin rS =>
        sT p.1 (kronLeftIndex idx) * sS p.2 (kronRightIndex idx))
      (fun q : Fin (rT * rS) =>
        sT (finProdFinEquiv.symm q).1 (kronLeftIndex idx) *
          sS (finProdFinEquiv.symm q).2 (kronRightIndex idx))
      (by intro p; simp)))

/-- The grouped Kronecker product of simple tensors is simple. -/
private lemma IsSimpleTensor.kroneckerTensor {k : ℕ} {dT dS : Fin k → ℕ+}
    {T : KTensor F dT} {S : KTensor F dS}
    (hT : IsSimpleTensor T) (hS : IsSimpleTensor S) :
    IsSimpleTensor (T ⊠ S) := by
  obtain ⟨u, rfl⟩ := hT
  obtain ⟨v, rfl⟩ := hS
  exact ⟨kronSimpleFactors u v, simpleTensor_kroneckerTensor u v⟩

/-- **Submultiplicativity** of tensor rank under `⊠`: `R(T ⊠ S) ≤ R(T) · R(S)`.
    Distribute simple-tensor decompositions: each pair `(t_i, s_j)` gives a simple
    summand of `T ⊠ S`. -/
lemma tensorRank_kron_le {k : ℕ} (hk : 1 ≤ k) {dT dS : Fin k → ℕ+}
    (T : KTensor F dT) (S : KTensor F dS) :
    tensorRank (T ⊠ S) ≤ tensorRank T * tensorRank S := by
  classical
  have hT_mem : tensorRank T ∈
      { r : ℕ | ∃ s : Fin r → KTensor F dT,
          (∀ i, IsSimpleTensor (s i)) ∧ T = ∑ i, s i } := by
    apply Nat.sInf_mem
    obtain ⟨rT, sT, hsT, hT⟩ := exists_tensorRank_decomp hk T
    exact ⟨rT, sT, hsT, hT⟩
  have hS_mem : tensorRank S ∈
      { r : ℕ | ∃ s : Fin r → KTensor F dS,
          (∀ i, IsSimpleTensor (s i)) ∧ S = ∑ i, s i } := by
    apply Nat.sInf_mem
    obtain ⟨rS, sS, hsS, hS⟩ := exists_tensorRank_decomp hk S
    exact ⟨rS, sS, hsS, hS⟩
  obtain ⟨sT, hsT, hT⟩ := hT_mem
  obtain ⟨sS, hsS, hS⟩ := hS_mem
  refine Nat.sInf_le ?_
  refine ⟨fun q =>
      (sT (finProdFinEquiv.symm q).1) ⊠ (sS (finProdFinEquiv.symm q).2), ?_, ?_⟩
  · intro q
    exact IsSimpleTensor.kroneckerTensor (hsT _) (hsS _)
  · conv_lhs =>
      rw [hT, hS]
    exact kroneckerTensor_sum_sum sT sS

/-! ## A.6.5 — Format-cast invariance of `tensorRank`.

If two formats `d, d' : Fin k → ℕ+` agree (`d = d'` as functions), the canonical
identification `KTensor F d = KTensor F d'` (which is just `rfl` after `subst`)
preserves tensor rank. -/

/-- **Format-cast invariance** of tensor rank. Given a leg-wise format equality
    `h : d = d'`, transporting a tensor preserves rank. -/
lemma tensorRank_format_cast {k : ℕ} {d d' : Fin k → ℕ+} (h : d = d')
    (T : KTensor F d) : tensorRank (h ▸ T) = tensorRank T := by
  subst h; rfl

/-! ## Restriction monotonicity of tensor rank (Christandl-Hoeberechts-Nieuwboer-
Vrana-Zuiddam tex:398 + tex:402)

Paper tex:402 verbatim: "Tensor rank `R(T)` is defined as the smallest number `r`
such that `T` can be written as a sum of `r` simple tensors `u ⊗ v ⊗ w`."

Paper tex:392 verbatim: "For two `k`-tensors `S` and `T` we say `S` is a
restriction of `T` and write `S ≤ T` if there are linear maps `A_i` such that
`S = (A_1 ⊗ ⋯ ⊗ A_k) T`."

The fundamental restriction-monotonicity of tensor rank (standard fact, used
implicitly throughout the paper, e.g. in the proof of Cor 2.6 tex:762-773):
if `S = (A_1 ⊗ ⋯ ⊗ A_k) T`, then `R(S) ≤ R(T)`.

Proof: take any decomposition `T = ∑_{ℓ=1}^r simpleTensor u_ℓ`. Then
`S = (A_1 ⊗ ⋯ ⊗ A_k) ∑_ℓ simpleTensor u_ℓ = ∑_ℓ (A_1 ⊗ ⋯ ⊗ A_k) simpleTensor u_ℓ`.
The image of a simple tensor under a leg-wise linear map is again simple:
`(A_1 ⊗ ⋯ ⊗ A_k) (u_1 ⊗ ⋯ ⊗ u_k) = (A_1 u_1) ⊗ ⋯ ⊗ (A_k u_k)`. Hence `S` admits a
decomposition into `r` simple tensors. -/

/-- The image of `simpleTensor u : KTensor F dT` under the leg-wise linear maps
    `A i : Matrix (Fin (dS i)) (Fin (dT i)) F` is again a simple tensor, namely
    `simpleTensor (fun i j => ∑ a, A i j a * u i a)`.

    Paper tex:392: "linear maps `A_i` such that `S = (A_1 ⊗ ⋯ ⊗ A_k) T`." -/
private lemma simpleTensor_restriction_image {k : ℕ} {dS dT : Fin k → ℕ+}
    (A : ∀ i : Fin k, Matrix (Fin (dS i)) (Fin (dT i)) F)
    (u : (i : Fin k) → Fin (dT i) → F) :
    (fun jdx : (∀ i : Fin k, Fin (dS i)) =>
        ∑ idx : (∀ i : Fin k, Fin (dT i)),
          (∏ i, A i (jdx i) (idx i)) * simpleTensor (F := F) (d := dT) u idx)
      = simpleTensor (F := F) (d := dS)
          (fun i j => ∑ a : Fin (dT i), A i j a * u i a) := by
  classical
  funext jdx
  -- Unfold simpleTensor u idx = ∏ i, u i (idx i).
  simp only [simpleTensor]
  -- Multiply: (∏ i, A i (jdx i) (idx i)) * (∏ i, u i (idx i))
  --   = ∏ i, (A i (jdx i) (idx i) * u i (idx i)).
  have h_mul_combine :
      ∀ idx : (∀ i : Fin k, Fin (dT i)),
        (∏ i, A i (jdx i) (idx i)) * (∏ i, u i (idx i))
          = ∏ i, A i (jdx i) (idx i) * u i (idx i) := by
    intro idx
    rw [← Finset.prod_mul_distrib]
  simp_rw [h_mul_combine]
  -- Goal: ∑ idx, ∏ i, A i (jdx i) (idx i) * u i (idx i)
  --     = ∏ i, ∑ a, A i (jdx i) a * u i a.
  -- This is the product-over-sum identity (`Finset.prod_univ_sum` on Pi types).
  rw [show (∏ i : Fin k, ∑ a : Fin (dT i), A i (jdx i) a * u i a)
      = ∑ idx : (∀ i : Fin k, Fin (dT i)),
          ∏ i, A i (jdx i) (idx i) * u i (idx i) from ?_]
  -- The forward direction of the product-over-sum identity.
  have hprod_sum :
      (∏ i : Fin k, ∑ a : Fin (dT i), A i (jdx i) a * u i a)
        = ∑ p ∈ Fintype.piFinset (fun i : Fin k => (Finset.univ : Finset (Fin (dT i)))),
            ∏ i, A i (jdx i) (p i) * u i (p i) := by
    rw [Finset.prod_univ_sum]
  rw [hprod_sum]
  -- `Fintype.piFinset (fun i => univ)` equals `(univ : Finset (∀ i, Fin (dT i)))`.
  rw [show
      Fintype.piFinset (fun i : Fin k => (Finset.univ : Finset (Fin (dT i))))
        = (Finset.univ : Finset (∀ i : Fin k, Fin (dT i))) from by
    ext idx
    simp]

/-- **Restriction-monotonicity of tensor rank** (Christandl-Hoeberechts-Nieuwboer-
    Vrana-Zuiddam tex:398 + tex:402).

    Paper tex:398: `S` is a restriction of `T` iff `S = (A_1 ⊗ ⋯ ⊗ A_k) T` for
    some leg-wise linear maps `A_i`.

    Paper tex:396: `R(T)` is the smallest `r` such that `T` is a sum of `r`
    simple tensors.

    The standard restriction-monotonicity used in the paper (e.g. implicit
    in the proof of Cor 2.6 tex:762-773, and explicit in the definition of a
    spectral point tex:781 (Strassen monotonicity)): `S ≤ T → R(S) ≤ R(T)`.

    Proof: write `T = ∑_{ℓ=1}^r simpleTensor u_ℓ`. By
    `simpleTensor_restriction_image`, applying the leg-wise linear maps `A_i`
    to each `simpleTensor u_ℓ` yields a simple tensor of the format `dS`.
    Summing gives `S = ∑_{ℓ=1}^r simpleTensor v_ℓ` with the same number `r`
    of simple summands, hence `R(S) ≤ r`. -/
lemma tensorRank_mono_under_Restricts {k : ℕ} (hk : 1 ≤ k) {dS dT : Fin k → ℕ+}
    {S : KTensor F dS} {T : KTensor F dT} (h : Restricts S T) :
    tensorRank S ≤ tensorRank T := by
  classical
  obtain ⟨A, hSeq⟩ := h
  -- Pull a tensor-rank decomposition out of T.
  have hT_mem : tensorRank T ∈
      { r : ℕ | ∃ s : Fin r → KTensor F dT,
          (∀ i, IsSimpleTensor (s i)) ∧ T = ∑ i, s i } := by
    apply Nat.sInf_mem
    obtain ⟨rT, sT, hsT, hT⟩ := exists_tensorRank_decomp hk T
    exact ⟨rT, sT, hsT, hT⟩
  obtain ⟨sT, hsT, hT⟩ := hT_mem
  -- Build a decomposition of S using `simpleTensor_restriction_image` on each summand.
  -- For each ℓ : Fin (tensorRank T), pick `u_ℓ` with `sT ℓ = simpleTensor u_ℓ`.
  have huPick : ∀ ℓ : Fin (tensorRank T),
      ∃ u : (i : Fin k) → Fin (dT i) → F, sT ℓ = simpleTensor (F := F) (d := dT) u := by
    intro ℓ
    obtain ⟨u, hu⟩ := hsT ℓ
    exact ⟨u, hu⟩
  -- For each ℓ, define v_ℓ : (∀ i, Fin (dS i) → F) such that the image of sT ℓ
  -- under (A_1 ⊗ ⋯ ⊗ A_k) is simpleTensor v_ℓ.
  set v : Fin (tensorRank T) → (i : Fin k) → Fin (dS i) → F := fun ℓ i j =>
    ∑ a : Fin (dT i), A i j a * (Classical.choose (huPick ℓ)) i a with hv_def
  -- The decomposition: S = ∑_ℓ simpleTensor (v ℓ).
  refine Nat.sInf_le ?_
  refine ⟨fun ℓ => simpleTensor (F := F) (d := dS) (v ℓ), ?_, ?_⟩
  · intro ℓ; exact ⟨v ℓ, rfl⟩
  · -- S jdx = ∑ idx, (∏ i, A i (jdx i) (idx i)) * T idx
    --       = ∑ idx, (∏ i, A i (jdx i) (idx i)) * (∑ ℓ, simpleTensor u_ℓ idx)
    --       = ∑ ℓ, ∑ idx, (∏ i, A i (jdx i) (idx i)) * simpleTensor u_ℓ idx
    --       = ∑ ℓ, simpleTensor (v ℓ) jdx          (by simpleTensor_restriction_image).
    funext jdx
    rw [hSeq jdx]
    -- Rewrite T idx via hT.
    have hT_pt : ∀ idx, T idx = ∑ ℓ, sT ℓ idx := by
      intro idx
      have := congr_fun hT idx
      simpa using this
    -- Substitute T idx = ∑ ℓ, sT ℓ idx into the LHS via Finset.sum_congr.
    rw [show ∑ idx : (∀ i, Fin (dT i)), (∏ i, A i (jdx i) (idx i)) * T idx
        = ∑ idx : (∀ i, Fin (dT i)), (∏ i, A i (jdx i) (idx i)) *
            (∑ ℓ, sT ℓ idx) from
      Finset.sum_congr rfl (fun idx _ => by rw [hT_pt idx])]
    -- Distribute the product over the inner sum.
    rw [show ∑ idx : (∀ i, Fin (dT i)), (∏ i, A i (jdx i) (idx i)) *
            (∑ ℓ, sT ℓ idx)
          = ∑ idx : (∀ i, Fin (dT i)), ∑ ℓ,
              (∏ i, A i (jdx i) (idx i)) * sT ℓ idx from
      Finset.sum_congr rfl (fun idx _ => Finset.mul_sum _ _ _)]
    -- Swap sums: ∑ idx, ∑ ℓ, _  =  ∑ ℓ, ∑ idx, _.
    rw [Finset.sum_comm]
    -- Now LHS = ∑ ℓ, ∑ idx, (∏ i, A i (jdx i) (idx i)) * sT ℓ idx.
    -- Each inner sum equals simpleTensor (v ℓ) jdx by simpleTensor_restriction_image.
    rw [show (∑ ℓ : Fin (tensorRank T), simpleTensor (F := F) (d := dS) (v ℓ)) jdx
        = ∑ ℓ : Fin (tensorRank T), simpleTensor (F := F) (d := dS) (v ℓ) jdx from
      Finset.sum_apply jdx _ _]
    refine Finset.sum_congr rfl ?_
    intro ℓ _
    -- Use the choice for ℓ.
    have hu_ℓ : sT ℓ = simpleTensor (F := F) (d := dT) (Classical.choose (huPick ℓ)) :=
      Classical.choose_spec (huPick ℓ)
    -- Rewrite sT ℓ idx via hu_ℓ pointwise inside the inner sum.
    have h_sT_pt : ∀ idx, sT ℓ idx =
        simpleTensor (F := F) (d := dT) (Classical.choose (huPick ℓ)) idx :=
      fun idx => congr_fun hu_ℓ idx
    rw [show ∑ idx : (∀ i, Fin (dT i)), (∏ i, A i (jdx i) (idx i)) * sT ℓ idx
        = ∑ idx : (∀ i, Fin (dT i)), (∏ i, A i (jdx i) (idx i)) *
            simpleTensor (F := F) (d := dT) (Classical.choose (huPick ℓ)) idx from
      Finset.sum_congr rfl (fun idx _ => by rw [h_sT_pt idx])]
    -- Apply simpleTensor_restriction_image.
    have himg := simpleTensor_restriction_image (F := F) (dS := dS) (dT := dT) A
      (Classical.choose (huPick ℓ))
    have hval := congr_fun himg jdx
    -- Both sides match `v ℓ` by definition: `v ℓ i j = ∑ a, A i j a * (choose ℓ) i a`.
    exact hval

end Semicontinuity
