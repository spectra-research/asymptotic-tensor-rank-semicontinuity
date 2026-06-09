/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.MaxRankBound

/-!
# Tensor base change under a field extension (Strassen 1988, Theorem 3.10)

Source: **Strassen 1988, Theorem 3.10** (`texbooks/strassen1988/strassen1988.tex:1264`).

For a field extension `K / F` and a `k`-tensor `T` over `F`, base change lifts `T`
to a `k`-tensor `T_K` over `K` by applying `algebraMap F K` entrywise. This file
provides the base-change functor on the project's `KTensor` type and proves the
**easy direction** of Strassen 1988 Theorem 3.10:

> if `S ≤ T` over `F` (restriction), then `S_K ≤ T_K` over `K`.

Concretely, restriction is realized via leg-wise matrices `A_i` over `F`; base
change `algebraMap`s those matrices entrywise, and the Kronecker-product
restriction equation is preserved because `algebraMap` is a ring homomorphism
(`map_sum`, `map_prod`, `map_mul`).

## Main results

* `KTensor.baseChange` — the base-change functor `KTensor F d → KTensor K d`.
* `KTensor.baseChange_kron` / `baseChange_directSum` — base change commutes with
  the Kronecker product `⊠` and direct sum `⊕ₜ`.
* `KTensor.baseChange_unitTensor` / `baseChange_unitPairTensor` — base change
  preserves the unit and pair-unit tensors.
* `KTensor.baseChange_restricts` — **Theorem 3.10, easy direction**: restriction
  over `F` implies restriction over `K`.
* `KTensor.baseChange_injective` — base change is injective (field extension).

The **converse** (a `K`-restriction descends to an `F`-restriction, so that the
restriction preorder is unchanged under field extension) is the hard direction,
resting on **Strassen 1987, Proposition 5.3(i)**, and is deferred — it is NOT
formalized here.
-/

namespace Semicontinuity

universe u

variable {F : Type u} [Field F] {K : Type u} [Field K] [Algebra F K] {k : ℕ}

/-- **Base change** of a `k`-tensor from `F` to `K`: apply `algebraMap F K`
    entrywise (Strassen 1988, tex:1264). -/
def KTensor.baseChange {d : Fin k → ℕ+} (T : KTensor F d) : KTensor K d :=
  fun idx => algebraMap F K (T idx)

@[simp] lemma KTensor.baseChange_apply {d : Fin k → ℕ+} (T : KTensor F d)
    (idx : ∀ i : Fin k, Fin (d i)) :
    (T.baseChange (K := K)) idx = algebraMap F K (T idx) := rfl

/-- Base change commutes with the Kronecker product `⊠` (tex:393).
    `algebraMap` of a product of leg values is the product of `algebraMap`s. -/
theorem KTensor.baseChange_kron {dS dT : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT) :
    (S ⊠ T).baseChange (K := K) = S.baseChange ⊠ T.baseChange := by
  funext idx
  simp only [KTensor.baseChange, kroneckerTensor, map_mul]

/-- Base change commutes with the direct sum `⊕ₜ`. Mirror the dependent
    block-selection `by_cases` of `directSumTensor`; the off-diagonal `0` is
    preserved by `map_zero`. -/
theorem KTensor.baseChange_directSum {dS dT : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT) :
    (S ⊕ₜ T).baseChange (K := K) = S.baseChange ⊕ₜ T.baseChange := by
  classical
  funext idx
  simp only [KTensor.baseChange, directSumTensor]
  by_cases hSL : ∀ i, (idx i).val < (dS i : ℕ)
  · rw [dif_pos hSL, dif_pos hSL]
  · by_cases hTL : ∀ i, (dS i : ℕ) ≤ (idx i).val
    · rw [dif_neg hSL, dif_pos hTL, dif_neg hSL, dif_pos hTL]
    · rw [dif_neg hSL, dif_neg hTL, dif_neg hSL, dif_neg hTL, map_zero]

/-- Base change preserves the rank-`r` unit tensor `⟨r⟩` (tex:396).
    `algebraMap` sends `1 ↦ 1` and `0 ↦ 0`. -/
theorem KTensor.baseChange_unitTensor (r : ℕ+) :
    (unitTensor F (k := k) r).baseChange (K := K) = unitTensor K (k := k) r := by
  funext idx
  simp only [KTensor.baseChange, unitTensor]
  split
  · rw [map_one]
  · rw [map_zero]

/-- Base change preserves the pair-unit tensor `⟨r⟩_{i,j}` (tex:836). -/
theorem KTensor.baseChange_unitPairTensor (r : ℕ+) (i j : Fin k) (hij : i ≠ j) :
    (unitPairTensor (F := F) r i j hij).baseChange (K := K)
      = unitPairTensor (F := K) r i j hij := by
  funext idx
  simp only [KTensor.baseChange, unitPairTensor]
  split
  · rw [map_one]
  · rw [map_zero]

/-- **Strassen 1988, Theorem 3.10 (easy direction)** (tex:1264).

    If `S` restricts to `T` over `F`, then the base changes `S_K` and `T_K`
    satisfy `S_K ≤ T_K` over `K`. The leg-wise matrices are obtained by
    `algebraMap`-ing the `F`-matrices entrywise; the Kronecker-product
    restriction equation is preserved because `algebraMap` is a ring
    homomorphism (`map_sum`, `map_prod`, `map_mul`). -/
theorem KTensor.baseChange_restricts {dS dT : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT)
    (h : Restricts S T) :
    Restricts (S.baseChange (K := K)) (T.baseChange (K := K)) := by
  obtain ⟨A, hA⟩ := h
  refine ⟨fun i a b => algebraMap F K (A i a b), ?_⟩
  intro jdx
  simp only [KTensor.baseChange]
  rw [hA jdx, map_sum]
  refine Finset.sum_congr rfl ?_
  intro idx _
  rw [map_mul, map_prod]

/-- Base change is injective: for a field extension `K / F`, `algebraMap F K` is
    injective, so base change is injective entrywise. -/
theorem KTensor.baseChange_injective {d : Fin k → ℕ+} :
    Function.Injective (KTensor.baseChange (F := F) (K := K) (d := d)) := by
  intro S T hST
  funext idx
  have := congrFun hST idx
  simp only [KTensor.baseChange] at this
  exact (algebraMap F K).injective this

end Semicontinuity
