/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.SpectrumDescend

/-!
# The commutative semiring of `KTensor`-classes modulo restriction-equivalence

This file builds the foundational algebraic object of the Strassen-duality
bridge: the commutative semiring `TensorClass F k` of `k`-tensors over a field
`F`, of arbitrary format, modulo restriction-equivalence `∼ₜ`, with `+` given by
the direct sum `⊕ₜ` and `*` by the Kronecker product `⊠`.

* `∼ₜ` is an equivalence relation on the sigma type
  `TT := Σ d, KTensor F d`, and `⊕ₜ`/`⊠` are `∼ₜ`-congruences
  (`Restricts.directSum_congr`, `Restricts.kron_congr` and the `∼ₜ` corollaries).
* the structural `∼ₜ` identities (commutativity, associativity,
  units, distributivity).
* the quotient `CommSemiring (TensorClass F k)`.

Source for the operations: `MaxRankBound.lean` (`Restricts`, `kroneckerTensor`,
`directSumTensor`, `unitTensor`) and `SpectrumDescend.lean` (`RestrictsEquiv`).
-/

namespace Semicontinuity

universe u

variable {F : Type u} [Field F] {k : ℕ}

/-! ## `∼ₜ` is an equivalence; `⊕ₜ`/`⊠` are `∼ₜ`-congruences. -/

/-- Value of `directSumTensor S T` at a multi-index, split by block (specialization of
the private lemma in `SpectrumDescend.lean`). -/
lemma directSumTensor_apply_block' {dS dT : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT)
    (idx : ∀ i : Fin k, Fin ((dS i + dT i : ℕ+) : ℕ)) :
    (directSumTensor (F := F) S T idx
      = if hS : ∀ i, (idx i).val < (dS i : ℕ) then S (fun i => ⟨(idx i).val, hS i⟩)
        else if hT : ∀ i, (dS i : ℕ) ≤ (idx i).val then
          T (fun i => ⟨(idx i).val - (dS i : ℕ), by
            have h1 : (idx i).val < ((dS i + dT i : ℕ+) : ℕ) := (idx i).isLt
            have h2 : ((dS i + dT i : ℕ+) : ℕ) = (dS i : ℕ) + (dT i : ℕ) := PNat.add_coe _ _
            have := hT i; omega⟩)
        else 0) := by
  classical
  unfold directSumTensor
  by_cases hS : ∀ i, (idx i).val < (dS i : ℕ)
  · simp only [dif_pos hS]
  · by_cases hT : ∀ i, (dS i : ℕ) ≤ (idx i).val
    · simp only [dif_neg hS, dif_pos hT]
    · simp only [dif_neg hS, dif_neg hT]

/-- Left block-embedding of a `dT₁`-index into a `(dT₁ + dT₂)`-index. -/
def dsumEmbLeft {d₁ d₂ : Fin k → ℕ+}
    (w : ∀ i : Fin k, Fin (d₁ i)) (i : Fin k) :
    Fin ((d₁ i + d₂ i : ℕ+) : ℕ) :=
  ⟨(w i).val, by
    have h1 : (w i).val < (d₁ i : ℕ) := (w i).isLt
    have h2 : ((d₁ i + d₂ i : ℕ+) : ℕ) = (d₁ i : ℕ) + (d₂ i : ℕ) := PNat.add_coe _ _
    omega⟩

/-- Right block-embedding of a `dT₂`-index into a `(dT₁ + dT₂)`-index. -/
def dsumEmbRight {d₁ d₂ : Fin k → ℕ+}
    (w : ∀ i : Fin k, Fin (d₂ i)) (i : Fin k) :
    Fin ((d₁ i + d₂ i : ℕ+) : ℕ) :=
  ⟨(d₁ i : ℕ) + (w i).val, by
    have h1 : (w i).val < (d₂ i : ℕ) := (w i).isLt
    have h2 : ((d₁ i + d₂ i : ℕ+) : ℕ) = (d₁ i : ℕ) + (d₂ i : ℕ) := PNat.add_coe _ _
    omega⟩

/-- The block-diagonal leg matrix `A i ⊕ B i` on leg `i`, used to witness
`Restricts.directSum_congr`. -/
noncomputable def dsumLegMatrix {dS₁ dT₁ dS₂ dT₂ : Fin k → ℕ+}
    (A : ∀ i : Fin k, Matrix (Fin (dS₁ i)) (Fin (dT₁ i)) F)
    (B : ∀ i : Fin k, Matrix (Fin (dS₂ i)) (Fin (dT₂ i)) F) (i : Fin k) :
    Matrix (Fin ((dS₁ i + dS₂ i : ℕ+) : ℕ)) (Fin ((dT₁ i + dT₂ i : ℕ+) : ℕ)) F :=
  fun a b =>
    if ha : (a : ℕ) < (dS₁ i : ℕ) then
      (if hb : (b : ℕ) < (dT₁ i : ℕ) then A i ⟨a, ha⟩ ⟨b, hb⟩ else 0)
    else
      (if hb : (dT₁ i : ℕ) ≤ (b : ℕ) then
        B i ⟨(a : ℕ) - (dS₁ i : ℕ), by
          have h2 : ((dS₁ i + dS₂ i : ℕ+) : ℕ) = (dS₁ i : ℕ) + (dS₂ i : ℕ) := PNat.add_coe _ _
          omega⟩
          ⟨(b : ℕ) - (dT₁ i : ℕ), by
          have h2 : ((dT₁ i + dT₂ i : ℕ+) : ℕ) = (dT₁ i : ℕ) + (dT₂ i : ℕ) := PNat.add_coe _ _
          omega⟩
        else 0)

/-- Value of the block leg-matrix on the left block (both indices `< dT₁`/`< dS₁`). -/
lemma dsumLegMatrix_left {dS₁ dT₁ dS₂ dT₂ : Fin k → ℕ+}
    (A : ∀ i : Fin k, Matrix (Fin (dS₁ i)) (Fin (dT₁ i)) F)
    (B : ∀ i : Fin k, Matrix (Fin (dS₂ i)) (Fin (dT₂ i)) F) (i : Fin k)
    {a : Fin ((dS₁ i + dS₂ i : ℕ+) : ℕ)} {b : Fin ((dT₁ i + dT₂ i : ℕ+) : ℕ)}
    (ha : (a : ℕ) < (dS₁ i : ℕ)) (hb : (b : ℕ) < (dT₁ i : ℕ)) :
    dsumLegMatrix A B i a b = A i ⟨a, ha⟩ ⟨b, hb⟩ := by
  simp only [dsumLegMatrix, dif_pos ha, dif_pos hb]

/-- The block leg-matrix is `0` when the row is in the left block but the column
in the right block. -/
lemma dsumLegMatrix_left_right_zero {dS₁ dT₁ dS₂ dT₂ : Fin k → ℕ+}
    (A : ∀ i : Fin k, Matrix (Fin (dS₁ i)) (Fin (dT₁ i)) F)
    (B : ∀ i : Fin k, Matrix (Fin (dS₂ i)) (Fin (dT₂ i)) F) (i : Fin k)
    {a : Fin ((dS₁ i + dS₂ i : ℕ+) : ℕ)} {b : Fin ((dT₁ i + dT₂ i : ℕ+) : ℕ)}
    (ha : (a : ℕ) < (dS₁ i : ℕ)) (hb : (dT₁ i : ℕ) ≤ (b : ℕ)) :
    dsumLegMatrix A B i a b = 0 := by
  simp only [dsumLegMatrix, dif_pos ha, dif_neg (by omega : ¬ (b : ℕ) < (dT₁ i : ℕ))]

/-- Value of the block leg-matrix on the right block. -/
lemma dsumLegMatrix_right {dS₁ dT₁ dS₂ dT₂ : Fin k → ℕ+}
    (A : ∀ i : Fin k, Matrix (Fin (dS₁ i)) (Fin (dT₁ i)) F)
    (B : ∀ i : Fin k, Matrix (Fin (dS₂ i)) (Fin (dT₂ i)) F) (i : Fin k)
    {a : Fin ((dS₁ i + dS₂ i : ℕ+) : ℕ)} {b : Fin ((dT₁ i + dT₂ i : ℕ+) : ℕ)}
    (ha : (dS₁ i : ℕ) ≤ (a : ℕ)) (hb : (dT₁ i : ℕ) ≤ (b : ℕ)) :
    dsumLegMatrix A B i a b
      = B i ⟨(a : ℕ) - (dS₁ i : ℕ), by
          have h2 : ((dS₁ i + dS₂ i : ℕ+) : ℕ) = (dS₁ i : ℕ) + (dS₂ i : ℕ) := PNat.add_coe _ _
          omega⟩
        ⟨(b : ℕ) - (dT₁ i : ℕ), by
          have h2 : ((dT₁ i + dT₂ i : ℕ+) : ℕ) = (dT₁ i : ℕ) + (dT₂ i : ℕ) := PNat.add_coe _ _
          omega⟩ := by
  simp only [dsumLegMatrix, dif_neg (by omega : ¬ (a : ℕ) < (dS₁ i : ℕ)), dif_pos hb]

/-- The block leg-matrix is `0` when the row is in the right block but the column
in the left block. -/
lemma dsumLegMatrix_right_left_zero {dS₁ dT₁ dS₂ dT₂ : Fin k → ℕ+}
    (A : ∀ i : Fin k, Matrix (Fin (dS₁ i)) (Fin (dT₁ i)) F)
    (B : ∀ i : Fin k, Matrix (Fin (dS₂ i)) (Fin (dT₂ i)) F) (i : Fin k)
    {a : Fin ((dS₁ i + dS₂ i : ℕ+) : ℕ)} {b : Fin ((dT₁ i + dT₂ i : ℕ+) : ℕ)}
    (ha : (dS₁ i : ℕ) ≤ (a : ℕ)) (hb : (b : ℕ) < (dT₁ i : ℕ)) :
    dsumLegMatrix A B i a b = 0 := by
  simp only [dsumLegMatrix, dif_neg (by omega : ¬ (a : ℕ) < (dS₁ i : ℕ)),
    dif_neg (by omega : ¬ (dT₁ i : ℕ) ≤ (b : ℕ))]

/-- **Restriction monotonicity of the direct sum** (reusable core).

If `S₁ ≤ₜ T₁` and `S₂ ≤ₜ T₂` then `S₁ ⊕ₜ S₂ ≤ₜ T₁ ⊕ₜ T₂`, via the
block-diagonal leg matrices `A i ⊕ B i` (the witness matrices for the two
restrictions placed in the top-left / bottom-right blocks). -/
lemma Restricts.directSum_congr {dS₁ dT₁ dS₂ dT₂ : Fin k → ℕ+}
    {S₁ : KTensor F dS₁} {T₁ : KTensor F dT₁}
    {S₂ : KTensor F dS₂} {T₂ : KTensor F dT₂}
    (h₁ : Restricts S₁ T₁) (h₂ : Restricts S₂ T₂) :
    Restricts (S₁ ⊕ₜ S₂) (T₁ ⊕ₜ T₂) := by
  classical
  obtain ⟨A, hA⟩ := h₁
  obtain ⟨B, hB⟩ := h₂
  refine ⟨dsumLegMatrix A B, ?_⟩
  intro jdx
  have hcS : ∀ i : Fin k, ((dS₁ i + dS₂ i : ℕ+) : ℕ) = (dS₁ i : ℕ) + (dS₂ i : ℕ) :=
    fun i => PNat.add_coe _ _
  have hcT : ∀ i : Fin k, ((dT₁ i + dT₂ i : ℕ+) : ℕ) = (dT₁ i : ℕ) + (dT₂ i : ℕ) :=
    fun i => PNat.add_coe _ _
  rw [directSumTensor_apply_block']
  by_cases hSL : ∀ i, (jdx i).val < (dS₁ i : ℕ)
  · -- jdx all in S₁-block: reduce RHS to the `dT₁`-block sum and apply `hA`.
    simp only [dif_pos hSL]
    rw [hA (fun i => ⟨(jdx i).val, hSL i⟩)]
    rw [← Finset.sum_subset
      (Finset.subset_univ ((Finset.univ : Finset (∀ i, Fin (dT₁ i))).image dsumEmbLeft))]
    · rw [Finset.sum_image]
      · refine Finset.sum_congr rfl ?_
        intro w _
        congr 1
        · refine Finset.prod_congr rfl ?_
          intro i _
          have hlt : ((dsumEmbLeft (d₁ := dT₁) (d₂ := dT₂) w i) : ℕ) < (dT₁ i : ℕ) := by
            simp only [dsumEmbLeft]; exact (w i).isLt
          rw [dsumLegMatrix_left A B i (hSL i) hlt]; rfl
        · rw [directSumTensor_apply_block']
          have hall : ∀ i, ((dsumEmbLeft (d₁ := dT₁) (d₂ := dT₂) w i) : ℕ) < (dT₁ i : ℕ) := by
            intro i; simp only [dsumEmbLeft]; exact (w i).isLt
          simp only [dif_pos hall]
          rfl
      · intro x _ y _ hxy
        funext i
        have := congrArg (fun f => (f i).val) hxy
        simp only [dsumEmbLeft] at this
        exact Fin.ext this
    · intro idx _ hidx
      have hnotleft : ¬ ∀ i, (idx i).val < (dT₁ i : ℕ) := by
        intro hall
        apply hidx
        refine Finset.mem_image.2 ⟨fun i => ⟨(idx i).val, hall i⟩, Finset.mem_univ _, ?_⟩
        funext i; apply Fin.ext; rfl
      push_neg at hnotleft
      obtain ⟨i₀, hi₀⟩ := hnotleft
      have hzero : dsumLegMatrix A B i₀ (jdx i₀) (idx i₀) = 0 :=
        dsumLegMatrix_left_right_zero A B i₀ (hSL i₀) (by omega)
      rw [Finset.prod_eq_zero (Finset.mem_univ i₀) hzero, zero_mul]
  · by_cases hTL : ∀ i, (dS₁ i : ℕ) ≤ (jdx i).val
    · -- jdx all in S₂-block: reduce RHS to the `dT₂`-block sum and apply `hB`.
      simp only [dif_neg hSL, dif_pos hTL]
      rw [hB (fun i => ⟨(jdx i).val - (dS₁ i : ℕ), by
        have h1 : (jdx i).val < ((dS₁ i + dS₂ i : ℕ+) : ℕ) := (jdx i).isLt
        have := hTL i; have := hcS i; omega⟩)]
      rw [← Finset.sum_subset
        (Finset.subset_univ ((Finset.univ : Finset (∀ i, Fin (dT₂ i))).image dsumEmbRight))]
      · rw [Finset.sum_image]
        · refine Finset.sum_congr rfl ?_
          intro w _
          congr 1
          · refine Finset.prod_congr rfl ?_
            intro i _
            have hge : (dT₁ i : ℕ) ≤ ((dsumEmbRight (d₁ := dT₁) (d₂ := dT₂) w i) : ℕ) := by
              simp only [dsumEmbRight]; omega
            rw [dsumLegMatrix_right A B i (hTL i) hge]
            congr 1
            apply Fin.ext; simp only [dsumEmbRight]; omega
          · rw [directSumTensor_apply_block']
            -- `hSL` failing gives a leg `i₀`; on it `dsumEmbRight ≥ dT₁`.
            obtain ⟨i₀, _⟩ := not_forall.1 hSL
            have hnotleft : ¬ ∀ i,
                ((dsumEmbRight (d₁ := dT₁) (d₂ := dT₂) w i) : ℕ) < (dT₁ i : ℕ) := by
              intro hall
              have := hall i₀
              simp only [dsumEmbRight] at this
              omega
            have hright : ∀ i, (dT₁ i : ℕ) ≤
                ((dsumEmbRight (d₁ := dT₁) (d₂ := dT₂) w i) : ℕ) := by
              intro i; simp only [dsumEmbRight]; omega
            rw [dif_neg hnotleft, dif_pos hright]
            congr 1; funext i; apply Fin.ext; simp only [dsumEmbRight]; omega
        · intro x _ y _ hxy
          funext i
          have := congrArg (fun f => (f i).val) hxy
          simp only [dsumEmbRight] at this
          exact Fin.ext (by omega)
      · intro idx _ hidx
        have hnotright : ¬ ∀ i, (dT₁ i : ℕ) ≤ (idx i).val := by
          intro hall
          apply hidx
          refine Finset.mem_image.2
            ⟨fun i => ⟨(idx i).val - (dT₁ i : ℕ), by
              have h1 : (idx i).val < ((dT₁ i + dT₂ i : ℕ+) : ℕ) := (idx i).isLt
              have := hall i; have := hcT i; omega⟩, Finset.mem_univ _, ?_⟩
          funext i; apply Fin.ext; simp only [dsumEmbRight]; have := hall i; omega
        push_neg at hnotright
        obtain ⟨i₀, hi₀⟩ := hnotright
        have hzero : dsumLegMatrix A B i₀ (jdx i₀) (idx i₀) = 0 :=
          dsumLegMatrix_right_left_zero A B i₀ (hTL i₀) (by omega)
        rw [Finset.prod_eq_zero (Finset.mem_univ i₀) hzero, zero_mul]
    · -- jdx mixed: LHS = 0, and every RHS term vanishes (idx forced mixed).
      simp only [dif_neg hSL, dif_neg hTL]
      symm
      apply Finset.sum_eq_zero
      intro idx _
      push_neg at hSL hTL
      obtain ⟨iL, hiL⟩ := hTL
      obtain ⟨iR, hiR⟩ := hSL
      rw [directSumTensor_apply_block']
      by_cases hidxL : ∀ i, (idx i).val < (dT₁ i : ℕ)
      · -- idx all-left, but jdx leg iR is right ⟹ M iR = 0.
        have hzero : dsumLegMatrix A B iR (jdx iR) (idx iR) = 0 :=
          dsumLegMatrix_right_left_zero A B iR hiR (hidxL iR)
        simp only [dif_pos hidxL]
        rw [Finset.prod_eq_zero (Finset.mem_univ iR) hzero, zero_mul]
      · by_cases hidxR : ∀ i, (dT₁ i : ℕ) ≤ (idx i).val
        · -- idx all-right, but jdx leg iL is left ⟹ M iL = 0.
          have hzero : dsumLegMatrix A B iL (jdx iL) (idx iL) = 0 :=
            dsumLegMatrix_left_right_zero A B iL hiL (hidxR iL)
          simp only [dif_neg hidxL, dif_pos hidxR]
          rw [Finset.prod_eq_zero (Finset.mem_univ iL) hzero, zero_mul]
        · simp only [dif_neg hidxL, dif_neg hidxR, mul_zero]

/-- Left decode of a grouped Kronecker leg-index `Fin (d₁ * d₂)`. -/
def kronDecodeL {d₁ d₂ : ℕ+} (a : Fin ((d₁ * d₂ : ℕ+) : ℕ)) : Fin (d₁ : ℕ) :=
  (finProdFinEquiv.symm (Fin.cast (by rw [PNat.mul_coe]) a)).1

/-- Right decode of a grouped Kronecker leg-index `Fin (d₁ * d₂)`. -/
def kronDecodeR {d₁ d₂ : ℕ+} (a : Fin ((d₁ * d₂ : ℕ+) : ℕ)) : Fin (d₂ : ℕ) :=
  (finProdFinEquiv.symm (Fin.cast (by rw [PNat.mul_coe]) a)).2

/-- The pair `(kronDecodeL, kronDecodeR)` is a bijection onto `Fin d₁ × Fin d₂`. -/
def kronDecodeEquiv {d₁ d₂ : ℕ+} :
    Fin ((d₁ * d₂ : ℕ+) : ℕ) ≃ Fin (d₁ : ℕ) × Fin (d₂ : ℕ) :=
  (finCongr (by rw [PNat.mul_coe])).trans finProdFinEquiv.symm

lemma kronDecodeEquiv_apply {d₁ d₂ : ℕ+} (a : Fin ((d₁ * d₂ : ℕ+) : ℕ)) :
    kronDecodeEquiv a = (kronDecodeL a, kronDecodeR a) := rfl

/-- `kronDecodeL` on a leg of a tuple agrees with `kronLeftIndex`. -/
lemma kronDecodeL_eq_kronLeftIndex {dS dT : Fin k → ℕ+}
    (idx : ∀ i : Fin k, Fin ((dS i * dT i : ℕ+) : ℕ)) (i : Fin k) :
    kronDecodeL (idx i) = kronLeftIndex idx i := by
  apply Fin.ext
  simp only [kronDecodeL, kronLeftIndex, finProdFinEquiv_symm_apply, Fin.coe_divNat, Fin.val_cast]

/-- `kronDecodeR` on a leg of a tuple agrees with `kronRightIndex`. -/
lemma kronDecodeR_eq_kronRightIndex {dS dT : Fin k → ℕ+}
    (idx : ∀ i : Fin k, Fin ((dS i * dT i : ℕ+) : ℕ)) (i : Fin k) :
    kronDecodeR (idx i) = kronRightIndex idx i := by
  apply Fin.ext
  simp only [kronDecodeR, kronRightIndex, finProdFinEquiv_symm_apply, Fin.coe_modNat, Fin.val_cast]

/-- `.val`-level formula for `kronDecodeL`: the quotient of the right dimension. -/
lemma kronDecodeL_val {d₁ d₂ : ℕ+} (a : Fin ((d₁ * d₂ : ℕ+) : ℕ)) :
    (kronDecodeL a : ℕ) = a.val / (d₂ : ℕ) := by
  simp only [kronDecodeL, finProdFinEquiv_symm_apply, Fin.coe_divNat, Fin.val_cast, PNat.mul_coe]

/-- `.val`-level formula for `kronDecodeR`: the remainder by the right dimension. -/
lemma kronDecodeR_val {d₁ d₂ : ℕ+} (a : Fin ((d₁ * d₂ : ℕ+) : ℕ)) :
    (kronDecodeR a : ℕ) = a.val % (d₂ : ℕ) := by
  simp only [kronDecodeR, finProdFinEquiv_symm_apply, Fin.coe_modNat, Fin.val_cast, PNat.mul_coe]

/-- **Restriction monotonicity of the Kronecker product** (reusable core).

If `S₁ ≤ₜ T₁` and `S₂ ≤ₜ T₂` then `S₁ ⊠ S₂ ≤ₜ T₁ ⊠ T₂`, via the leg matrices
`A i ⊗ B i` (Kronecker/tensor product of the two witness matrices on each leg). -/
lemma Restricts.kron_congr {dS₁ dT₁ dS₂ dT₂ : Fin k → ℕ+}
    {S₁ : KTensor F dS₁} {T₁ : KTensor F dT₁}
    {S₂ : KTensor F dS₂} {T₂ : KTensor F dT₂}
    (h₁ : Restricts S₁ T₁) (h₂ : Restricts S₂ T₂) :
    Restricts (S₁ ⊠ S₂) (T₁ ⊠ T₂) := by
  classical
  obtain ⟨A, hA⟩ := h₁
  obtain ⟨B, hB⟩ := h₂
  refine ⟨fun i a b => A i (kronDecodeL a) (kronDecodeL b) * B i (kronDecodeR a) (kronDecodeR b),
    ?_⟩
  intro jdx
  -- Unfold the LHS Kronecker product and substitute `hA`, `hB`.
  change S₁ (kronLeftIndex jdx) * S₂ (kronRightIndex jdx) = _
  rw [hA (kronLeftIndex jdx), hB (kronRightIndex jdx), Finset.sum_mul_sum]
  -- Reindex the RHS sum by the composite pair-equiv, then split into `∑ u ∑ v`.
  set E : (∀ i, Fin ((dT₁ i * dT₂ i : ℕ+) : ℕ)) ≃
      (∀ i, Fin (dT₁ i)) × (∀ i, Fin (dT₂ i)) :=
    (Equiv.piCongrRight (fun _ => kronDecodeEquiv)).trans
      (Equiv.arrowProdEquivProdArrow _ _ _) with hE
  rw [← Equiv.sum_comp E.symm
    (fun idx : ∀ i, Fin ((dT₁ i * dT₂ i : ℕ+) : ℕ) =>
      (∏ i, (A i (kronDecodeL (jdx i)) (kronDecodeL (idx i))
        * B i (kronDecodeR (jdx i)) (kronDecodeR (idx i)))) * (T₁ ⊠ T₂) idx)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro u _
  refine Finset.sum_congr rfl ?_
  intro v _
  -- Decode facts: `E.symm (u,v)` decodes to `(u i, v i)` on each leg.
  have hdec : ∀ i, kronDecodeEquiv (E.symm (u, v) i) = (u i, v i) := by
    intro i
    have hsymm : E.symm (u, v) i = kronDecodeEquiv.symm (u i, v i) := by
      simp only [hE, Equiv.symm_trans_apply, Equiv.piCongrRight_symm_apply, Pi.map_apply,
        Equiv.arrowProdEquivProdArrow_symm_apply]
    rw [hsymm, Equiv.apply_symm_apply]
  have hL : ∀ i, kronDecodeL (d₁ := dT₁ i) (d₂ := dT₂ i) (E.symm (u, v) i) = u i := by
    intro i
    have h := hdec i
    rw [kronDecodeEquiv_apply] at h
    exact (Prod.ext_iff.1 h).1
  have hR : ∀ i, kronDecodeR (d₁ := dT₁ i) (d₂ := dT₂ i) (E.symm (u, v) i) = v i := by
    intro i
    have h := hdec i
    rw [kronDecodeEquiv_apply] at h
    exact (Prod.ext_iff.1 h).2
  -- The Kronecker leg matrix entry on the decoded index.
  have hKron : (∏ i, A i (kronDecodeL (jdx i)) (kronDecodeL (E.symm (u, v) i))
        * B i (kronDecodeR (jdx i)) (kronDecodeR (E.symm (u, v) i)))
      = (∏ i, A i (kronLeftIndex jdx i) (u i)) * (∏ i, B i (kronRightIndex jdx i) (v i)) := by
    rw [Finset.prod_mul_distrib]
    congr 1
    · refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [hL i, kronDecodeL_eq_kronLeftIndex]
    · refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [hR i, kronDecodeR_eq_kronRightIndex]
  -- The Kronecker tensor value on the decoded index.
  have hTval : (T₁ ⊠ T₂) (E.symm (u, v)) = T₁ u * T₂ v := by
    change T₁ (kronLeftIndex (E.symm (u, v))) * T₂ (kronRightIndex (E.symm (u, v))) = _
    have hkl : kronLeftIndex (E.symm (u, v)) = u := by
      funext i; exact hL i
    have hkr : kronRightIndex (E.symm (u, v)) = v := by
      funext i; exact hR i
    rw [hkl, hkr]
  -- Assemble: both sides are now equal up to commutativity of `*`.
  rw [hKron, hTval]
  ring

/-! ### `∼ₜ` is an equivalence and `⊕ₜ`/`⊠` are `∼ₜ`-congruences. -/

/-- Symmetry of `∼ₜ`. -/
lemma RestrictsEquiv.symm {dS dT : Fin k → ℕ+}
    {S : KTensor F dS} {T : KTensor F dT} (h : S ∼ₜ T) : T ∼ₜ S :=
  ⟨h.2, h.1⟩

/-- Transitivity of `∼ₜ`. -/
lemma RestrictsEquiv.trans {dS dT dU : Fin k → ℕ+}
    {S : KTensor F dS} {T : KTensor F dT} {U : KTensor F dU}
    (hST : S ∼ₜ T) (hTU : T ∼ₜ U) : S ∼ₜ U :=
  ⟨hST.1.trans hTU.1, hTU.2.trans hST.2⟩

/-- Reflexivity of `∼ₜ`. -/
lemma RestrictsEquiv.refl {d : Fin k → ℕ+} (T : KTensor F d) : T ∼ₜ T :=
  ⟨Restricts.refl T, Restricts.refl T⟩

/-- `⊕ₜ` respects `∼ₜ` (both arguments). -/
lemma RestrictsEquiv.directSum_congr {dS₁ dT₁ dS₂ dT₂ : Fin k → ℕ+}
    {S₁ : KTensor F dS₁} {T₁ : KTensor F dT₁}
    {S₂ : KTensor F dS₂} {T₂ : KTensor F dT₂}
    (h₁ : S₁ ∼ₜ T₁) (h₂ : S₂ ∼ₜ T₂) : (S₁ ⊕ₜ S₂) ∼ₜ (T₁ ⊕ₜ T₂) :=
  ⟨Restricts.directSum_congr h₁.1 h₂.1, Restricts.directSum_congr h₁.2 h₂.2⟩

/-- `⊠` respects `∼ₜ` (both arguments). -/
lemma RestrictsEquiv.kron_congr {dS₁ dT₁ dS₂ dT₂ : Fin k → ℕ+}
    {S₁ : KTensor F dS₁} {T₁ : KTensor F dT₁}
    {S₂ : KTensor F dS₂} {T₂ : KTensor F dT₂}
    (h₁ : S₁ ∼ₜ T₁) (h₂ : S₂ ∼ₜ T₂) : (S₁ ⊠ S₂) ∼ₜ (T₁ ⊠ T₂) :=
  ⟨Restricts.kron_congr h₁.1 h₂.1, Restricts.kron_congr h₁.2 h₂.2⟩

/-! ### The sigma type of all `k`-tensors and its `∼ₜ`-setoid. -/

/-- A `k`-tensor over `F` of arbitrary format, packaged with its format. -/
abbrev TT (F : Type u) [Field F] (k : ℕ) : Type u := Σ d : Fin k → ℕ+, KTensor F d

/-- The `∼ₜ`-relation lifted to the sigma type `TT F k`. -/
def TTEquiv (x y : TT F k) : Prop := x.2 ∼ₜ y.2

/-- `∼ₜ` makes `TT F k` a setoid. -/
instance tensorSetoid : Setoid (TT F k) where
  r := TTEquiv
  iseqv :=
    { refl := fun x => RestrictsEquiv.refl x.2
      symm := fun h => RestrictsEquiv.symm h
      trans := fun h₁ h₂ => RestrictsEquiv.trans h₁ h₂ }

lemma tensorSetoid_def (x y : TT F k) : x ≈ y ↔ x.2 ∼ₜ y.2 := Iff.rfl

/-! ## Structural `∼ₜ` identities.

All identities below require at least one tensor leg (`[NeZero k]`). For `k = 0`
the format type `Fin 0 → ℕ+` is a singleton, every tensor is a scalar, and the
direct sum `directSumTensor S T` returns `S` independently of `T` (it always
takes the vacuously-true `S`-block branch). Hence `S ⊕ₜ T ∼ₜ T ⊕ₜ S` is *false*
at `k = 0`, so the additive structure is genuinely non-commutative there.
`[NeZero k]` is the minimal hypothesis ruling out this degenerate case. -/

variable [NeZero k]

/-- The block-swap permutation leg matrix witnessing one direction of direct-sum
commutativity. Row `a : Fin (dT + dS)`, col `b : Fin (dS + dT)`. -/
noncomputable def dsumSwapMatrix (dS dT : Fin k → ℕ+) (i : Fin k) :
    Matrix (Fin ((dT i + dS i : ℕ+) : ℕ)) (Fin ((dS i + dT i : ℕ+) : ℕ)) F :=
  fun a b =>
    if (a : ℕ) < (dT i : ℕ) then
      (if (b : ℕ) = (dS i : ℕ) + (a : ℕ) then 1 else 0)
    else
      (if (b : ℕ) + (dT i : ℕ) = (a : ℕ) then 1 else 0)

/-- One direction of direct-sum commutativity, as a `Restricts` witness using the
block-swap permutation leg matrices. -/
lemma directSum_comm_restricts {dS dT : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT) :
    Restricts (T ⊕ₜ S) (S ⊕ₜ T) := by
  classical
  have hcS : ∀ i : Fin k, ((dS i + dT i : ℕ+) : ℕ) = (dS i : ℕ) + (dT i : ℕ) :=
    fun i => PNat.add_coe _ _
  have hcT : ∀ i : Fin k, ((dT i + dS i : ℕ+) : ℕ) = (dT i : ℕ) + (dS i : ℕ) :=
    fun i => PNat.add_coe _ _
  refine ⟨dsumSwapMatrix dS dT, ?_⟩
  intro jdx
  -- The unique nonzero column is the block-swap of `jdx`.
  let col0 : ∀ i : Fin k, Fin ((dS i + dT i : ℕ+) : ℕ) := fun i =>
    if h : (jdx i).val < (dT i : ℕ) then
      ⟨(dS i : ℕ) + (jdx i).val, by have := hcS i; omega⟩
    else
      ⟨(jdx i).val - (dT i : ℕ), by
        have h1 : (jdx i).val < ((dT i + dS i : ℕ+) : ℕ) := (jdx i).isLt
        have := hcT i; have := hcS i; omega⟩
  -- Block facts about `col0`.
  have hcol0_lt_iff : ∀ i, (col0 i).val < (dS i : ℕ) ↔ ¬ (jdx i).val < (dT i : ℕ) := by
    intro i
    by_cases h : (jdx i).val < (dT i : ℕ)
    · simp only [col0, dif_pos h, h, not_true]
      simp
    · simp only [col0, dif_neg h, h, not_false_iff, iff_true]
      have h1 : (jdx i).val < ((dT i + dS i : ℕ+) : ℕ) := (jdx i).isLt
      have := hcT i; omega
  rw [Finset.sum_eq_single col0]
  · -- The coefficient at `col0` is `1`.
    have hprod : (∏ i, dsumSwapMatrix (F := F) dS dT i (jdx i) (col0 i)) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      simp only [dsumSwapMatrix]
      by_cases h : (jdx i).val < (dT i : ℕ)
      · simp only [if_pos h, col0, dif_pos h, if_pos]
      · simp only [if_neg h, col0, dif_neg h]
        have := hcT i; rw [if_pos (by omega)]
    rw [hprod, one_mul]
    -- Both sides evaluate to the same tensor entry.
    -- LHS = `directSumTensor T S jdx`; RHS = `directSumTensor S T col0`.
    rw [directSumTensor_apply_block', directSumTensor_apply_block']
    by_cases hjT : ∀ i, (jdx i).val < (dT i : ℕ)
    · -- `jdx` all in the T-block on the left → `T jdx'`.
      -- `col0` all in the T-block of `S ⊕ T` (`≥ dS`) → `T (col0 - dS)`.
      have hcolge : ∀ i, (dS i : ℕ) ≤ (col0 i).val := by
        intro i; simp only [col0, dif_pos (hjT i)]; omega
      have hcolnotS : ¬ ∀ i, (col0 i).val < (dS i : ℕ) :=
        fun hall => absurd (hall (Classical.arbitrary _))
          (not_lt.2 (hcolge (Classical.arbitrary _)))
      -- LHS: `dif_pos hjT`; RHS: `dif_neg hcolnotS, dif_pos hcolge`.
      rw [dif_pos hjT, dif_neg hcolnotS, dif_pos hcolge]
      congr 1; funext i; apply Fin.ext
      simp only [col0, dif_pos (hjT i)]; omega
    · by_cases hjS : ∀ i, (dT i : ℕ) ≤ (jdx i).val
      · -- `jdx` all in the S-block on the left → `S (jdx - dT)`.
        -- `col0` all in the S-block of `S ⊕ T` (`< dS`) → `S col0`.
        have hcollt : ∀ i, (col0 i).val < (dS i : ℕ) := fun i =>
          (hcol0_lt_iff i).2 (not_lt.2 (hjS i))
        -- LHS: `dif_neg hjT, dif_pos hjS`; RHS: `dif_pos hcollt`.
        rw [dif_neg hjT, dif_pos hjS, dif_pos hcollt]
        congr 1; funext i; apply Fin.ext
        have hi := hjS i
        simp only [col0, dif_neg (not_lt.2 (hjS i))]
      · -- `jdx` mixed → both LHS and RHS are `0`.
        have hcS' : ¬ ∀ i, (col0 i).val < (dS i : ℕ) := by
          obtain ⟨iB, hiB⟩ := not_forall.1 hjS  -- a leg with `jdx iB < dT iB`
          exact fun hall => absurd ((hcol0_lt_iff iB).1 (hall iB)) (not_not.2 (not_le.1 hiB))
        have hcT' : ¬ ∀ i, (dS i : ℕ) ≤ (col0 i).val := by
          obtain ⟨iA, hiA⟩ := not_forall.1 hjT  -- a leg with `¬ jdx iA < dT iA`
          exact fun hall => absurd (hall iA) (not_le.2 ((hcol0_lt_iff iA).2 hiA))
        rw [dif_neg hjT, dif_neg hjS, dif_neg hcS', dif_neg hcT']
  · -- Off-witness columns contribute 0.
    intro col _ hcol
    have hne : ∃ i, col i ≠ col0 i := by
      by_contra h
      push_neg at h
      exact hcol (funext h)
    obtain ⟨i₀, hi₀⟩ := hne
    have hzero : dsumSwapMatrix (F := F) dS dT i₀ (jdx i₀) (col i₀) = 0 := by
      simp only [dsumSwapMatrix]
      by_cases h : (jdx i₀).val < (dT i₀ : ℕ)
      · rw [if_pos h, if_neg]
        intro hcoleq
        apply hi₀; apply Fin.ext
        simp only [col0, dif_pos h]; omega
      · rw [if_neg h, if_neg]
        intro hcoleq
        apply hi₀; apply Fin.ext
        have := hcT i₀
        simp only [col0, dif_neg h]; omega
    rw [Finset.prod_eq_zero (Finset.mem_univ i₀) hzero, zero_mul]
  · intro hnot; exact (hnot (Finset.mem_univ _)).elim

/-- **Commutativity of `⊕ₜ`** up to `∼ₜ`. -/
lemma directSum_comm {dS dT : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT) : (S ⊕ₜ T) ∼ₜ (T ⊕ₜ S) :=
  ⟨directSum_comm_restricts T S, directSum_comm_restricts S T⟩

/-- The value of `((S ⊕ T) ⊕ U)` at a multi-index, as a three-way block split. -/
lemma directSum_assoc_left_value {dS dT dU : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT) (U : KTensor F dU)
    (jdx : ∀ i, Fin ((((dS i + dT i) + dU i : ℕ+)) : ℕ)) :
    ((S ⊕ₜ T) ⊕ₜ U) jdx
      = if hS : ∀ i, (jdx i).val < (dS i : ℕ) then S (fun i => ⟨(jdx i).val, hS i⟩)
        else if hT : ∀ i, (dS i : ℕ) ≤ (jdx i).val ∧ (jdx i).val < (dS i : ℕ) + (dT i : ℕ)
          then T (fun i => ⟨(jdx i).val - (dS i : ℕ), by
            have := (hT i).1; have := (hT i).2; omega⟩)
        else if hU : ∀ i, (dS i : ℕ) + (dT i : ℕ) ≤ (jdx i).val
          then U (fun i => ⟨(jdx i).val - ((dS i : ℕ) + (dT i : ℕ)), by
            have h1 : (jdx i).val < ((((dS i + dT i) + dU i : ℕ+)) : ℕ) := (jdx i).isLt
            have h2 : ((((dS i + dT i) + dU i : ℕ+)) : ℕ)
              = (dS i : ℕ) + (dT i : ℕ) + (dU i : ℕ) := by
                rw [PNat.add_coe, PNat.add_coe]
            have := hU i; omega⟩)
        else 0 := by
  classical
  have hcST : ∀ i : Fin k, ((dS i + dT i : ℕ+) : ℕ) = (dS i : ℕ) + (dT i : ℕ) :=
    fun i => PNat.add_coe _ _
  rw [directSumTensor_apply_block']
  by_cases hinner : ∀ i, (jdx i).val < ((dS i + dT i : ℕ+) : ℕ)
  · -- jdx in the `(S⊕T)`-block; split that inner sum.
    rw [dif_pos hinner, directSumTensor_apply_block']
    by_cases hS : ∀ i, (jdx i).val < (dS i : ℕ)
    · -- all in S-block.
      rw [dif_pos hS, dif_pos hS]
    · -- not all in S; inner sum takes T-block iff all `≥ dS`, else 0.
      rw [dif_neg hS]
      by_cases hTmid : ∀ i, (dS i : ℕ) ≤ (jdx i).val
      · -- all `≥ dS` and (from hinner) all `< dS+dT` ⟹ all in mid-block.
        have hmid : ∀ i, (dS i : ℕ) ≤ (jdx i).val ∧ (jdx i).val < (dS i : ℕ) + (dT i : ℕ) :=
          fun i => ⟨hTmid i, by have := hinner i; rw [hcST i] at this; exact this⟩
        rw [dif_pos hTmid, dif_neg hS, dif_pos hmid]
      · -- mixed within S⊕T ⟹ inner value 0; outer not-S, not-mid (some leg `< dS`),
        -- not-U (all `< dS+dT`).
        rw [dif_neg hTmid]
        have hnotMid : ¬ ∀ i, (dS i : ℕ) ≤ (jdx i).val ∧ (jdx i).val < (dS i : ℕ) + (dT i : ℕ) := by
          obtain ⟨i₀, hi₀⟩ := not_forall.1 hTmid
          exact fun hall => hi₀ (hall i₀).1
        have hnotU : ¬ ∀ i, (dS i : ℕ) + (dT i : ℕ) ≤ (jdx i).val := by
          obtain ⟨i₀, hi₀⟩ := not_forall.1 hS
          refine fun hall => absurd (hall i₀) (not_le.2 ?_)
          have := not_lt.1 hi₀; have hin := hinner i₀; rw [hcST i₀] at hin; omega
        rw [dif_neg hS, dif_neg hnotMid, dif_neg hnotU]
  · -- jdx not all in `(S⊕T)`-block.
    rw [dif_neg hinner]
    have hnotS : ¬ ∀ i, (jdx i).val < (dS i : ℕ) := by
      obtain ⟨i₀, hi₀⟩ := not_forall.1 hinner
      refine fun hall => hi₀ ?_
      rw [hcST i₀]; have := hall i₀; omega
    rw [dif_neg hnotS]
    by_cases hUge : ∀ i, ((dS i + dT i : ℕ+) : ℕ) ≤ (jdx i).val
    · -- all `≥ dS+dT` ⟹ outer U-block.
      have hU : ∀ i, (dS i : ℕ) + (dT i : ℕ) ≤ (jdx i).val := by
        intro i; have := hUge i; rw [hcST i] at this; exact this
      have hnotMid : ¬ ∀ i, (dS i : ℕ) ≤ (jdx i).val ∧ (jdx i).val < (dS i : ℕ) + (dT i : ℕ) := by
        refine fun hall => absurd (hall (Classical.arbitrary _)).2 (not_lt.2 ?_)
        exact hU (Classical.arbitrary _)
      rw [dif_pos hUge, dif_neg hnotMid, dif_pos hU]
      congr 1
    · -- some leg `< dS+dT` (¬hUge) and some leg `≥ dS+dT` (¬hinner) ⟹ outer value 0;
      -- and not-mid, not-U on the RHS.
      rw [dif_neg hUge]
      have hnotMid : ¬ ∀ i, (dS i : ℕ) ≤ (jdx i).val ∧ (jdx i).val < (dS i : ℕ) + (dT i : ℕ) := by
        obtain ⟨i₀, hi₀⟩ := not_forall.1 hinner
        refine fun hall => hi₀ ?_
        rw [hcST i₀]; exact (hall i₀).2
      have hnotU : ¬ ∀ i, (dS i : ℕ) + (dT i : ℕ) ≤ (jdx i).val := by
        obtain ⟨i₀, hi₀⟩ := not_forall.1 hUge
        refine fun hall => hi₀ ?_
        rw [hcST i₀]; exact hall i₀
      rw [dif_neg hnotMid, dif_neg hnotU]

omit [NeZero k] in
/-- The value of `(S ⊕ (T ⊕ U))` at a multi-index, as the same three-way block
split as `directSum_assoc_left_value`. -/
lemma directSum_assoc_right_value {dS dT dU : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT) (U : KTensor F dU)
    (jdx : ∀ i, Fin (((dS i + (dT i + dU i) : ℕ+)) : ℕ)) :
    (S ⊕ₜ (T ⊕ₜ U)) jdx
      = if hS : ∀ i, (jdx i).val < (dS i : ℕ) then S (fun i => ⟨(jdx i).val, hS i⟩)
        else if hT : ∀ i, (dS i : ℕ) ≤ (jdx i).val ∧ (jdx i).val < (dS i : ℕ) + (dT i : ℕ)
          then T (fun i => ⟨(jdx i).val - (dS i : ℕ), by
            have := (hT i).1; have := (hT i).2; omega⟩)
        else if hU : ∀ i, (dS i : ℕ) + (dT i : ℕ) ≤ (jdx i).val
          then U (fun i => ⟨(jdx i).val - ((dS i : ℕ) + (dT i : ℕ)), by
            have h1 : (jdx i).val < (((dS i + (dT i + dU i) : ℕ+)) : ℕ) := (jdx i).isLt
            have h2 : (((dS i + (dT i + dU i) : ℕ+)) : ℕ)
              = (dS i : ℕ) + (dT i : ℕ) + (dU i : ℕ) := by
                rw [PNat.add_coe, PNat.add_coe]; ring
            have := hU i; omega⟩)
        else 0 := by
  classical
  have hcTU : ∀ i : Fin k, ((dT i + dU i : ℕ+) : ℕ) = (dT i : ℕ) + (dU i : ℕ) :=
    fun i => PNat.add_coe _ _
  rw [directSumTensor_apply_block']
  by_cases hS : ∀ i, (jdx i).val < (dS i : ℕ)
  · rw [dif_pos hS, dif_pos hS]
  · rw [dif_neg hS, dif_neg hS]
    -- jdx in the `(T⊕U)`-block (`≥ dS`) iff all `≥ dS`.
    by_cases hSge : ∀ i, (dS i : ℕ) ≤ (jdx i).val
    · rw [dif_pos hSge, directSumTensor_apply_block']
      by_cases hTmid : ∀ i, (jdx i).val - (dS i : ℕ) < (dT i : ℕ)
      · -- inner `(T⊕U)` takes T-block ⟹ overall mid-block.
        have hmid : ∀ i, (dS i : ℕ) ≤ (jdx i).val ∧ (jdx i).val < (dS i : ℕ) + (dT i : ℕ) :=
          fun i => ⟨hSge i, by have := hTmid i; have := hSge i; omega⟩
        rw [dif_pos hmid]
        have hinnerS : ∀ i, ((jdx i).val - (dS i : ℕ)) < (dT i : ℕ) := hTmid
        rw [dif_pos hinnerS]
      · -- inner not all in T; needs all `≥ dT` (then U-block) else 0.
        have hnotMid : ¬ ∀ i, (dS i : ℕ) ≤ (jdx i).val ∧ (jdx i).val < (dS i : ℕ) + (dT i : ℕ) := by
          obtain ⟨i₀, hi₀⟩ := not_forall.1 hTmid
          refine fun hall => hi₀ ?_
          have := (hall i₀).2; have := (hall i₀).1; omega
        rw [dif_neg hnotMid, dif_neg hTmid]
        by_cases hUge : ∀ i, (dT i : ℕ) ≤ (jdx i).val - (dS i : ℕ)
        · have hU : ∀ i, (dS i : ℕ) + (dT i : ℕ) ≤ (jdx i).val := by
            intro i; have := hUge i; have := hSge i; omega
          rw [dif_pos hUge, dif_pos hU]
          congr 1; funext i; apply Fin.ext
          simp only; omega
        · have hnotU : ¬ ∀ i, (dS i : ℕ) + (dT i : ℕ) ≤ (jdx i).val := by
            obtain ⟨i₀, hi₀⟩ := not_forall.1 hUge
            refine fun hall => hi₀ ?_
            have := hall i₀; have := hSge i₀; omega
          rw [dif_neg hUge, dif_neg hnotU]
    · -- some leg `< dS` and (¬hS) some leg... actually ¬hS already; here ¬hSge.
      rw [dif_neg hSge]
      have hnotMid : ¬ ∀ i, (dS i : ℕ) ≤ (jdx i).val ∧ (jdx i).val < (dS i : ℕ) + (dT i : ℕ) := by
        obtain ⟨i₀, hi₀⟩ := not_forall.1 hSge
        exact fun hall => hi₀ (hall i₀).1
      have hnotU : ¬ ∀ i, (dS i : ℕ) + (dT i : ℕ) ≤ (jdx i).val := by
        obtain ⟨i₀, hi₀⟩ := not_forall.1 hSge
        refine fun hall => hi₀ ?_
        have := hall i₀; have := (dT i₀).pos; omega
      rw [dif_neg hnotMid, dif_neg hnotU]

/-- **Associativity of `⊕ₜ`** up to `∼ₜ`. -/
lemma directSum_assoc {dS dT dU : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT) (U : KTensor F dU) :
    ((S ⊕ₜ T) ⊕ₜ U) ∼ₜ (S ⊕ₜ (T ⊕ₜ U)) := by
  have hfmt : ∀ i : Fin k,
      (((dS i + dT i) + dU i : ℕ+) : ℕ) = ((dS i + (dT i + dU i) : ℕ+) : ℕ) := by
    intro i; simp only [PNat.add_coe]; ring
  have hval : ∀ (jdx : ∀ i, Fin ((((dS i + dT i) + dU i : ℕ+)) : ℕ)),
      ((S ⊕ₜ T) ⊕ₜ U) jdx
        = (S ⊕ₜ (T ⊕ₜ U)) (fun i => Fin.cast (hfmt i) (jdx i)) := by
    intro jdx
    rw [directSum_assoc_left_value, directSum_assoc_right_value]
    simp only [Fin.val_cast]
  constructor
  · exact Restricts.of_eq_cast hfmt hval
  · refine Restricts.of_eq_cast (fun i => (hfmt i).symm) (fun jdx => ?_)
    rw [directSum_assoc_left_value, directSum_assoc_right_value]
    simp only [Fin.val_cast]

/-! ### Kronecker product identities. -/

omit [NeZero k] in
/-- Value of `(S ⊠ T) idx` at the underlying `.val`-level: factors as a product. -/
lemma kron_apply {dS dT : Fin k → ℕ+} (S : KTensor F dS) (T : KTensor F dT)
    (idx : ∀ i, Fin ((dS i * dT i : ℕ+) : ℕ)) :
    (S ⊠ T) idx
      = S (fun i => kronDecodeL (idx i)) * T (fun i => kronDecodeR (idx i)) := by
  change S (kronLeftIndex idx) * T (kronRightIndex idx) = _
  congr 1

omit [NeZero k] in
/-- **Associativity of `⊠`** up to `∼ₜ`. -/
lemma kron_assoc {dS dT dU : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT) (U : KTensor F dU) :
    ((S ⊠ T) ⊠ U) ∼ₜ (S ⊠ (T ⊠ U)) := by
  have hfmt : ∀ i : Fin k,
      ((((dS i * dT i) * dU i : ℕ+)) : ℕ) = (((dS i * (dT i * dU i) : ℕ+)) : ℕ) := by
    intro i; simp only [PNat.mul_coe]; ring
  -- Both equal `S a * T b * U c` where `(a,b,c)` is the triple decode of the index.
  have key : ∀ (jdx : ∀ i, Fin (((dS i * dT i) * dU i : ℕ+) : ℕ)),
      ((S ⊠ T) ⊠ U) jdx
        = (S ⊠ (T ⊠ U)) (fun i => Fin.cast (hfmt i) (jdx i)) := by
    intro jdx
    set cjdx : ∀ i, Fin ((dS i * (dT i * dU i) : ℕ+) : ℕ) :=
      fun i => Fin.cast (hfmt i) (jdx i) with hcjdx
    rw [kron_apply (S ⊠ T) U jdx, kron_apply S (T ⊠ U) cjdx]
    rw [kron_apply S T (fun i => kronDecodeL (jdx i)),
        kron_apply T U (fun i => kronDecodeR (cjdx i))]
    -- Match the three decoded indices by their `.val`.
    have ha : (fun i => kronDecodeL (kronDecodeL (jdx i)))
        = (fun i => kronDecodeL (cjdx i)) := by
      funext i; apply Fin.ext
      simp only [hcjdx, kronDecodeL, finProdFinEquiv_symm_apply,
        Fin.coe_divNat, Fin.val_cast, PNat.mul_coe]
      rw [Nat.div_div_eq_div_mul]; congr 1; ring
    have hb : (fun i => kronDecodeR (kronDecodeL (jdx i)))
        = (fun i => kronDecodeL (kronDecodeR (cjdx i))) := by
      funext i; apply Fin.ext
      simp only [hcjdx, kronDecodeL, kronDecodeR, finProdFinEquiv_symm_apply,
        Fin.coe_divNat, Fin.coe_modNat, Fin.val_cast, PNat.mul_coe]
      rw [Nat.mod_mul_left_div_self]
    have hc : (fun i => kronDecodeR (jdx i))
        = (fun i => kronDecodeR (kronDecodeR (cjdx i))) := by
      funext i; apply Fin.ext
      simp only [hcjdx, kronDecodeR, finProdFinEquiv_symm_apply,
        Fin.coe_modNat, Fin.val_cast, PNat.mul_coe]
      rw [Nat.mod_mod_of_dvd _ (dvd_mul_left _ _)]
    rw [ha, hb, hc]; ring
  exact ⟨Restricts.of_eq_cast hfmt key,
    Restricts.of_eq_cast (fun i => (hfmt i).symm) (fun jdx => by
      rw [key]; congr 1)⟩

omit [NeZero k] in
/-- One direction of Kronecker commutativity, via the factor-swap permutation
leg matrices. -/
lemma kron_comm_restricts {dS dT : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT) :
    Restricts (T ⊠ S) (S ⊠ T) := by
  classical
  -- Leg matrix: row `a : Fin (dT*dS)`, col `b : Fin (dS*dT)`; `1` iff the decoded
  -- factors of `b` are the swap of those of `a`.
  refine ⟨fun i a b =>
    if (kronDecodeL b : ℕ) = (kronDecodeR a).val ∧ (kronDecodeR b : ℕ) = (kronDecodeL a).val
      then 1 else 0, ?_⟩
  intro jdx
  -- The unique nonzero column: swap the factors of each leg of `jdx`.
  let col0 : ∀ i, Fin ((dS i * dT i : ℕ+) : ℕ) := fun i =>
    Fin.cast (by rw [PNat.mul_coe]) (finProdFinEquiv (kronDecodeR (jdx i), kronDecodeL (jdx i)))
  have hdec0 : ∀ i, finProdFinEquiv.symm (Fin.cast (by rw [PNat.mul_coe]) (col0 i))
      = (kronDecodeR (jdx i), kronDecodeL (jdx i)) := by
    intro i
    simp only [col0, Fin.cast_eq_self, Equiv.symm_apply_apply]
  have hL0 : ∀ i, (kronDecodeL (col0 i)).val = (kronDecodeR (jdx i)).val := by
    intro i
    have : kronDecodeL (col0 i) = (kronDecodeR (jdx i)) := by
      change (finProdFinEquiv.symm (Fin.cast _ (col0 i))).1 = _
      rw [hdec0 i]
    rw [this]
  have hR0 : ∀ i, (kronDecodeR (col0 i)).val = (kronDecodeL (jdx i)).val := by
    intro i
    have : kronDecodeR (col0 i) = (kronDecodeL (jdx i)) := by
      change (finProdFinEquiv.symm (Fin.cast _ (col0 i))).2 = _
      rw [hdec0 i]
    rw [this]
  rw [Finset.sum_eq_single col0]
  · have hprod : (∏ i, (if (kronDecodeL (col0 i) : ℕ) = (kronDecodeR (jdx i)).val
        ∧ (kronDecodeR (col0 i) : ℕ) = (kronDecodeL (jdx i)).val then (1 : F) else 0)) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      rw [if_pos ⟨hL0 i, hR0 i⟩]
    rw [hprod, one_mul]
    -- `(T ⊠ S) jdx = T(L jdx)*S(R jdx)` and `(S ⊠ T) col0 = S(L col0)*T(R col0)`.
    rw [kron_apply, kron_apply]
    have hSarg : (fun i => kronDecodeL (col0 i)) = (fun i => kronDecodeR (jdx i)) := by
      funext i; exact Fin.ext (hL0 i)
    have hTarg : (fun i => kronDecodeR (col0 i)) = (fun i => kronDecodeL (jdx i)) := by
      funext i; exact Fin.ext (hR0 i)
    rw [hSarg, hTarg]; ring
  · -- Off-witness columns contribute 0.
    intro col _ hcol
    have hne : ∃ i, col i ≠ col0 i := by
      by_contra h; push_neg at h; exact hcol (funext h)
    obtain ⟨i₀, hi₀⟩ := hne
    have hzero : (if (kronDecodeL (col i₀) : ℕ) = (kronDecodeR (jdx i₀)).val
        ∧ (kronDecodeR (col i₀) : ℕ) = (kronDecodeL (jdx i₀)).val then (1 : F) else 0) = 0 := by
      rw [if_neg]
      rintro ⟨hLeq, hReq⟩
      -- col i₀ and col0 i₀ have the same decode ⟹ equal, contradiction.
      apply hi₀
      have hcolL : kronDecodeL (col i₀) = kronDecodeL (col0 i₀) :=
        Fin.ext (by rw [hLeq, hL0 i₀])
      have hcolR : kronDecodeR (col i₀) = kronDecodeR (col0 i₀) :=
        Fin.ext (by rw [hReq, hR0 i₀])
      -- Reconstruct any index from its two decoded factors.
      have key2 : ∀ (x : Fin ((dS i₀ * dT i₀ : ℕ+) : ℕ)),
          x = Fin.cast (by rw [PNat.mul_coe])
            (finProdFinEquiv (kronDecodeL x, kronDecodeR x)) := by
        intro x
        apply Fin.ext
        have : (kronDecodeL x, kronDecodeR x)
            = finProdFinEquiv.symm (Fin.cast (by rw [PNat.mul_coe]) x) := rfl
        rw [this, Equiv.apply_symm_apply]; simp
      rw [key2 (col i₀), key2 (col0 i₀), hcolL, hcolR]
    rw [Finset.prod_eq_zero (Finset.mem_univ i₀) hzero, zero_mul]
  · intro hnot; exact (hnot (Finset.mem_univ _)).elim

omit [NeZero k] in
/-- **Commutativity of `⊠`** up to `∼ₜ`. -/
lemma kron_comm {dS dT : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT) : (S ⊠ T) ∼ₜ (T ⊠ S) :=
  ⟨kron_comm_restricts T S, kron_comm_restricts S T⟩

/-! ### Zero and unit identities. -/

/-- The canonical zero `k`-tensor (minimal format `fun _ => 1`). -/
def zeroT : KTensor F (fun (_ : Fin k) => (1 : ℕ+)) := fun _ => 0

omit [NeZero k] in
/-- Every zero `k`-tensor (in any format) restricts to any other zero `k`-tensor.
The target value is `0`, so the right-hand sum vanishes for any leg matrices. -/
lemma zero_Restricts {dS dT : Fin k → ℕ+} :
    Restricts (0 : KTensor F dS) (0 : KTensor F dT) := by
  classical
  refine ⟨fun _ => 0, fun jdx => ?_⟩
  symm
  apply Finset.sum_eq_zero
  intro idx _
  change _ * (0 : KTensor F dT) idx = 0
  simp

omit [NeZero k] in
/-- All zero `k`-tensors form a single `∼ₜ`-class. -/
lemma zero_equiv {dS dT : Fin k → ℕ+} :
    (0 : KTensor F dS) ∼ₜ (0 : KTensor F dT) :=
  ⟨zero_Restricts, zero_Restricts⟩

omit [NeZero k] in
/-- `zeroT` is `∼ₜ` to the zero tensor of any format (it *is* the zero tensor of
its own format). -/
lemma zeroT_equiv_zero {d : Fin k → ℕ+} :
    (zeroT : KTensor F (fun _ => (1 : ℕ+))) ∼ₜ (0 : KTensor F d) :=
  zero_equiv

omit [NeZero k] in
/-- `0 ⊠ T ∼ₜ 0`: the Kronecker product with a zero tensor is zero. -/
lemma zero_kron {dS dT : Fin k → ℕ+} (T : KTensor F dT) :
    ((0 : KTensor F dS) ⊠ T) ∼ₜ (0 : KTensor F dS) := by
  have h0 : ((0 : KTensor F dS) ⊠ T) = (0 : KTensor F (fun i => dS i * dT i)) := by
    funext idx
    change (0 : KTensor F dS) _ * T _ = (0 : KTensor F (fun i => dS i * dT i)) idx
    simp
  rw [h0]; exact zero_equiv

omit [NeZero k] in
/-- The rank-`1` unit tensor is the all-ones tensor `fun _ => 1`. -/
lemma unitTensor_one_eq : (unitTensor F (k := k) 1) = fun _ => 1 := by
  funext idx
  change (if ∀ i j, idx i = idx j then (1 : F) else 0) = 1
  rw [if_pos]
  intro i j
  apply Fin.ext
  have hi : (idx i).val < 1 := by have := (idx i).isLt; simp only [PNat.one_coe] at this; exact this
  have hj : (idx j).val < 1 := by have := (idx j).isLt; simp only [PNat.one_coe] at this; exact this
  omega

omit [NeZero k] in
/-- **Left unit for `⊠`**: `⟨1⟩ ⊠ T ∼ₜ T`. -/
lemma one_kron {dT : Fin k → ℕ+} (T : KTensor F dT) :
    (unitTensor F (k := k) 1 ⊠ T) ∼ₜ T := by
  have hfmt : ∀ i : Fin k, (((1 : ℕ+) * dT i : ℕ+) : ℕ) = (dT i : ℕ) := by
    intro i; rw [PNat.mul_coe]; simp
  have key : ∀ (jdx : ∀ i, Fin (((1 : ℕ+) * dT i : ℕ+) : ℕ)),
      (unitTensor F (k := k) 1 ⊠ T) jdx = T (fun i => Fin.cast (hfmt i) (jdx i)) := by
    intro jdx
    rw [kron_apply, unitTensor_one_eq]
    change (1 : F) * T (fun i => kronDecodeR (jdx i)) = _
    rw [one_mul]
    congr 1; funext i; apply Fin.ext
    have hjlt : (jdx i).val < (dT i : ℕ) := lt_of_lt_of_eq (jdx i).isLt (hfmt i)
    simp only [kronDecodeR, finProdFinEquiv_symm_apply, Fin.coe_modNat, Fin.val_cast, PNat.mul_coe,
      PNat.one_coe]
    rw [Nat.mod_eq_of_lt hjlt]
  exact ⟨Restricts.of_eq_cast hfmt key,
    Restricts.of_eq_cast (fun i => (hfmt i).symm) (fun jdx => by rw [key]; congr 1)⟩

omit [NeZero k] in
/-- **Right unit for `⊠`**: `T ⊠ ⟨1⟩ ∼ₜ T`. -/
lemma kron_one {dT : Fin k → ℕ+} (T : KTensor F dT) :
    (T ⊠ unitTensor F (k := k) 1) ∼ₜ T :=
  (kron_comm T (unitTensor F (k := k) 1)).trans (one_kron T)

/-- `T` restricts into the upper block of `(0 : KTensor F dZ) ⊕ₜ T`. -/
lemma restricts_zero_directSum {dZ dT : Fin k → ℕ+} (T : KTensor F dT) :
    Restricts T ((0 : KTensor F dZ) ⊕ₜ T) := by
  classical
  have hc : ∀ i : Fin k, ((dZ i + dT i : ℕ+) : ℕ) = (dZ i : ℕ) + (dT i : ℕ) :=
    fun i => PNat.add_coe _ _
  -- Leg matrix: row `a : Fin dT`, col `b : Fin (dZ+dT)`; `1` iff `b = dZ + a`.
  refine ⟨fun i a b => if (b : ℕ) = (dZ i : ℕ) + (a : ℕ) then 1 else 0, ?_⟩
  intro jdx
  let col0 : ∀ i, Fin ((dZ i + dT i : ℕ+) : ℕ) := fun i =>
    ⟨(dZ i : ℕ) + (jdx i).val, by have := (jdx i).isLt; have := hc i; omega⟩
  rw [Finset.sum_eq_single col0]
  · have hprod : (∏ i, (if (col0 i : ℕ) = (dZ i : ℕ) + (jdx i).val then (1 : F) else 0)) = 1 := by
      apply Finset.prod_eq_one; intro i _; rw [if_pos]; rfl
    rw [hprod, one_mul, directSumTensor_apply_block']
    have hge : ¬ ∀ i, (col0 i).val < (dZ i : ℕ) := by
      refine fun hall => absurd (hall (Classical.arbitrary _)) (not_lt.2 ?_)
      simp only [col0]; omega
    have hT : ∀ i, (dZ i : ℕ) ≤ (col0 i).val := by intro i; simp only [col0]; omega
    rw [dif_neg hge, dif_pos hT]
    congr 1; funext i; apply Fin.ext; simp only [col0]; omega
  · intro col _ hcol
    have hne : ∃ i, col i ≠ col0 i := by
      by_contra h; push_neg at h; exact hcol (funext h)
    obtain ⟨i₀, hi₀⟩ := hne
    have hzero : (if (col i₀ : ℕ) = (dZ i₀ : ℕ) + (jdx i₀).val then (1 : F) else 0) = 0 := by
      rw [if_neg]; intro h; apply hi₀; apply Fin.ext; simp only [col0]; omega
    rw [Finset.prod_eq_zero (Finset.mem_univ i₀) hzero, zero_mul]
  · intro hnot; exact (hnot (Finset.mem_univ _)).elim

/-- `(0 : KTensor F dZ) ⊕ₜ T` restricts to `T`. -/
lemma zero_directSum_restricts {dZ dT : Fin k → ℕ+} (T : KTensor F dT) :
    Restricts ((0 : KTensor F dZ) ⊕ₜ T) T := by
  classical
  have hc : ∀ i : Fin k, ((dZ i + dT i : ℕ+) : ℕ) = (dZ i : ℕ) + (dT i : ℕ) :=
    fun i => PNat.add_coe _ _
  -- Leg matrix: row `a : Fin (dZ+dT)`, col `b : Fin dT`; `1` iff `a = dZ + b`.
  refine ⟨fun i a b => if (a : ℕ) = (dZ i : ℕ) + (b : ℕ) then 1 else 0, ?_⟩
  intro jdx
  rw [directSumTensor_apply_block']
  by_cases hlow : ∀ i, (jdx i).val < (dZ i : ℕ)
  · -- jdx in the zero block ⟹ value 0; every term of the RHS sum vanishes.
    rw [dif_pos hlow]
    symm
    apply Finset.sum_eq_zero
    intro col _
    have hzero : (if (jdx (Classical.arbitrary _) : ℕ)
        = (dZ (Classical.arbitrary _) : ℕ) + (col (Classical.arbitrary _) : ℕ) then (1 : F) else 0)
        = 0 := by
      rw [if_neg]; have := hlow (Classical.arbitrary (Fin k)); omega
    rw [Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary (Fin k))) hzero, zero_mul]
  · by_cases hhigh : ∀ i, (dZ i : ℕ) ≤ (jdx i).val
    · -- jdx in the T-block ⟹ value `T (jdx - dZ)`; unique nonzero column.
      rw [dif_neg hlow, dif_pos hhigh]
      let col0 : ∀ i, Fin (dT i) := fun i =>
        ⟨(jdx i).val - (dZ i : ℕ), by
          have h1 : (jdx i).val < ((dZ i + dT i : ℕ+) : ℕ) := (jdx i).isLt
          have h2 := hc i
          have h3 := hhigh i
          omega⟩
      rw [Finset.sum_eq_single col0]
      · have hprod : (∏ i,
            (if (jdx i : ℕ) = (dZ i : ℕ) + (col0 i : ℕ) then (1 : F) else 0)) = 1 := by
          apply Finset.prod_eq_one; intro i _; rw [if_pos]
          simp only [col0]; have := hhigh i; omega
        rw [hprod, one_mul]
      · intro col _ hcol
        have hne : ∃ i, col i ≠ col0 i := by
          by_contra h; push_neg at h; exact hcol (funext h)
        obtain ⟨i₀, hi₀⟩ := hne
        have hzero : (if (jdx i₀ : ℕ) = (dZ i₀ : ℕ) + (col i₀ : ℕ) then (1 : F) else 0) = 0 := by
          rw [if_neg]; intro h; apply hi₀; apply Fin.ext; simp only [col0]
          have := hhigh i₀; omega
        rw [Finset.prod_eq_zero (Finset.mem_univ i₀) hzero, zero_mul]
      · intro hnot; exact (hnot (Finset.mem_univ _)).elim
    · -- jdx mixed ⟹ value 0; the RHS sum vanishes (a `< dZ` leg).
      rw [dif_neg hlow, dif_neg hhigh]
      symm
      apply Finset.sum_eq_zero
      intro col _
      obtain ⟨i₀, hi₀⟩ := not_forall.1 hhigh
      have hzero : (if (jdx i₀ : ℕ) = (dZ i₀ : ℕ) + (col i₀ : ℕ) then (1 : F) else 0) = 0 := by
        rw [if_neg]; have := not_le.1 hi₀; omega
      rw [Finset.prod_eq_zero (Finset.mem_univ i₀) hzero, zero_mul]

/-- **Additive left unit**: `(0 : KTensor F dZ) ⊕ₜ T ∼ₜ T`. -/
lemma zero_directSum {dZ dT : Fin k → ℕ+} (T : KTensor F dT) :
    ((0 : KTensor F dZ) ⊕ₜ T) ∼ₜ T :=
  ⟨zero_directSum_restricts T, restricts_zero_directSum T⟩

/-! ### Distributivity of `⊠` over `⊕ₜ` (up to `∼ₜ`). -/

/-- The per-leg distributivity index correspondence.

The left format `dS * (dT + dU)` and the right format `(dS * dT) + (dS * dU)`
have the same cardinality on each leg. Decompose a left index `a` as
`a = t + (dT+dU)·s` with `s < dS`, `t < dT+dU`. If `t < dT` (the `T`-block), send
`a` to the `(S⊠T)`-block index `t + dT·s`; otherwise (the `U`-block) send it to
the `(S⊠U)`-block index `dS·dT + ((t-dT) + dU·s)`. This is the realization of the
ring distributivity bijection `a·(b+c) ↔ a·b + a·c` on the indices. -/
def distribCorr (dS dT dU : ℕ+)
    (a : Fin ((dS * (dT + dU) : ℕ+) : ℕ)) :
    Fin (((dS * dT + dS * dU : ℕ+)) : ℕ) :=
  let s : ℕ := a.val / ((dT : ℕ) + (dU : ℕ))
  let t : ℕ := a.val % ((dT : ℕ) + (dU : ℕ))
  if hbr : t < (dT : ℕ) then
    ⟨t + (dT : ℕ) * s, by
      have hcL : ((dS * (dT + dU) : ℕ+) : ℕ) = (dS : ℕ) * ((dT : ℕ) + (dU : ℕ)) := by
        rw [PNat.mul_coe, PNat.add_coe]
      have hcR : ((dS * dT + dS * dU : ℕ+) : ℕ)
          = (dS : ℕ) * (dT : ℕ) + (dS : ℕ) * (dU : ℕ) := by
        rw [PNat.add_coe, PNat.mul_coe, PNat.mul_coe]
      have ht : t < (dT : ℕ) + (dU : ℕ) := Nat.mod_lt _ (by positivity)
      have hs : s < (dS : ℕ) := by
        have ha : a.val < (dS : ℕ) * ((dT : ℕ) + (dU : ℕ)) := hcL ▸ a.isLt
        exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at ha)
      rw [hcR]
      have htlt : t < (dT : ℕ) := hbr
      calc t + (dT : ℕ) * s < (dT : ℕ) + (dT : ℕ) * s := by omega
        _ = (dT : ℕ) * (s + 1) := by ring
        _ ≤ (dT : ℕ) * (dS : ℕ) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ (dS : ℕ) * (dT : ℕ) + (dS : ℕ) * (dU : ℕ) := by
            rw [Nat.mul_comm]; omega⟩
  else
    ⟨(dS : ℕ) * (dT : ℕ) + ((t - (dT : ℕ)) + (dU : ℕ) * s), by
      have hcL : ((dS * (dT + dU) : ℕ+) : ℕ) = (dS : ℕ) * ((dT : ℕ) + (dU : ℕ)) := by
        rw [PNat.mul_coe, PNat.add_coe]
      have hcR : ((dS * dT + dS * dU : ℕ+) : ℕ)
          = (dS : ℕ) * (dT : ℕ) + (dS : ℕ) * (dU : ℕ) := by
        rw [PNat.add_coe, PNat.mul_coe, PNat.mul_coe]
      have ht : t < (dT : ℕ) + (dU : ℕ) := Nat.mod_lt _ (by positivity)
      have hs : s < (dS : ℕ) := by
        have ha : a.val < (dS : ℕ) * ((dT : ℕ) + (dU : ℕ)) := hcL ▸ a.isLt
        exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at ha)
      rw [hcR]
      have htU : t - (dT : ℕ) < (dU : ℕ) := by
        have := not_lt.1 hbr; omega
      have : (t - (dT : ℕ)) + (dU : ℕ) * s < (dU : ℕ) * (dS : ℕ) := by
        calc (t - (dT : ℕ)) + (dU : ℕ) * s < (dU : ℕ) + (dU : ℕ) * s := by omega
          _ = (dU : ℕ) * (s + 1) := by ring
          _ ≤ (dU : ℕ) * (dS : ℕ) := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_comm (dU : ℕ) (dS : ℕ)] at this
      omega⟩

/-- Common `.val` abbreviations: the decode of a `distribCorr` source index. -/
lemma distribCorr_val_lt_of_T {dS dT dU : ℕ+}
    (a : Fin ((dS * (dT + dU) : ℕ+) : ℕ))
    (hbr : a.val % ((dT : ℕ) + (dU : ℕ)) < (dT : ℕ)) :
    (distribCorr dS dT dU a).val < (dS : ℕ) * (dT : ℕ) ∧
      (distribCorr dS dT dU a).val
        = (a.val % ((dT : ℕ) + (dU : ℕ))) + (dT : ℕ) * (a.val / ((dT : ℕ) + (dU : ℕ))) := by
  have hval : (distribCorr dS dT dU a).val
      = (a.val % ((dT : ℕ) + (dU : ℕ))) + (dT : ℕ) * (a.val / ((dT : ℕ) + (dU : ℕ))) := by
    simp only [distribCorr, dif_pos hbr]
  refine ⟨?_, hval⟩
  rw [hval]
  set s : ℕ := a.val / ((dT : ℕ) + (dU : ℕ)) with hs_def
  set t : ℕ := a.val % ((dT : ℕ) + (dU : ℕ)) with ht_def
  have hcL : ((dS * (dT + dU) : ℕ+) : ℕ) = (dS : ℕ) * ((dT : ℕ) + (dU : ℕ)) := by
    rw [PNat.mul_coe, PNat.add_coe]
  have hs : s < (dS : ℕ) := by
    have ha : a.val < (dS : ℕ) * ((dT : ℕ) + (dU : ℕ)) := hcL ▸ a.isLt
    exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at ha)
  calc t + (dT : ℕ) * s < (dT : ℕ) + (dT : ℕ) * s := by omega
    _ = (dT : ℕ) * (s + 1) := by ring
    _ ≤ (dT : ℕ) * (dS : ℕ) := Nat.mul_le_mul_left _ (by omega)
    _ = (dS : ℕ) * (dT : ℕ) := by ring

/-- `.val` of a `distribCorr` source index in the `U`-branch. -/
lemma distribCorr_val_ge_of_U {dS dT dU : ℕ+}
    (a : Fin ((dS * (dT + dU) : ℕ+) : ℕ))
    (hbr : ¬ a.val % ((dT : ℕ) + (dU : ℕ)) < (dT : ℕ)) :
    (dS : ℕ) * (dT : ℕ) ≤ (distribCorr dS dT dU a).val ∧
      (distribCorr dS dT dU a).val - (dS : ℕ) * (dT : ℕ)
        = ((a.val % ((dT : ℕ) + (dU : ℕ))) - (dT : ℕ))
          + (dU : ℕ) * (a.val / ((dT : ℕ) + (dU : ℕ))) := by
  have hval : (distribCorr dS dT dU a).val
      = (dS : ℕ) * (dT : ℕ)
        + (((a.val % ((dT : ℕ) + (dU : ℕ))) - (dT : ℕ))
          + (dU : ℕ) * (a.val / ((dT : ℕ) + (dU : ℕ)))) := by
    simp only [distribCorr, dif_neg hbr]
  rw [hval]; omega

/-- **Distributivity value identity.** Evaluating `S ⊠ (T ⊕ₜ U)` at a multi-index
`jdx` equals evaluating `(S ⊠ T) ⊕ₜ (S ⊠ U)` at the leg-wise `distribCorr` image
of `jdx`. -/
lemma left_distrib_value {dS dT dU : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT) (U : KTensor F dU)
    (jdx : ∀ i, Fin ((dS i * (dT i + dU i) : ℕ+) : ℕ)) :
    (S ⊠ (T ⊕ₜ U)) jdx
      = ((S ⊠ T) ⊕ₜ (S ⊠ U))
        (fun i => distribCorr (dS i) (dT i) (dU i) (jdx i)) := by
  classical
  let col0 : ∀ i, Fin (((dS i * dT i + dS i * dU i : ℕ+)) : ℕ) := fun i =>
    distribCorr (dS i) (dT i) (dU i) (jdx i)
  change (S ⊠ (T ⊕ₜ U)) jdx = ((S ⊠ T) ⊕ₜ (S ⊠ U)) col0
  -- `.val` of each leg's decodeR, with the modulus normalised to `dT+dU`.
  have hkd : ∀ i, ((kronDecodeR (jdx i)) : ℕ)
      = (jdx i).val % ((dT i : ℕ) + (dU i : ℕ)) := by
    intro i; rw [kronDecodeR_val, PNat.add_coe]
  -- LHS = `S(decodeL jdx) * (T⊕U)(decodeR jdx)`.
  rw [kron_apply]
  -- Block test for `col0`: all legs in the `(S⊠T)`-block iff all decodeR < dT.
  by_cases hT : ∀ i, ((kronDecodeR (jdx i) : ℕ)) < (dT i : ℕ)
  · -- T-branch on every leg.
    have hbr : ∀ i, (jdx i).val % ((dT i : ℕ) + (dU i : ℕ)) < (dT i : ℕ) := by
      intro i; rw [← hkd]; exact hT i
    have hcollt : ∀ i, (col0 i).val < ((dS i * dT i : ℕ+) : ℕ) := by
      intro i
      rw [PNat.mul_coe]
      exact (distribCorr_val_lt_of_T (jdx i) (hbr i)).1
    -- Evaluate `(T⊕U)(decodeR jdx)` to the T-block.
    have hdsT : ∀ i, ((kronDecodeR (jdx i)) : Fin ((dT i + dU i : ℕ+) : ℕ)).val
        < (dT i : ℕ) := fun i => hT i
    have hTUval : (T ⊕ₜ U) (fun i => kronDecodeR (jdx i))
        = T (fun i => ⟨(kronDecodeR (jdx i)).val, hdsT i⟩) := by
      rw [directSumTensor_apply_block', dif_pos (fun i => hdsT i)]
    rw [hTUval]
    -- Evaluate the RHS direct sum at `col0` to the `(S⊠T)`-block, then `kron_apply`.
    have hRHS : ((S ⊠ T) ⊕ₜ (S ⊠ U)) col0
        = (S ⊠ T) (fun i => ⟨(col0 i).val, hcollt i⟩) := by
      rw [directSumTensor_apply_block', dif_pos hcollt]
    rw [hRHS, kron_apply]
    -- Now match the three tensor arguments by their `.val`.
    have hLeq : (fun i => kronDecodeL (jdx i))
        = (fun i => kronDecodeL ⟨(col0 i).val, hcollt i⟩) := by
      funext i; apply Fin.ext
      simp only [kronDecodeL_val, PNat.add_coe]
      have hv := (distribCorr_val_lt_of_T (jdx i) (hbr i)).2
      change (col0 i).val = _ at hv
      rw [hv, Nat.add_mul_div_left _ _ (by positivity : 0 < (dT i : ℕ)),
        Nat.div_eq_of_lt (hbr i), Nat.zero_add]
    have hReq : (fun i => (⟨(kronDecodeR (jdx i)).val, hdsT i⟩ : Fin (dT i)))
        = (fun i => kronDecodeR ⟨(col0 i).val, hcollt i⟩) := by
      funext i; apply Fin.ext
      simp only [kronDecodeR_val, PNat.add_coe]
      have hv := (distribCorr_val_lt_of_T (jdx i) (hbr i)).2
      change (col0 i).val = _ at hv
      rw [hv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hbr i)]
    rw [hLeq, hReq]
  · -- Not all legs in T; either all in U (U-branch) or mixed (both sides 0).
    push_neg at hT
    obtain ⟨iR, hiR⟩ := hT
    by_cases hU : ∀ i, (dT i : ℕ) ≤ ((kronDecodeR (jdx i)) : ℕ)
    · -- U-branch on every leg.
      have hbr : ∀ i, ¬ (jdx i).val % ((dT i : ℕ) + (dU i : ℕ)) < (dT i : ℕ) := by
        intro i; rw [← hkd]; exact not_lt.2 (hU i)
      have hcolge : ∀ i, ((dS i * dT i : ℕ+) : ℕ) ≤ (col0 i).val := by
        intro i; rw [PNat.mul_coe]
        exact (distribCorr_val_ge_of_U (jdx i) (hbr i)).1
      have hcolnotT : ¬ ∀ i, (col0 i).val < ((dS i * dT i : ℕ+) : ℕ) :=
        fun hall => absurd (hall (Classical.arbitrary _))
          (not_lt.2 (hcolge (Classical.arbitrary _)))
      -- The U-branch of `(T⊕U)` on `decodeR jdx`.
      have hnotT : ¬ ∀ i, ((kronDecodeR (jdx i)) : Fin ((dT i + dU i : ℕ+) : ℕ)).val
          < (dT i : ℕ) := fun hall => absurd (hall iR) (not_lt.2 hiR)
      have hUge : ∀ i, (dT i : ℕ)
          ≤ ((kronDecodeR (jdx i)) : Fin ((dT i + dU i : ℕ+) : ℕ)).val := fun i => hU i
      have hTUval : (T ⊕ₜ U) (fun i => kronDecodeR (jdx i))
          = U (fun i => ⟨(kronDecodeR (jdx i)).val - (dT i : ℕ), by
              have h1 : ((kronDecodeR (jdx i)) : Fin ((dT i + dU i : ℕ+) : ℕ)).val
                < ((dT i + dU i : ℕ+) : ℕ) := (kronDecodeR (jdx i)).isLt
              have h2 : ((dT i + dU i : ℕ+) : ℕ) = (dT i : ℕ) + (dU i : ℕ) := PNat.add_coe _ _
              have := hUge i; omega⟩) := by
        rw [directSumTensor_apply_block', dif_neg hnotT, dif_pos hUge]
      rw [hTUval]
      -- Evaluate the RHS direct sum at `col0` to the `(S⊠U)`-block, then `kron_apply`.
      have hRHS : ((S ⊠ T) ⊕ₜ (S ⊠ U)) col0
          = (S ⊠ U) (fun i => ⟨(col0 i).val - ((dS i * dT i : ℕ+) : ℕ), by
              change (col0 i).val - ((dS i * dT i : ℕ+) : ℕ) < ((dS i * dU i : ℕ+) : ℕ)
              have := hcolge i
              have h1 : (col0 i).val < ((dS i * dT i + dS i * dU i : ℕ+) : ℕ) := (col0 i).isLt
              have h2 : ((dS i * dT i + dS i * dU i : ℕ+) : ℕ)
                = ((dS i * dT i : ℕ+) : ℕ) + ((dS i * dU i : ℕ+) : ℕ) := PNat.add_coe _ _
              omega⟩) := by
        rw [directSumTensor_apply_block', dif_neg hcolnotT, dif_pos hcolge]
      rw [hRHS, kron_apply]
      -- Match arguments by `.val`.
      have hLeq : (fun i => kronDecodeL (jdx i))
          = (fun i => kronDecodeL ⟨(col0 i).val - ((dS i * dT i : ℕ+) : ℕ), by
              change (col0 i).val - ((dS i * dT i : ℕ+) : ℕ) < ((dS i * dU i : ℕ+) : ℕ)
              have := hcolge i
              have h1 : (col0 i).val < ((dS i * dT i + dS i * dU i : ℕ+) : ℕ) := (col0 i).isLt
              have h2 : ((dS i * dT i + dS i * dU i : ℕ+) : ℕ)
                = ((dS i * dT i : ℕ+) : ℕ) + ((dS i * dU i : ℕ+) : ℕ) := PNat.add_coe _ _
              omega⟩) := by
        funext i; apply Fin.ext
        simp only [kronDecodeL_val, PNat.add_coe, PNat.mul_coe]
        have hv := (distribCorr_val_ge_of_U (jdx i) (hbr i)).2
        change (col0 i).val - ((dS i * dT i : ℕ+) : ℕ) = _ at hv
        rw [PNat.mul_coe] at hv
        rw [hv, Nat.add_mul_div_left _ _ (by positivity : 0 < (dU i : ℕ))]
        have hmod : (jdx i).val % ((dT i : ℕ) + (dU i : ℕ)) - (dT i : ℕ) < (dU i : ℕ) := by
          have h1 : (jdx i).val % ((dT i : ℕ) + (dU i : ℕ)) < (dT i : ℕ) + (dU i : ℕ) :=
            Nat.mod_lt _ (by positivity)
          have h2 : 0 < (dU i : ℕ) := (dU i).pos
          omega
        rw [Nat.div_eq_of_lt hmod, Nat.zero_add]
      have hReq : (fun i => (⟨(kronDecodeR (jdx i)).val - (dT i : ℕ), by
              have h1 : ((kronDecodeR (jdx i)) : Fin ((dT i + dU i : ℕ+) : ℕ)).val
                < ((dT i + dU i : ℕ+) : ℕ) := (kronDecodeR (jdx i)).isLt
              have h2 : ((dT i + dU i : ℕ+) : ℕ) = (dT i : ℕ) + (dU i : ℕ) := PNat.add_coe _ _
              have := hUge i; omega⟩ : Fin (dU i)))
          = (fun i => kronDecodeR ⟨(col0 i).val - ((dS i * dT i : ℕ+) : ℕ), by
              change (col0 i).val - ((dS i * dT i : ℕ+) : ℕ) < ((dS i * dU i : ℕ+) : ℕ)
              have := hcolge i
              have h1 : (col0 i).val < ((dS i * dT i + dS i * dU i : ℕ+) : ℕ) := (col0 i).isLt
              have h2 : ((dS i * dT i + dS i * dU i : ℕ+) : ℕ)
                = ((dS i * dT i : ℕ+) : ℕ) + ((dS i * dU i : ℕ+) : ℕ) := PNat.add_coe _ _
              omega⟩) := by
        funext i; apply Fin.ext
        simp only [kronDecodeR_val, PNat.add_coe, PNat.mul_coe]
        have hv := (distribCorr_val_ge_of_U (jdx i) (hbr i)).2
        change (col0 i).val - ((dS i * dT i : ℕ+) : ℕ) = _ at hv
        rw [PNat.mul_coe] at hv
        rw [hv, Nat.add_mul_mod_self_left]
        have hmod : (jdx i).val % ((dT i : ℕ) + (dU i : ℕ)) - (dT i : ℕ) < (dU i : ℕ) := by
          have h1 : (jdx i).val % ((dT i : ℕ) + (dU i : ℕ)) < (dT i : ℕ) + (dU i : ℕ) :=
            Nat.mod_lt _ (by positivity)
          have h2 : 0 < (dU i : ℕ) := (dU i).pos
          omega
        rw [Nat.mod_eq_of_lt hmod]
      rw [hLeq, hReq]
    · -- Mixed: LHS `(T⊕U)` value is `0`; RHS direct-sum value is `0` as well.
      push_neg at hU
      obtain ⟨iL, hiL⟩ := hU
      -- LHS `(T⊕U)(decodeR jdx) = 0`.
      have hnotT : ¬ ∀ i, ((kronDecodeR (jdx i)) : Fin ((dT i + dU i : ℕ+) : ℕ)).val
          < (dT i : ℕ) := fun hall => absurd (hall iR) (not_lt.2 hiR)
      have hnotU : ¬ ∀ i, (dT i : ℕ)
          ≤ ((kronDecodeR (jdx i)) : Fin ((dT i + dU i : ℕ+) : ℕ)).val :=
        fun hall => absurd (hall iL) (not_le.2 hiL)
      have hTUval : (T ⊕ₜ U) (fun i => kronDecodeR (jdx i)) = 0 := by
        rw [directSumTensor_apply_block', dif_neg hnotT, dif_neg hnotU]
      rw [hTUval, mul_zero]
      -- RHS direct-sum value is `0`: `col0` is mixed.
      have hbrL : (jdx iL).val % ((dT iL : ℕ) + (dU iL : ℕ)) < (dT iL : ℕ) := by
        rw [← hkd]; exact hiL
      have hbrR : ¬ (jdx iR).val % ((dT iR : ℕ) + (dU iR : ℕ)) < (dT iR : ℕ) := by
        rw [← hkd]; exact not_lt.2 hiR
      have hcolLlt : (col0 iL).val < ((dS iL * dT iL : ℕ+) : ℕ) := by
        rw [PNat.mul_coe]; exact (distribCorr_val_lt_of_T (jdx iL) hbrL).1
      have hcolRge : ((dS iR * dT iR : ℕ+) : ℕ) ≤ (col0 iR).val := by
        rw [PNat.mul_coe]; exact (distribCorr_val_ge_of_U (jdx iR) hbrR).1
      have hnotcolT : ¬ ∀ i, (col0 i).val < ((dS i * dT i : ℕ+) : ℕ) :=
        fun hall => absurd (hall iR) (not_lt.2 hcolRge)
      have hnotcolU : ¬ ∀ i, ((dS i * dT i : ℕ+) : ℕ) ≤ (col0 i).val :=
        fun hall => absurd (hall iL) (not_le.2 hcolLlt)
      rw [directSumTensor_apply_block', dif_neg hnotcolT, dif_neg hnotcolU]

/-- **Distributivity of `⊠` over `⊕ₜ`**, forward `Restricts`, via the value
identity `left_distrib_value` and the permutation leg matrix selecting the
`distribCorr` column. -/
lemma left_distrib_kron_restricts {dS dT dU : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT) (U : KTensor F dU) :
    Restricts (S ⊠ (T ⊕ₜ U)) ((S ⊠ T) ⊕ₜ (S ⊠ U)) := by
  classical
  refine ⟨fun i a b => if b = distribCorr (dS i) (dT i) (dU i) a then 1 else 0, ?_⟩
  intro jdx
  rw [Finset.sum_eq_single (fun i => distribCorr (dS i) (dT i) (dU i) (jdx i))]
  · have hprod : (∏ i, (if distribCorr (dS i) (dT i) (dU i) (jdx i)
        = distribCorr (dS i) (dT i) (dU i) (jdx i) then (1 : F) else 0)) = 1 := by
      apply Finset.prod_eq_one; intro i _; rw [if_pos rfl]
    rw [hprod, one_mul, left_distrib_value]
  · intro col _ hcol
    have hne : ∃ i, col i ≠ distribCorr (dS i) (dT i) (dU i) (jdx i) := by
      by_contra h; push_neg at h; exact hcol (funext h)
    obtain ⟨i₀, hi₀⟩ := hne
    have hzero : (if col i₀ = distribCorr (dS i₀) (dT i₀) (dU i₀) (jdx i₀)
        then (1 : F) else 0) = 0 := by
      rw [if_neg]; intro h; exact hi₀ h
    rw [Finset.prod_eq_zero (Finset.mem_univ i₀) hzero, zero_mul]
  · intro hnot; exact (hnot (Finset.mem_univ _)).elim

/-- The per-leg distributivity correspondence is injective. -/
lemma distribCorr_injective {dS dT dU : ℕ+} :
    Function.Injective (distribCorr dS dT dU) := by
  intro a₁ a₂ h
  apply Fin.ext
  -- Reconstruct `a.val = t + (dT+dU)·s` from the two branches of `distribCorr`.
  have hrec : ∀ a : Fin ((dS * (dT + dU) : ℕ+) : ℕ),
      a.val = (a.val % ((dT : ℕ) + (dU : ℕ)))
        + ((dT : ℕ) + (dU : ℕ)) * (a.val / ((dT : ℕ) + (dU : ℕ))) := by
    intro a; exact (Nat.mod_add_div a.val _).symm
  rw [hrec a₁, hrec a₂]
  by_cases hb₁ : a₁.val % ((dT : ℕ) + (dU : ℕ)) < (dT : ℕ)
  · by_cases hb₂ : a₂.val % ((dT : ℕ) + (dU : ℕ)) < (dT : ℕ)
    · -- Both in the T-branch: equate the `(t + dT·s)` vals, then divide/mod by `dT`.
      have hv₁ := (distribCorr_val_lt_of_T a₁ hb₁).2
      have hv₂ := (distribCorr_val_lt_of_T a₂ hb₂).2
      rw [h] at hv₁
      rw [hv₂] at hv₁
      -- `hv₁ : t₂ + dT·s₂ = t₁ + dT·s₁` (as the equal `distribCorr` vals).
      set t₁ := a₁.val % ((dT : ℕ) + (dU : ℕ))
      set t₂ := a₂.val % ((dT : ℕ) + (dU : ℕ))
      set s₁ := a₁.val / ((dT : ℕ) + (dU : ℕ))
      set s₂ := a₂.val / ((dT : ℕ) + (dU : ℕ))
      -- From `t₂ + dT·s₂ = t₁ + dT·s₁` with `t₁,t₂ < dT`, get `t₁=t₂`, `s₁=s₂`.
      have ht₁ : t₁ < (dT : ℕ) := hb₁
      have ht₂ : t₂ < (dT : ℕ) := hb₂
      have hts : t₁ = t₂ ∧ s₁ = s₂ := by
        constructor
        · have := congrArg (· % (dT : ℕ)) hv₁
          simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht₁, Nat.mod_eq_of_lt ht₂]
            using this.symm
        · have := congrArg (· / (dT : ℕ)) hv₁
          simpa [Nat.add_mul_div_left _ _ (by positivity : 0 < (dT : ℕ)),
            Nat.div_eq_of_lt ht₁, Nat.div_eq_of_lt ht₂] using this.symm
      rw [hts.1, hts.2]
    · -- T-branch vs U-branch: vals land in disjoint ranges, contradiction.
      exfalso
      have hv₁ := (distribCorr_val_lt_of_T a₁ hb₁).1
      have hv₂ := (distribCorr_val_ge_of_U a₂ hb₂).1
      rw [h] at hv₁
      exact absurd hv₁ (not_lt.2 hv₂)
  · by_cases hb₂ : a₂.val % ((dT : ℕ) + (dU : ℕ)) < (dT : ℕ)
    · -- U-branch vs T-branch: symmetric contradiction.
      exfalso
      have hv₁ := (distribCorr_val_ge_of_U a₁ hb₁).1
      have hv₂ := (distribCorr_val_lt_of_T a₂ hb₂).1
      rw [h] at hv₁
      exact absurd hv₂ (not_lt.2 hv₁)
    · -- Both in the U-branch.
      have hg₁ := (distribCorr_val_ge_of_U a₁ hb₁)
      have hg₂ := (distribCorr_val_ge_of_U a₂ hb₂)
      -- `b₁' = (t₁-dT)+dU·s₁` and `b₂' = (t₂-dT)+dU·s₂` are equal (`b₁=b₂`).
      have hbb : (distribCorr dS dT dU a₁).val - (dS : ℕ) * (dT : ℕ)
          = (distribCorr dS dT dU a₂).val - (dS : ℕ) * (dT : ℕ) := by
        rw [h]
      rw [hg₁.2, hg₂.2] at hbb
      set t₁ := a₁.val % ((dT : ℕ) + (dU : ℕ))
      set t₂ := a₂.val % ((dT : ℕ) + (dU : ℕ))
      set s₁ := a₁.val / ((dT : ℕ) + (dU : ℕ))
      set s₂ := a₂.val / ((dT : ℕ) + (dU : ℕ))
      have ht₁ : t₁ < (dT : ℕ) + (dU : ℕ) := Nat.mod_lt _ (by positivity)
      have ht₂ : t₂ < (dT : ℕ) + (dU : ℕ) := Nat.mod_lt _ (by positivity)
      have htU₁ : t₁ - (dT : ℕ) < (dU : ℕ) := by have := not_lt.1 hb₁; omega
      have htU₂ : t₂ - (dT : ℕ) < (dU : ℕ) := by have := not_lt.1 hb₂; omega
      -- `(t₁-dT)+dU·s₁ = (t₂-dT)+dU·s₂` with `t-dT < dU`.
      have hts : t₁ - (dT : ℕ) = t₂ - (dT : ℕ) ∧ s₁ = s₂ := by
        constructor
        · have := congrArg (· % (dU : ℕ)) hbb
          simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt htU₁, Nat.mod_eq_of_lt htU₂] using this
        · have := congrArg (· / (dU : ℕ)) hbb
          simpa [Nat.add_mul_div_left _ _ (by positivity : 0 < (dU : ℕ)),
            Nat.div_eq_of_lt htU₁, Nat.div_eq_of_lt htU₂] using this
      have htt : t₁ = t₂ := by
        have h1 := not_lt.1 hb₁; have h2 := not_lt.1 hb₂; have := hts.1; omega
      rw [htt, hts.2]

/-- The per-leg distributivity correspondence is bijective. -/
lemma distribCorr_bijective {dS dT dU : ℕ+} :
    Function.Bijective (distribCorr dS dT dU) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨distribCorr_injective, ?_⟩
  rw [Fintype.card_fin, Fintype.card_fin, PNat.mul_coe, PNat.add_coe, PNat.add_coe,
    PNat.mul_coe, PNat.mul_coe, Nat.mul_add]

/-- The inverse of the per-leg distributivity correspondence. -/
noncomputable def distribCorrInv (dS dT dU : ℕ+)
    (b : Fin (((dS * dT + dS * dU : ℕ+)) : ℕ)) :
    Fin ((dS * (dT + dU) : ℕ+) : ℕ) :=
  (Equiv.ofBijective _ distribCorr_bijective).symm b

lemma distribCorr_distribCorrInv {dS dT dU : ℕ+}
    (b : Fin (((dS * dT + dS * dU : ℕ+)) : ℕ)) :
    distribCorr dS dT dU (distribCorrInv dS dT dU b) = b :=
  (Equiv.ofBijective _ distribCorr_bijective).apply_symm_apply b

/-- The reverse direction of distributivity, as a `Restricts` witness using the
inverse per-leg distributivity correspondence as a permutation leg matrix. -/
lemma right_distrib_kron_restricts {dS dT dU : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT) (U : KTensor F dU) :
    Restricts ((S ⊠ T) ⊕ₜ (S ⊠ U)) (S ⊠ (T ⊕ₜ U)) := by
  classical
  -- Leg matrix: row `a : Fin (sum)`, col `b : Fin (dS*(dT+dU))`; `1` iff
  -- `a = distribCorr b`, i.e. `b = distribCorrInv a`.
  refine ⟨fun i a b => if a = distribCorr (dS i) (dT i) (dU i) b then 1 else 0, ?_⟩
  intro jdx
  -- The unique nonzero column: the per-leg inverse of `jdx`.
  let col0 : ∀ i, Fin ((dS i * (dT i + dU i) : ℕ+) : ℕ) := fun i =>
    distribCorrInv (dS i) (dT i) (dU i) (jdx i)
  rw [Finset.sum_eq_single col0]
  · have hprod : (∏ i, (if jdx i = distribCorr (dS i) (dT i) (dU i) (col0 i)
        then (1 : F) else 0)) = 1 := by
      apply Finset.prod_eq_one; intro i _
      rw [if_pos (distribCorr_distribCorrInv (jdx i)).symm]
    rw [hprod, one_mul]
    -- Value: `((S⊠T)⊕(S⊠U)) jdx = (S ⊠ (T⊕U)) col0`, via the value identity at `col0`.
    have hval := left_distrib_value S T U col0
    have hjdx : (fun i => distribCorr (dS i) (dT i) (dU i) (col0 i)) = jdx := by
      funext i; exact distribCorr_distribCorrInv (jdx i)
    rw [hjdx] at hval
    exact hval.symm
  · intro col _ hcol
    have hne : ∃ i, col i ≠ col0 i := by
      by_contra h; push_neg at h; exact hcol (funext h)
    obtain ⟨i₀, hi₀⟩ := hne
    have hzero : (if jdx i₀ = distribCorr (dS i₀) (dT i₀) (dU i₀) (col i₀)
        then (1 : F) else 0) = 0 := by
      rw [if_neg]; intro h
      apply hi₀
      -- `jdx i₀ = distribCorr (col i₀)` and `jdx i₀ = distribCorr (col0 i₀)`, so injectivity.
      have h0 : jdx i₀ = distribCorr (dS i₀) (dT i₀) (dU i₀) (col0 i₀) :=
        (distribCorr_distribCorrInv (jdx i₀)).symm
      exact distribCorr_injective (h.symm.trans h0)
    rw [Finset.prod_eq_zero (Finset.mem_univ i₀) hzero, zero_mul]
  · intro hnot; exact (hnot (Finset.mem_univ _)).elim

/-- **Left distributivity** `S ⊠ (T ⊕ₜ U) ∼ₜ (S ⊠ T) ⊕ₜ (S ⊠ U)` (up to `∼ₜ`). -/
lemma left_distrib_kron {dS dT dU : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT) (U : KTensor F dU) :
    (S ⊠ (T ⊕ₜ U)) ∼ₜ ((S ⊠ T) ⊕ₜ (S ⊠ U)) :=
  ⟨left_distrib_kron_restricts S T U, right_distrib_kron_restricts S T U⟩

/-- **Right distributivity** `(T ⊕ₜ U) ⊠ S ∼ₜ (T ⊠ S) ⊕ₜ (U ⊠ S)` (up to `∼ₜ`),
derived from `left_distrib_kron` via Kronecker commutativity. -/
lemma right_distrib_kron {dS dT dU : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT) (U : KTensor F dU) :
    ((T ⊕ₜ U) ⊠ S) ∼ₜ ((T ⊠ S) ⊕ₜ (U ⊠ S)) :=
  (kron_comm (T ⊕ₜ U) S).trans
    ((left_distrib_kron S T U).trans
      (RestrictsEquiv.directSum_congr (kron_comm S T) (kron_comm S U)))

/-! ## The quotient `CommSemiring (TensorClass F k)`. -/

/-- The commutative semiring of `k`-tensor classes over `F` modulo
restriction-equivalence `∼ₜ`. -/
def TensorClass (F : Type u) [Field F] (k : ℕ) [NeZero k] : Type u :=
  Quotient (tensorSetoid (F := F) (k := k))

namespace TensorClass

/-- The class of a packaged tensor. -/
def mk (x : TT F k) : TensorClass F k := Quotient.mk _ x

/-- The additive operation `⊕ₜ` lifted to classes. -/
noncomputable instance : Add (TensorClass F k) where
  add := Quotient.map₂ (fun a b => ⟨_, a.2 ⊕ₜ b.2⟩)
    (fun _ _ h₁ _ _ h₂ => RestrictsEquiv.directSum_congr h₁ h₂)

/-- The Kronecker operation `⊠` lifted to classes. -/
noncomputable instance : Mul (TensorClass F k) where
  mul := Quotient.map₂ (fun a b => ⟨_, a.2 ⊠ b.2⟩)
    (fun _ _ h₁ _ _ h₂ => RestrictsEquiv.kron_congr h₁ h₂)

/-- The additive identity: the class of the canonical zero tensor. -/
instance : Zero (TensorClass F k) where
  zero := Quotient.mk _ ⟨_, (zeroT : KTensor F (fun _ => (1 : ℕ+)))⟩

/-- The multiplicative identity: the class of the rank-`1` unit tensor. -/
noncomputable instance : One (TensorClass F k) where
  one := Quotient.mk _ ⟨_, unitTensor F (k := k) 1⟩

@[simp] lemma mk_add (a b : TT F k) :
    mk a + mk b = mk ⟨_, a.2 ⊕ₜ b.2⟩ := rfl

@[simp] lemma mk_mul (a b : TT F k) :
    mk a * mk b = mk ⟨_, a.2 ⊠ b.2⟩ := rfl

lemma zero_def : (0 : TensorClass F k) = mk ⟨_, (zeroT : KTensor F (fun _ => (1 : ℕ+)))⟩ := rfl

lemma one_def : (1 : TensorClass F k) = mk ⟨_, unitTensor F (k := k) 1⟩ := rfl

/-- `mk` of `∼ₜ`-related tensors are equal. -/
lemma mk_eq_of_equiv {x y : TT F k} (h : x.2 ∼ₜ y.2) : mk x = mk y :=
  Quotient.sound h

noncomputable instance : CommSemiring (TensorClass F k) where
  add := (· + ·)
  add_assoc := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    exact mk_eq_of_equiv (directSum_assoc a.2 b.2 c.2)
  zero := 0
  zero_add := by
    rintro ⟨a⟩
    exact mk_eq_of_equiv (zero_directSum a.2)
  add_zero := by
    rintro ⟨a⟩
    exact mk_eq_of_equiv
      ((directSum_comm a.2 (zeroT : KTensor F (fun _ => (1 : ℕ+)))).trans (zero_directSum a.2))
  add_comm := by
    rintro ⟨a⟩ ⟨b⟩
    exact mk_eq_of_equiv (directSum_comm a.2 b.2)
  mul := (· * ·)
  left_distrib := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    exact mk_eq_of_equiv (left_distrib_kron a.2 b.2 c.2)
  right_distrib := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    exact mk_eq_of_equiv (right_distrib_kron c.2 a.2 b.2)
  zero_mul := by
    rintro ⟨a⟩
    exact mk_eq_of_equiv (zero_kron a.2)
  mul_zero := by
    rintro ⟨a⟩
    exact mk_eq_of_equiv
      ((kron_comm a.2 (zeroT : KTensor F (fun _ => (1 : ℕ+)))).trans (zero_kron a.2))
  mul_assoc := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    exact mk_eq_of_equiv (kron_assoc a.2 b.2 c.2)
  one := 1
  one_mul := by
    rintro ⟨a⟩
    exact mk_eq_of_equiv (one_kron a.2)
  mul_one := by
    rintro ⟨a⟩
    exact mk_eq_of_equiv (kron_one a.2)
  mul_comm := by
    rintro ⟨a⟩ ⟨b⟩
    exact mk_eq_of_equiv (kron_comm a.2 b.2)
  nsmul := nsmulRec
  npow := npowRec

end TensorClass

end Semicontinuity
