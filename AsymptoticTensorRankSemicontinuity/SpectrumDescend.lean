/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.MaxRankBound
import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Ring.Star

/-!
# §3.2 Auxiliary lemmas: spectral points descend when `F(⟨2⟩_{i,j}) = 1`

Source: the semicontinuity manuscript,
lines 1018–1051.

* `free_units` — **Lemma 3.6** (tex:1016-1021, `\label{lem:free-units}`).
* `free_splitting` — **Lemma 3.7** (tex:1029-1034, `\label{lem:free-splitting}`).
* `spec_descend` — **Lemma 3.8** (tex:1038-1045, `\label{lem:spec-descend}`).

Maps `γ`, `φ`: tex:1023-1025, require `k ≥ 3` for the descent to make sense.

The pair-unit tensor `⟨r⟩_{i,j}` is taken in its natural minimal format
(`d_i = d_j = r`, other legs `= 1`) — see `unitPairTensor` in `MaxRankBound.lean`.
-/

namespace Semicontinuity

universe u

variable {F : Type u} [Field F]

/-! ## Restriction-equivalence (tex:1014). -/

/-- Restriction-equivalence `S ∼ T` (tex:1014): `S ≤ T ∧ T ≤ S`. Note that `S, T`
    may have different formats: only the legs must be in 1-1 correspondence. -/
def RestrictsEquiv {k : ℕ} {dS dT : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT) : Prop :=
  Restricts S T ∧ Restricts T S

@[inherit_doc] scoped infix:50 " ∼ₜ " => RestrictsEquiv

lemma Restricts.of_eq_cast {k : ℕ} {dS dT : Fin k → ℕ+}
    {S : KTensor F dS} {T : KTensor F dT}
    (hfmt : ∀ i : Fin k, (dS i : ℕ) = (dT i : ℕ))
    (hval : ∀ jdx : (∀ i : Fin k, Fin (dS i)),
      S jdx = T (fun i => Fin.cast (hfmt i) (jdx i))) :
    Restricts S T := by
  classical
  refine ⟨fun i row col => if Fin.cast (hfmt i) row = col then 1 else 0, ?_⟩
  intro jdx
  let idx0 : ∀ i : Fin k, Fin (dT i) := fun i => Fin.cast (hfmt i) (jdx i)
  rw [Finset.sum_eq_single idx0]
  · rw [hval jdx]
    have hprod :
        (∏ i : Fin k,
          (if Fin.cast (hfmt i) (jdx i) = idx0 i then (1 : F) else 0)) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      simp [idx0]
    rw [hprod, one_mul]
  · intro idx _ hidx
    have hne : ∃ i : Fin k, Fin.cast (hfmt i) (jdx i) ≠ idx i := by
      by_contra h
      push_neg at h
      apply hidx
      funext i
      exact (h i).symm
    obtain ⟨i, hi⟩ := hne
    have hzero :
        (if Fin.cast (hfmt i) (jdx i) = idx i then (1 : F) else 0) = 0 := by
      simp [hi]
    have hprod_zero :
        (∏ j : Fin k,
          (if Fin.cast (hfmt j) (jdx j) = idx j then (1 : F) else 0)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hzero
    rw [hprod_zero, zero_mul]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

/-! ## Maps `γ` and `φ` between `k`- and `(k-1)`-tensors (tex:1023-1025). -/

/-- Output format of `γ`: legs `0..k-3` unchanged, last leg has dimension
    `d_{k-2} * d_{k-1}` (the merged legs). -/
noncomputable def dGamma {k : ℕ} (hk : 3 ≤ k) (d : Fin k → ℕ+) : Fin (k - 1) → ℕ+ :=
  fun i =>
    if h : (i : ℕ) < k - 2 then d ⟨i, by omega⟩
    else d ⟨k - 2, by omega⟩ * d ⟨k - 1, by omega⟩

/-- **`γ`** (tex:1023-1024): on simple tensors
    `γ(v_1 ⊗ ⋯ ⊗ v_k) = v_1 ⊗ ⋯ ⊗ v_{k-2} ⊗ (v_{k-1} ⊗ v_k)`. Requires `k ≥ 3`.

    On a multi-index `idx : ∀ i : Fin (k-1), Fin (dGamma hk d i)`, the value is
    `T` evaluated at the lifted multi-index obtained by:
    - For `j < k-2`: pass through `idx ⟨j, _⟩` (dim `d j`).
    - For `j = k-2, k-1`: decompose the merged last coordinate
      `idx ⟨k-2, _⟩ : Fin (d ⟨k-2⟩ * d ⟨k-1⟩)` via `finProdFinEquiv.symm`
      into a pair `(Fin (d ⟨k-2⟩), Fin (d ⟨k-1⟩))`. -/
noncomputable def gammaMap {k : ℕ} (hk : 3 ≤ k) {d : Fin k → ℕ+}
    (T : KTensor F d) : KTensor F (dGamma hk d) := by
  classical
  intro idx
  -- The decomposed last index of the input: `pair : Fin (d ⟨k-2⟩) × Fin (d ⟨k-1⟩)`.
  have hkm2_lt_km1 : (k - 2 : ℕ) < k - 1 := by omega
  have hdim_last : dGamma hk d ⟨k - 2, hkm2_lt_km1⟩
      = d ⟨k - 2, by omega⟩ * d ⟨k - 1, by omega⟩ := by
    unfold dGamma
    have h_not : ¬ ((⟨k - 2, hkm2_lt_km1⟩ : Fin (k - 1)) : ℕ) < k - 2 := by simp
    simp only [dif_neg h_not]
  let pair : Fin (d ⟨k - 2, by omega⟩ : ℕ) × Fin (d ⟨k - 1, by omega⟩ : ℕ) :=
    finProdFinEquiv.symm
      (Fin.cast (by rw [hdim_last, PNat.mul_coe]) (idx ⟨k - 2, hkm2_lt_km1⟩))
  refine T (fun j : Fin k => ?_)
  by_cases hj_lt : (j : ℕ) < k - 2
  · -- Pass through.
    have hj_lt_km1 : (j : ℕ) < k - 1 := by omega
    have hdim : dGamma hk d ⟨j, hj_lt_km1⟩ = d j := by
      unfold dGamma
      simp only [dif_pos hj_lt]
    exact Fin.cast (by rw [hdim]) (idx ⟨j, hj_lt_km1⟩)
  · by_cases hj_eq : (j : ℕ) = k - 2
    · -- Get the left component (leg k-2 of T).
      have hdj : d j = d ⟨k - 2, by omega⟩ := by
        congr 1; apply Fin.ext; exact hj_eq
      exact Fin.cast (by rw [hdj]) pair.1
    · -- j.val = k-1.
      have hj_eq_km1 : (j : ℕ) = k - 1 := by have := j.isLt; omega
      have hdj : d j = d ⟨k - 1, by omega⟩ := by
        congr 1; apply Fin.ext; exact hj_eq_km1
      exact Fin.cast (by rw [hdj]) pair.2

/-- Output format of `φ`: legs `0..k-2` are the input's legs, last leg has dim 1. -/
noncomputable def dPhi {k : ℕ} (_hk : 3 ≤ k) (e : Fin (k - 1) → ℕ+) : Fin k → ℕ+ :=
  fun i => if h : (i : ℕ) < k - 1 then e ⟨i, by omega⟩ else 1

/-- **`φ`** (tex:1025): `(k-1)`-tensors → `k`-tensors, `φ(U) = U ⊗ e_1`.

    On a multi-index `idx : ∀ i : Fin k, Fin (dPhi hk e i)`, the value is
    `U` applied to the restriction of `idx` to the first `k-1` legs, provided
    the last leg's coordinate (in `Fin 1`) is `0`. Since `Fin 1` has only one
    element this is always the case, so the definition is just `U` evaluated at
    the pruned multi-index. -/
noncomputable def phiMap {k : ℕ} (hk : 3 ≤ k) {e : Fin (k - 1) → ℕ+}
    (U : KTensor F e) : KTensor F (dPhi hk e) := by
  classical
  intro idx
  refine U (fun i : Fin (k - 1) => ?_)
  -- Lift i : Fin (k-1) into Fin k.
  have hi_lt : (i : ℕ) < k := by have := i.isLt; omega
  have hi_lt_km1 : (i : ℕ) < k - 1 := i.isLt
  -- idx ⟨i, hi_lt⟩ has type Fin (dPhi hk e ⟨i, hi_lt⟩) = Fin (e ⟨i, _⟩).
  have hdim : dPhi hk e ⟨i, hi_lt⟩ = e i := by
    unfold dPhi
    simp only [dif_pos hi_lt_km1]
  exact Fin.cast (by rw [hdim]) (idx ⟨i, hi_lt⟩)

/-! ## Strassen's asymptotic spectrum `Δ(F, k)` (tex:787-789). -/

/-- A spectral point on `k`-tensors over `F` (tex:781-783, `Δ(F, k)`). -/
structure SpectralPoint (k : ℕ) (F : Type u) [Field F] where
  toFun : ∀ {d : Fin k → ℕ+}, KTensor F d → ℝ
  /-- **Multiplicativity under `⊠`** (tex:781). -/
  mult : ∀ {dS dT : Fin k → ℕ+} (S : KTensor F dS) (T : KTensor F dT),
    toFun (S ⊠ T) = toFun S * toFun T
  /-- **Additivity under `⊕`** (tex:781). -/
  add : ∀ {dS dT : Fin k → ℕ+} (S : KTensor F dS) (T : KTensor F dT),
    toFun (S ⊕ₜ T) = toFun S + toFun T
  /-- **Normalization**: `F(⟨r⟩) = r` for the rank-`r` unit `k`-tensor (tex:781). -/
  normalize (r : ℕ+) : toFun (unitTensor (F := F) (k := k) r) = (r : ℕ)
  /-- **Monotonicity under restriction** (tex:781). -/
  mono : ∀ {dS dT : Fin k → ℕ+} (S : KTensor F dS) (T : KTensor F dT),
    S ≤ₜ T → toFun S ≤ toFun T

/-- A spectral point applies to tensors of any format: `φ T` for
`φ : SpectralPoint k F`. -/
instance {k : ℕ} : CoeFun (SpectralPoint k F)
    (fun _ => ∀ {d : Fin k → ℕ+}, KTensor F d → ℝ) :=
  ⟨SpectralPoint.toFun⟩

/-! ## Lemma 3.6 (tex:1016-1021). -/

/-- Pair-unit normalization used in Lemma 3.6 (paper tex:1016-1021).

The natural pair-unit `⟨1⟩_{i,j}` is restriction-equivalent to the rank-one unit
tensor, so every spectral point takes value `1` on it. -/
lemma SpectralPoint.unitPair_one {k : ℕ} (Fspec : SpectralPoint k F)
    (i j : Fin k) (hij : i ≠ j) :
    Fspec.toFun (unitPairTensor (F := F) 1 i j hij) = 1 := by
  classical
  have hdim : ∀ ℓ : Fin k, naturalPairFormat (1 : ℕ+) i j ℓ = 1 := by
    intro ℓ
    unfold naturalPairFormat
    by_cases hℓ : ℓ = i ∨ ℓ = j
    · simp [hℓ]
    · simp [hℓ]
  have hpair_le_unit :
      Restricts (unitPairTensor (F := F) (k := k) 1 i j hij)
        (unitTensor (F := F) (k := k) 1) := by
    refine ⟨fun _ _ _ => 1, ?_⟩
    intro jdx
    let idx0 : (∀ ℓ : Fin k, Fin ((fun _ : Fin k => (1 : ℕ+)) ℓ)) :=
      fun ℓ => Fin.cast
        (show (naturalPairFormat (1 : ℕ+) i j ℓ : ℕ) =
            (((fun _ : Fin k => (1 : ℕ+)) ℓ : ℕ+) : ℕ) by rw [hdim ℓ])
        (jdx ℓ)
    rw [Finset.sum_eq_single idx0]
    · unfold unitPairTensor unitTensor
      have hij_val : (jdx i).val = (jdx j).val := by
        have hi : (jdx i).val < 1 := by
          simpa [hdim i] using (jdx i).isLt
        have hj : (jdx j).val < 1 := by
          simpa [hdim j] using (jdx j).isLt
        omega
      have hall : ∀ a b : Fin k,
          idx0 a = idx0 b := by
        intro a b
        apply Fin.ext
        have ha : (idx0 a).val < 1 := by simp
        have hb : (idx0 b).val < 1 := by simp
        omega
      rw [if_pos hij_val]
      have hunit : (if ∀ a b : Fin k, idx0 a = idx0 b then (1 : F) else 0) = 1 := by
        rw [if_pos hall]
      simp [hunit]
    · intro idx _ hidx
      have : idx = idx0 := by
        funext ℓ
        apply Fin.ext
        have hidx_lt : (idx ℓ).val < 1 := by simp
        have hidx0_lt : (idx0 ℓ).val < 1 := by simp
        omega
      exact (hidx this).elim
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  have hunit_le_pair :
      Restricts (unitTensor (F := F) (k := k) 1)
        (unitPairTensor (F := F) (k := k) 1 i j hij) := by
    refine ⟨fun _ _ _ => 1, ?_⟩
    intro jdx
    let idx0 : (∀ ℓ : Fin k, Fin (naturalPairFormat (1 : ℕ+) i j ℓ)) :=
      fun ℓ => Fin.cast
        (show (((fun _ : Fin k => (1 : ℕ+)) ℓ : ℕ+) : ℕ) =
            (naturalPairFormat (1 : ℕ+) i j ℓ : ℕ) by rw [hdim ℓ])
        (jdx ℓ)
    rw [Finset.sum_eq_single idx0]
    · unfold unitPairTensor unitTensor
      have hall_jdx : ∀ a b : Fin k, jdx a = jdx b := by
        intro a b
        apply Fin.ext
        have ha : (jdx a).val < 1 := by simp
        have hb : (jdx b).val < 1 := by simp
        omega
      have hij_val :
          (idx0 i).val = (idx0 j).val := by
        have hi : (idx0 i).val < 1 := by
          simp [idx0]
        have hj : (idx0 j).val < 1 := by
          simp [idx0]
        omega
      rw [if_pos (hall_jdx)]
      simp [hij_val]
    · intro idx _ hidx
      have : idx = idx0 := by
        funext ℓ
        apply Fin.ext
        have hidx_lt : (idx ℓ).val < 1 := by
          simpa [hdim ℓ] using (idx ℓ).isLt
        have hidx0_lt : (idx0 ℓ).val < 1 := by
          simp [idx0]
        omega
      exact (hidx this).elim
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  have hle_pair_unit := Fspec.mono
    (unitPairTensor (F := F) (k := k) 1 i j hij)
    (unitTensor (F := F) (k := k) 1) hpair_le_unit
  have hle_unit_pair := Fspec.mono
    (unitTensor (F := F) (k := k) 1)
    (unitPairTensor (F := F) (k := k) 1 i j hij) hunit_le_pair
  have hnorm := Fspec.normalize (1 : ℕ+)
  have hle_pair_one :
      Fspec.toFun (unitPairTensor (F := F) (k := k) 1 i j hij) ≤ 1 := by
    simpa [hnorm] using hle_pair_unit
  have hone_le_pair :
      (1 : ℝ) ≤ Fspec.toFun (unitPairTensor (F := F) (k := k) 1 i j hij) := by
    simpa [hnorm] using hle_unit_pair
  exact le_antisymm hle_pair_one hone_le_pair

/-- **Pair-unit Kronecker multiplicativity** (tensor-level, tex:1016-1021):
`⟨r·s⟩_{i,j} ∼ₜ ⟨r⟩_{i,j} ⊠ ⟨s⟩_{i,j}`.  The `Fin (r·s) ≃ Fin r × Fin s` div/mod
reindex on legs `i,j` (identity elsewhere) gives restrictions in both directions. -/
lemma unitPairTensor_kron_equiv {k : ℕ} (i j : Fin k) (hij : i ≠ j) (r s : ℕ+) :
    RestrictsEquiv (unitPairTensor (F := F) (r * s) i j hij)
      ((unitPairTensor (F := F) r i j hij) ⊠ (unitPairTensor (F := F) s i j hij)) := by
  classical
  -- Format equality between `naturalPairFormat (r*s)` and the Kron of two
  -- `naturalPairFormat`s: both equal `r*s` on legs i,j and `1` elsewhere.
  have hdim_eq : ∀ ℓ : Fin k,
      (naturalPairFormat (r * s) i j ℓ : ℕ) =
        (naturalPairFormat r i j ℓ * naturalPairFormat s i j ℓ : ℕ+) := by
    intro ℓ
    unfold naturalPairFormat
    by_cases hℓ : ℓ = i ∨ ℓ = j
    · simp [hℓ, PNat.mul_coe]
    · simp [hℓ]
  -- The unique nonzero contributor for the sum, mapping `jdx` on LHS-format to
  -- the same `Fin.cast`-ed multi-index on RHS-format.
  -- Helper: equality of values in `Fin (r*s)` iff div/mod by `s` both agree.
  -- Leg-specific dimension reductions (legs i and j).
  have hnpf_s_i : naturalPairFormat s i j i = s := by unfold naturalPairFormat; simp
  have hnpf_s_j : naturalPairFormat s i j j = s := by unfold naturalPairFormat; simp
  have hnpf_r_i : naturalPairFormat r i j i = r := by unfold naturalPairFormat; simp
  have hnpf_r_j : naturalPairFormat r i j j = r := by unfold naturalPairFormat; simp
  have hnpf_rs_i : naturalPairFormat (r * s) i j i = r * s := by
    unfold naturalPairFormat; simp
  have hnpf_rs_j : naturalPairFormat (r * s) i j j = r * s := by
    unfold naturalPairFormat; simp
  have hval_iff : ∀ (a b : ℕ),
      a < (r : ℕ) * s → b < (r : ℕ) * s →
      (a = b ↔ a / (s : ℕ) = b / s ∧ a % s = b % s) := by
    intro a b _ha _hb
    constructor
    · intro h; exact ⟨by rw [h], by rw [h]⟩
    · rintro ⟨h1, h2⟩
      have ka : (s : ℕ) * (a / s) + a % s = a := Nat.div_add_mod a s
      have kb : (s : ℕ) * (b / s) + b % s = b := Nat.div_add_mod b s
      have : (s : ℕ) * (a / s) = (s : ℕ) * (b / s) := by rw [h1]
      omega
  -- Direction 1: `unitPairTensor (r*s) ≤ unitPairTensor r ⊠ unitPairTensor s`.
  have hLR : Restricts (unitPairTensor (F := F) (r * s) i j hij)
      ((unitPairTensor (F := F) r i j hij) ⊠ (unitPairTensor (F := F) s i j hij)) := by
    refine ⟨fun ℓ a b => if a.val = b.val then 1 else 0, ?_⟩
    intro jdx
    let idx0 : ∀ ℓ : Fin k,
        Fin (((fun ℓ => naturalPairFormat r i j ℓ * naturalPairFormat s i j ℓ) ℓ : ℕ+) : ℕ) :=
      fun ℓ => Fin.cast (hdim_eq ℓ) (jdx ℓ)
    rw [Finset.sum_eq_single idx0]
    · -- Compute the coefficient: product is 1 by definitional cast.
      have hprod : (∏ ℓ : Fin k,
          (if (jdx ℓ).val = (idx0 ℓ).val then (1 : F) else 0)) = 1 := by
        apply Finset.prod_eq_one
        intro ℓ _
        simp [idx0]
      rw [hprod, one_mul]
      -- Now compare unitPairTensor (r*s) jdx with the Kron of the two pair-units.
      unfold unitPairTensor kroneckerTensor
      have hi_val : (jdx i).val = (idx0 i).val := by simp [idx0]
      have hj_val : (jdx j).val = (idx0 j).val := by simp [idx0]
      -- The leg-i,j of idx0 lies in Fin (r*s).
      -- `kronLeftIndex idx0 i` has Fin.val = (idx0 i).val / s; similarly leg j.
      -- `kronRightIndex idx0 i` has Fin.val = (idx0 i).val % s; similarly leg j.
      have hkL_i : (kronLeftIndex idx0 i).val = (idx0 i).val / s := by
        simp [kronLeftIndex, finProdFinEquiv_symm_apply, Fin.divNat, hnpf_s_i]
      have hkL_j : (kronLeftIndex idx0 j).val = (idx0 j).val / s := by
        simp [kronLeftIndex, finProdFinEquiv_symm_apply, Fin.divNat, hnpf_s_j]
      have hkR_i : (kronRightIndex idx0 i).val = (idx0 i).val % s := by
        simp [kronRightIndex, finProdFinEquiv_symm_apply, Fin.modNat, hnpf_s_i]
      have hkR_j : (kronRightIndex idx0 j).val = (idx0 j).val % s := by
        simp [kronRightIndex, finProdFinEquiv_symm_apply, Fin.modNat, hnpf_s_j]
      have hidx0_i_lt : (idx0 i).val < (r : ℕ) * s := by
        have h := (idx0 i).isLt
        change (idx0 i).val < (r : ℕ) * s
        have heq : ((naturalPairFormat r i j i * naturalPairFormat s i j i : ℕ+) : ℕ)
            = (r : ℕ) * s := by rw [hnpf_r_i, hnpf_s_i, PNat.mul_coe]
        rw [show (idx0 i).val = (idx0 i).val from rfl]
        rw [← heq]; exact h
      have hidx0_j_lt : (idx0 j).val < (r : ℕ) * s := by
        have h := (idx0 j).isLt
        have heq : ((naturalPairFormat r i j j * naturalPairFormat s i j j : ℕ+) : ℕ)
            = (r : ℕ) * s := by rw [hnpf_r_j, hnpf_s_j, PNat.mul_coe]
        rw [← heq]; exact h
      by_cases h : (jdx i).val = (jdx j).val
      · have hidx0 : (idx0 i).val = (idx0 j).val := by rw [← hi_val, ← hj_val, h]
        have hL : (kronLeftIndex idx0 i).val = (kronLeftIndex idx0 j).val := by
          rw [hkL_i, hkL_j, hidx0]
        have hR : (kronRightIndex idx0 i).val = (kronRightIndex idx0 j).val := by
          rw [hkR_i, hkR_j, hidx0]
        simp [h, hL, hR]
      · have hidx0 : (idx0 i).val ≠ (idx0 j).val := by rw [← hi_val, ← hj_val]; exact h
        -- Either div or mod must differ.
        have hne : (idx0 i).val / s ≠ (idx0 j).val / s ∨
            (idx0 i).val % s ≠ (idx0 j).val % s := by
          by_contra hboth
          push_neg at hboth
          obtain ⟨hd, hm⟩ := hboth
          exact hidx0
            ((hval_iff (idx0 i).val (idx0 j).val hidx0_i_lt hidx0_j_lt).mpr ⟨hd, hm⟩)
        rcases hne with hdne | hmne
        · have hL : (kronLeftIndex idx0 i).val ≠ (kronLeftIndex idx0 j).val := by
            rw [hkL_i, hkL_j]; exact hdne
          simp [h, hL]
        · have hR : (kronRightIndex idx0 i).val ≠ (kronRightIndex idx0 j).val := by
            rw [hkR_i, hkR_j]; exact hmne
          simp [h, hR]
    · intro idx _ hidx
      have hne : ∃ ℓ : Fin k, (jdx ℓ).val ≠ (idx ℓ).val := by
        by_contra h
        push_neg at h
        apply hidx
        funext ℓ
        apply Fin.ext
        have hv_idx0 : (idx0 ℓ).val = (jdx ℓ).val := by simp [idx0]
        rw [hv_idx0, h ℓ]
      obtain ⟨ℓ, hℓ⟩ := hne
      have hzero : (if (jdx ℓ).val = (idx ℓ).val then (1 : F) else 0) = 0 := by
        simp [hℓ]
      have hprod_zero :
          (∏ m : Fin k,
            (if (jdx m).val = (idx m).val then (1 : F) else 0)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ ℓ) hzero
      rw [hprod_zero, zero_mul]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  -- Direction 2: `unitPairTensor r ⊠ unitPairTensor s ≤ unitPairTensor (r*s)`.
  have hRL : Restricts ((unitPairTensor (F := F) r i j hij) ⊠
        (unitPairTensor (F := F) s i j hij))
      (unitPairTensor (F := F) (r * s) i j hij) := by
    refine ⟨fun ℓ a b => if a.val = b.val then 1 else 0, ?_⟩
    intro jdx
    -- jdx : ∀ ℓ, Fin (naturalPairFormat r ℓ * naturalPairFormat s ℓ)
    let idx0 : ∀ ℓ : Fin k, Fin (naturalPairFormat (r * s) i j ℓ) :=
      fun ℓ => Fin.cast (hdim_eq ℓ).symm (jdx ℓ)
    rw [Finset.sum_eq_single idx0]
    · have hprod : (∏ ℓ : Fin k,
          (if (jdx ℓ).val = (idx0 ℓ).val then (1 : F) else 0)) = 1 := by
        apply Finset.prod_eq_one
        intro ℓ _
        simp [idx0]
      rw [hprod, one_mul]
      unfold unitPairTensor kroneckerTensor
      have hi_val : (jdx i).val = (idx0 i).val := by simp [idx0]
      have hj_val : (jdx j).val = (idx0 j).val := by simp [idx0]
      have hkL_i : (kronLeftIndex jdx i).val = (jdx i).val / s := by
        simp [kronLeftIndex, finProdFinEquiv_symm_apply, Fin.divNat, hnpf_s_i]
      have hkL_j : (kronLeftIndex jdx j).val = (jdx j).val / s := by
        simp [kronLeftIndex, finProdFinEquiv_symm_apply, Fin.divNat, hnpf_s_j]
      have hkR_i : (kronRightIndex jdx i).val = (jdx i).val % s := by
        simp [kronRightIndex, finProdFinEquiv_symm_apply, Fin.modNat, hnpf_s_i]
      have hkR_j : (kronRightIndex jdx j).val = (jdx j).val % s := by
        simp [kronRightIndex, finProdFinEquiv_symm_apply, Fin.modNat, hnpf_s_j]
      have hjdx_i_lt : (jdx i).val < (r : ℕ) * s := by
        have h := (jdx i).isLt
        have heq : ((naturalPairFormat r i j i * naturalPairFormat s i j i : ℕ+) : ℕ)
            = (r : ℕ) * s := by rw [hnpf_r_i, hnpf_s_i, PNat.mul_coe]
        rw [← heq]; exact h
      have hjdx_j_lt : (jdx j).val < (r : ℕ) * s := by
        have h := (jdx j).isLt
        have heq : ((naturalPairFormat r i j j * naturalPairFormat s i j j : ℕ+) : ℕ)
            = (r : ℕ) * s := by rw [hnpf_r_j, hnpf_s_j, PNat.mul_coe]
        rw [← heq]; exact h
      by_cases h : (idx0 i).val = (idx0 j).val
      · have hjdx : (jdx i).val = (jdx j).val := by rw [hi_val, hj_val, h]
        have hL : (kronLeftIndex jdx i).val = (kronLeftIndex jdx j).val := by
          rw [hkL_i, hkL_j, hjdx]
        have hR : (kronRightIndex jdx i).val = (kronRightIndex jdx j).val := by
          rw [hkR_i, hkR_j, hjdx]
        simp [h, hL, hR]
      · have hjdx : (jdx i).val ≠ (jdx j).val := by rw [hi_val, hj_val]; exact h
        have hne : (jdx i).val / s ≠ (jdx j).val / s ∨
            (jdx i).val % s ≠ (jdx j).val % s := by
          by_contra hboth
          push_neg at hboth
          obtain ⟨hd, hm⟩ := hboth
          exact hjdx
            ((hval_iff (jdx i).val (jdx j).val hjdx_i_lt hjdx_j_lt).mpr ⟨hd, hm⟩)
        rcases hne with hdne | hmne
        · have hL : (kronLeftIndex jdx i).val ≠ (kronLeftIndex jdx j).val := by
            rw [hkL_i, hkL_j]; exact hdne
          simp [h, hL]
        · have hR : (kronRightIndex jdx i).val ≠ (kronRightIndex jdx j).val := by
            rw [hkR_i, hkR_j]; exact hmne
          simp [h, hR]
    · intro idx _ hidx
      have hne : ∃ ℓ : Fin k, (jdx ℓ).val ≠ (idx ℓ).val := by
        by_contra h
        push_neg at h
        apply hidx
        funext ℓ
        apply Fin.ext
        have hv_idx0 : (idx0 ℓ).val = (jdx ℓ).val := by simp [idx0]
        rw [hv_idx0, h ℓ]
      obtain ⟨ℓ, hℓ⟩ := hne
      have hzero : (if (jdx ℓ).val = (idx ℓ).val then (1 : F) else 0) = 0 := by
        simp [hℓ]
      have hprod_zero :
          (∏ m : Fin k,
            (if (jdx m).val = (idx m).val then (1 : F) else 0)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ ℓ) hzero
      rw [hprod_zero, zero_mul]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  exact ⟨hLR, hRL⟩

/-- Multiplicativity of pair-units used in Lemma 3.6 (paper tex:1016-1021).

The tensor `⟨rs⟩_{i,j}` is restriction-equivalent to
`⟨r⟩_{i,j} ⊠ ⟨s⟩_{i,j}`; applying monotonicity in both directions and the
spectral-point multiplication axiom gives this equality. -/
lemma SpectralPoint.unitPair_mul {k : ℕ} (Fspec : SpectralPoint k F)
    (i j : Fin k) (hij : i ≠ j) (r s : ℕ+) :
    Fspec.toFun (unitPairTensor (F := F) (r * s) i j hij) =
      Fspec.toFun (unitPairTensor (F := F) r i j hij) *
        Fspec.toFun (unitPairTensor (F := F) s i j hij) := by
  classical
  have hequiv := unitPairTensor_kron_equiv (F := F) i j hij r s
  have hLR_mono := Fspec.mono _ _ hequiv.1
  have hRL_mono := Fspec.mono _ _ hequiv.2
  have hmult := Fspec.mult
    (unitPairTensor (F := F) r i j hij) (unitPairTensor (F := F) s i j hij)
  rw [hmult] at hLR_mono hRL_mono
  linarith

/-! ## Leg-permutation pullback `SpectralPoint.reindex`.

For a permutation `σ : Equiv.Perm (Fin k)` we define the leg-permutation
`legReindex σ T : KTensor F (fun i => d (σ i))` of a tensor, and pull a spectral
point back along it. Reindexing legs preserves all of `⊠`, `⊕ₜ`, unit tensors,
and restriction, so `Fspec.reindex σ` is again a spectral point; moreover the
two value-sets coincide (`reindex_iUnion_range`). This is the correct form of
the leg-permutation WLOG: it produces a *different* spectral point with the
*same* value set, on which a chosen pair sits at a prescribed position. -/

/-- **Leg-permutation of a tensor**: reindex the legs of `T` by `σ`.

    `legReindex σ T : KTensor F (fun i => d (σ i))`, defined as precomposition of
    the index family with the bijection `Equiv.piCongrLeft (fun j => Fin (d j)) σ`. -/
def KTensor.legReindex {k : ℕ} {d : Fin k → ℕ+} (σ : Equiv.Perm (Fin k))
    (T : KTensor F d) : KTensor F (fun i => d (σ i)) :=
  fun jdx => T (Equiv.piCongrLeft (fun i => Fin ((d i : ℕ))) σ jdx)

/-- Value of `legReindex` at a multi-index, unfolded. -/
lemma KTensor.legReindex_apply {k : ℕ} {d : Fin k → ℕ+} (σ : Equiv.Perm (Fin k))
    (T : KTensor F d) (jdx : ∀ i : Fin k, Fin (d (σ i))) :
    KTensor.legReindex σ T jdx = T (Equiv.piCongrLeft (fun i => Fin ((d i : ℕ))) σ jdx) :=
  rfl

/-- `legReindex` commutes with the Kronecker product `⊠`. -/
lemma KTensor.legReindex_kron {k : ℕ} {dS dT : Fin k → ℕ+} (σ : Equiv.Perm (Fin k))
    (S : KTensor F dS) (T : KTensor F dT) :
    KTensor.legReindex σ (S ⊠ T)
      = (KTensor.legReindex σ S) ⊠ (KTensor.legReindex σ T) := by
  funext jdx
  simp only [KTensor.legReindex, kroneckerTensor]
  congr 1
  · congr 1
    funext i
    apply Fin.eq_of_val_eq
    simp only [kronLeftIndex, Equiv.piCongrLeft_apply_eq_cast,
      finProdFinEquiv_symm_apply, Fin.divNat]
    simp only [Fin.val_eq_val_of_heq (cast_heq _ _), Equiv.apply_symm_apply]
  · congr 1
    funext i
    apply Fin.eq_of_val_eq
    simp only [kronRightIndex, Equiv.piCongrLeft_apply_eq_cast,
      finProdFinEquiv_symm_apply, Fin.modNat]
    simp only [Fin.val_eq_val_of_heq (cast_heq _ _), Equiv.apply_symm_apply]

/-- Reindexing the leg-coordinate `(piCongrLeft σ jdx) i` equals `jdx (σ.symm i)`
    at the level of underlying `.val`s (no cast on naturals). -/
lemma piCongrLeft_val {k : ℕ} {d : Fin k → ℕ+} (σ : Equiv.Perm (Fin k))
    (jdx : ∀ i : Fin k, Fin (d (σ i))) (i : Fin k) :
    ((Equiv.piCongrLeft (fun i => Fin ((d i : ℕ))) σ jdx) i).val
      = (jdx (σ.symm i)).val := by
  rw [Equiv.piCongrLeft_apply_eq_cast]
  exact Fin.val_eq_val_of_heq (cast_heq _ _)

/-- The block condition "all legs of `piCongrLeft σ jdx` lie below `dS`" is
    equivalent (after the leg-permutation) to "all legs of `jdx` lie below
    `dS ∘ σ`". -/
lemma piCongrLeft_forall_lt {k : ℕ} {dS dT : Fin k → ℕ+} (σ : Equiv.Perm (Fin k))
    (jdx : ∀ i : Fin k, Fin ((fun i => dS (σ i) + dT (σ i)) i)) :
    (∀ i : Fin k,
      ((Equiv.piCongrLeft (fun i => Fin (((fun i => dS i + dT i) i : ℕ+) : ℕ)) σ jdx) i).val
        < (dS i : ℕ))
      ↔ (∀ i : Fin k, (jdx i).val < (dS (σ i) : ℕ)) := by
  constructor
  · intro h i
    have := h (σ i)
    rwa [piCongrLeft_val, Equiv.symm_apply_apply] at this
  · intro h i
    rw [piCongrLeft_val]
    have := h (σ.symm i)
    rwa [Equiv.apply_symm_apply] at this

/-- The block condition "all legs of `piCongrLeft σ jdx` lie at/above `dS`". -/
lemma piCongrLeft_forall_le {k : ℕ} {dS dT : Fin k → ℕ+} (σ : Equiv.Perm (Fin k))
    (jdx : ∀ i : Fin k, Fin ((fun i => dS (σ i) + dT (σ i)) i)) :
    (∀ i : Fin k,
      (dS i : ℕ) ≤
        ((Equiv.piCongrLeft (fun i => Fin (((fun i => dS i + dT i) i : ℕ+) : ℕ)) σ jdx) i).val)
      ↔ (∀ i : Fin k, (dS (σ i) : ℕ) ≤ (jdx i).val) := by
  constructor
  · intro h i
    have := h (σ i)
    rwa [piCongrLeft_val, Equiv.symm_apply_apply] at this
  · intro h i
    rw [piCongrLeft_val]
    have := h (σ.symm i)
    rwa [Equiv.apply_symm_apply] at this

/-- `legReindex` commutes with the direct sum `⊕ₜ`. -/
lemma KTensor.legReindex_directSum {k : ℕ} {dS dT : Fin k → ℕ+}
    (σ : Equiv.Perm (Fin k)) (S : KTensor F dS) (T : KTensor F dT) :
    KTensor.legReindex σ (S ⊕ₜ T)
      = (KTensor.legReindex σ S) ⊕ₜ (KTensor.legReindex σ T) := by
  classical
  funext jdx
  simp only [KTensor.legReindex, directSumTensor]
  by_cases hSL : ∀ i : Fin k, (jdx i).val < (dS (σ i) : ℕ)
  · -- All legs in dS-block.
    rw [dif_pos ((piCongrLeft_forall_lt σ jdx).2 hSL), dif_pos hSL]
    congr 1
    funext i
    apply Fin.ext
    simp only [piCongrLeft_val]
  · by_cases hTL : ∀ i : Fin k, (dS (σ i) : ℕ) ≤ (jdx i).val
    · -- All legs in dT-block.
      rw [dif_neg (fun h => hSL ((piCongrLeft_forall_lt σ jdx).1 h)),
        dif_neg hSL,
        dif_pos ((piCongrLeft_forall_le σ jdx).2 hTL), dif_pos hTL]
      congr 1
      funext i
      apply Fin.ext
      simp only [piCongrLeft_val, Equiv.apply_symm_apply]
    · -- Off block-diagonal: both 0.
      rw [dif_neg (fun h => hSL ((piCongrLeft_forall_lt σ jdx).1 h)),
        dif_neg hSL,
        dif_neg (fun h => hTL ((piCongrLeft_forall_le σ jdx).1 h)), dif_neg hTL]

/-- `legReindex` fixes the unit tensor `⟨r⟩` (permutation-invariant). -/
lemma KTensor.legReindex_unitTensor {k : ℕ} (σ : Equiv.Perm (Fin k)) (r : ℕ+) :
    KTensor.legReindex σ (unitTensor (F := F) (k := k) r)
      = unitTensor (F := F) (k := k) r := by
  funext jdx
  simp only [KTensor.legReindex, unitTensor]
  congr 1
  apply propext
  constructor
  · intro h a b
    apply Fin.ext
    have := h (σ a) (σ b)
    rwa [Fin.ext_iff, piCongrLeft_val, piCongrLeft_val,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
  · intro h a b
    apply Fin.ext
    rw [piCongrLeft_val, piCongrLeft_val]
    exact Fin.ext_iff.1 (h (σ.symm a) (σ.symm b))

/-- Round-trip: `legReindex σ.symm (legReindex σ T)` recovers `T` (up to the
    defeq format `fun i => d (σ.symm (σ i))`). Stated via `piCongrLeft`. -/
lemma KTensor.legReindex_legReindex {k : ℕ} {d : Fin k → ℕ+} (σ : Equiv.Perm (Fin k))
    (T : KTensor F d) (jdx : ∀ i : Fin k, Fin (d (σ (σ.symm i)))) :
    KTensor.legReindex σ.symm (KTensor.legReindex σ T) jdx
      = T (fun i => Fin.cast (by rw [Equiv.apply_symm_apply]) (jdx i)) := by
  simp only [KTensor.legReindex]
  congr 1
  funext i
  apply Fin.eq_of_val_eq
  rw [piCongrLeft_val, piCongrLeft_val, Equiv.symm_symm]
  rw [Fin.val_cast]
  exact Fin.val_eq_val_of_heq (congr_arg_heq jdx (Equiv.apply_symm_apply σ i))

/-- `legReindex` preserves restriction: reindex the leg-matrices by `σ`. -/
lemma KTensor.legReindex_Restricts {k : ℕ} {dS dT : Fin k → ℕ+}
    (σ : Equiv.Perm (Fin k)) {S : KTensor F dS} {T : KTensor F dT}
    (h : Restricts S T) :
    Restricts (KTensor.legReindex σ S) (KTensor.legReindex σ T) := by
  classical
  obtain ⟨A, hA⟩ := h
  refine ⟨fun i => A (σ i), ?_⟩
  intro jdx
  simp only [KTensor.legReindex]
  rw [hA]
  -- Reindex the outer sum over `idx : ∀ i, Fin (dT i)` by `piCongrLeft σ`.
  rw [← Equiv.sum_comp (Equiv.piCongrLeft (fun i => Fin ((dT i : ℕ))) σ)
      (fun idx => (∏ i, A i ((Equiv.piCongrLeft (fun i => Fin ((dS i : ℕ))) σ jdx) i) (idx i))
        * T idx)]
  refine Finset.sum_congr rfl ?_
  intro jdx' _
  congr 1
  -- Reindex the product over `Fin k` by `σ`.
  rw [← Equiv.prod_comp σ
      (fun i => A i ((Equiv.piCongrLeft (fun i => Fin ((dS i : ℕ))) σ jdx) i)
        ((Equiv.piCongrLeft (fun i => Fin ((dT i : ℕ))) σ jdx') i))]
  refine Finset.prod_congr rfl ?_
  intro i _
  rw [Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply]

/-- The round-trip `legReindex σ.symm (legReindex σ S)` restricts to `S`
    (they are equal up to the format-cast `dS (σ (σ.symm i)) = dS i`). -/
lemma KTensor.legReindex_legReindex_restricts {k : ℕ} {d : Fin k → ℕ+}
    (σ : Equiv.Perm (Fin k)) (S : KTensor F d) :
    Restricts (KTensor.legReindex σ.symm (KTensor.legReindex σ S)) S :=
  Restricts.of_eq_cast (fun i => by rw [Equiv.apply_symm_apply])
    (fun jdx => KTensor.legReindex_legReindex σ S jdx)

/-- `S` restricts to the round-trip `legReindex σ.symm (legReindex σ S)`. -/
lemma KTensor.restricts_legReindex_legReindex {k : ℕ} {d : Fin k → ℕ+}
    (σ : Equiv.Perm (Fin k)) (S : KTensor F d) :
    Restricts S (KTensor.legReindex σ.symm (KTensor.legReindex σ S)) := by
  refine Restricts.of_eq_cast (fun i => by rw [Equiv.apply_symm_apply])
    (fun jdx => ?_)
  rw [KTensor.legReindex_legReindex]
  congr 1

/-- `legReindex` reflects restriction (apply the forward direction with `σ⁻¹`). -/
lemma KTensor.legReindex_Restricts_iff {k : ℕ} {dS dT : Fin k → ℕ+}
    (σ : Equiv.Perm (Fin k)) {S : KTensor F dS} {T : KTensor F dT}
    (h : Restricts (KTensor.legReindex σ S) (KTensor.legReindex σ T)) :
    Restricts S T := by
  have h2 := KTensor.legReindex_Restricts σ.symm h
  exact (KTensor.restricts_legReindex_legReindex σ S).trans
    (h2.trans (KTensor.legReindex_legReindex_restricts σ T))

/-- **Leg-permutation pullback** of a spectral point along `σ`.

    `Fspec.reindex σ` evaluates `Fspec` on the `σ`-reindexed tensor. Because
    leg-reindexing preserves `⊠`, `⊕ₜ`, unit tensors, and restriction, this is
    again a spectral point. -/
def SpectralPoint.reindex {k : ℕ} (Fspec : SpectralPoint k F)
    (σ : Equiv.Perm (Fin k)) : SpectralPoint k F where
  toFun T := Fspec.toFun (KTensor.legReindex σ T)
  mult S T := by rw [KTensor.legReindex_kron]; exact Fspec.mult _ _
  add S T := by rw [KTensor.legReindex_directSum]; exact Fspec.add _ _
  normalize r := by rw [KTensor.legReindex_unitTensor]; exact Fspec.normalize r
  mono S T h := Fspec.mono _ _ (KTensor.legReindex_Restricts σ h)

@[simp] lemma SpectralPoint.reindex_toFun {k : ℕ} (Fspec : SpectralPoint k F)
    (σ : Equiv.Perm (Fin k)) {d : Fin k → ℕ+} (T : KTensor F d) :
    (Fspec.reindex σ).toFun T = Fspec.toFun (KTensor.legReindex σ T) := rfl

/-- **Value-set equality**: the leg-permutation pullback has the same value set
    as the original spectral point (since `legReindex σ` is a bijection of
    tensors that ranges over all formats as `d` does). -/
lemma SpectralPoint.reindex_iUnion_range {k : ℕ} (Fspec : SpectralPoint k F)
    (σ : Equiv.Perm (Fin k)) :
    (⋃ d : Fin k → ℕ+,
        Set.range (fun T : KTensor F d => (Fspec.reindex σ).toFun T)) =
      (⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor F d => Fspec.toFun T)) := by
  apply Set.eq_of_subset_of_subset
  · -- A value `Fspec (legReindex σ T)` is realized at format `d ∘ σ`.
    intro v hv
    rw [Set.mem_iUnion] at hv ⊢
    obtain ⟨d, T, hT⟩ := hv
    refine ⟨fun i => d (σ i), ?_⟩
    rw [Set.mem_range]
    exact ⟨KTensor.legReindex σ T, hT⟩
  · -- Conversely realize `Fspec T'` (format `d'`) as `(reindex σ) (legReindex σ⁻¹ T')`.
    intro v hv
    rw [Set.mem_iUnion] at hv ⊢
    obtain ⟨d', T', hT'⟩ := hv
    refine ⟨fun i => d' (σ.symm i), ?_⟩
    rw [Set.mem_range]
    refine ⟨KTensor.legReindex σ.symm T', ?_⟩
    rw [SpectralPoint.reindex_toFun]
    -- `Fspec (legReindex σ (legReindex σ⁻¹ T')) = Fspec T' = v`.
    rw [← hT']
    -- Need: Fspec.toFun (legReindex σ (legReindex σ.symm T')) = Fspec.toFun T'.
    have hR1 := KTensor.legReindex_legReindex_restricts σ.symm T'
    have hR2 := KTensor.restricts_legReindex_legReindex σ.symm T'
    rw [Equiv.symm_symm] at hR1 hR2
    exact le_antisymm (Fspec.mono _ _ hR1) (Fspec.mono _ _ hR2)

/-- `naturalPairFormat r i j ∘ σ = naturalPairFormat r (σ.symm i) (σ.symm j)`. -/
lemma naturalPairFormat_comp_perm {k : ℕ} (σ : Equiv.Perm (Fin k)) (r : ℕ+)
    (i j : Fin k) :
    (fun ℓ => naturalPairFormat r i j (σ ℓ))
      = naturalPairFormat r (σ.symm i) (σ.symm j) := by
  funext ℓ
  simp only [naturalPairFormat]
  refine if_congr (or_congr ?_ ?_) rfl rfl <;> exact (Equiv.eq_symm_apply σ).symm

/-- **Pair-unit transport** under `legReindex`: reindexing `⟨r⟩_{i,j}` by `σ`
    gives `⟨r⟩_{σ⁻¹ i, σ⁻¹ j}` (up to the format-cast `naturalPairFormat ∘ σ =
    naturalPairFormat (σ⁻¹ ·)`). We record this as restriction-equivalence. -/
lemma KTensor.legReindex_unitPairTensor_restrictsEquiv {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (r : ℕ+) (i j : Fin k) (hij : i ≠ j)
    (hij' : σ.symm i ≠ σ.symm j) :
    (KTensor.legReindex σ (unitPairTensor (F := F) r i j hij)) ∼ₜ
      unitPairTensor (F := F) r (σ.symm i) (σ.symm j) hij' := by
  classical
  have hfmt : ∀ ℓ : Fin k,
      (naturalPairFormat r i j (σ ℓ) : ℕ) = (naturalPairFormat r (σ.symm i) (σ.symm j) ℓ : ℕ) := by
    intro ℓ
    rw [show naturalPairFormat r i j (σ ℓ)
        = (fun ℓ => naturalPairFormat r i j (σ ℓ)) ℓ from rfl,
      naturalPairFormat_comp_perm]
  constructor
  · refine Restricts.of_eq_cast hfmt (fun jdx => ?_)
    simp only [KTensor.legReindex, unitPairTensor]
    congr 1
    rw [piCongrLeft_val, piCongrLeft_val]
    simp only [Fin.val_cast]
  · refine Restricts.of_eq_cast (fun ℓ => (hfmt ℓ).symm) (fun jdx => ?_)
    simp only [KTensor.legReindex, unitPairTensor]
    congr 1
    rw [piCongrLeft_val, piCongrLeft_val]
    simp only [Fin.val_cast]

/-- Value-level corollary: `Fspec.reindex σ` sends `⟨r⟩_{i,j}` to the same value
    that `Fspec` assigns to `⟨r⟩_{σ⁻¹ i, σ⁻¹ j}`. -/
lemma SpectralPoint.reindex_toFun_unitPairTensor {k : ℕ} (Fspec : SpectralPoint k F)
    (σ : Equiv.Perm (Fin k)) (r : ℕ+) (i j : Fin k) (hij : i ≠ j)
    (hij' : σ.symm i ≠ σ.symm j) :
    (Fspec.reindex σ).toFun (unitPairTensor (F := F) r i j hij)
      = Fspec.toFun (unitPairTensor (F := F) r (σ.symm i) (σ.symm j) hij') := by
  rw [SpectralPoint.reindex_toFun]
  obtain ⟨hLR, hRL⟩ :=
    KTensor.legReindex_unitPairTensor_restrictsEquiv (F := F) σ r i j hij hij'
  exact le_antisymm (Fspec.mono _ _ hLR) (Fspec.mono _ _ hRL)

/-- There is a permutation sending a chosen pair `(i, j)` (distinct) to any other
    chosen pair `(a, b)` (distinct). -/
lemma exists_perm_mapping_pair {k : ℕ} (i j : Fin k) (hij : i ≠ j)
    (a b : Fin k) (hab : a ≠ b) :
    ∃ σ : Equiv.Perm (Fin k), σ i = a ∧ σ j = b := by
  classical
  -- τ₁ = swap i a sends i ↦ a. Let j₁ = τ₁ j; since j ≠ i, j₁ ≠ a.
  -- τ₂ = swap j₁ b sends j₁ ↦ b and fixes a (as a ≠ j₁, a ≠ b). σ = τ₂ * τ₁.
  set j₁ := Equiv.swap i a j with hj₁
  have hj₁a : j₁ ≠ a := by
    rw [hj₁]
    intro h
    have : Equiv.swap i a j = Equiv.swap i a i := by rw [h, Equiv.swap_apply_left]
    exact hij ((Equiv.swap i a).injective this).symm
  refine ⟨Equiv.swap j₁ b * Equiv.swap i a, ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hj₁a) hab]
  · simp only [Equiv.Perm.mul_apply, ← hj₁, Equiv.swap_apply_left]

/-- Monotonicity of pair-units used in Lemma 3.6 (paper tex:1016-1021).

For `r ≤ s`, the smaller pair-unit embeds into the larger one by the coordinate
inclusion on legs `i` and `j` and the unique maps on all other legs. -/
lemma unitPairTensor_restricts_of_le {k : ℕ} (i j : Fin k) (hij : i ≠ j)
    {r s : ℕ+} (hrs : (r : ℕ) ≤ (s : ℕ)) :
    Restricts (unitPairTensor (F := F) r i j hij)
      (unitPairTensor (F := F) s i j hij) := by
  classical
  have hdim_le : ∀ ℓ : Fin k,
      (naturalPairFormat r i j ℓ : ℕ) ≤ (naturalPairFormat s i j ℓ : ℕ) := by
    intro ℓ
    unfold naturalPairFormat
    by_cases hℓ : ℓ = i ∨ ℓ = j
    · simp [hℓ, hrs]
    · simp [hℓ]
  let legMatrix : ∀ ℓ : Fin k,
      Matrix (Fin (naturalPairFormat r i j ℓ)) (Fin (naturalPairFormat s i j ℓ)) F :=
    fun ℓ a b => if ℓ = i ∨ ℓ = j then if a.val = b.val then 1 else 0 else 1
  refine ⟨legMatrix, ?_⟩
  intro jdx
  let idx0 : ∀ ℓ : Fin k, Fin (naturalPairFormat s i j ℓ) :=
    fun ℓ => ⟨(jdx ℓ).val, lt_of_lt_of_le (jdx ℓ).isLt (hdim_le ℓ)⟩
  rw [Finset.sum_eq_single idx0]
  · unfold unitPairTensor
    have hprod : (∏ ℓ : Fin k,
        legMatrix ℓ (jdx ℓ) (idx0 ℓ)) = 1 := by
      apply Finset.prod_eq_one
      intro ℓ _
      by_cases hℓ : ℓ = i ∨ ℓ = j <;> simp [legMatrix, hℓ, idx0]
    have hij_val :
        (idx0 i).val = (idx0 j).val ↔ (jdx i).val = (jdx j).val := by
      simp [idx0]
    rw [hprod]
    by_cases h : (jdx i).val = (jdx j).val
    · simp [h, hij_val]
    · simp [h, hij_val]
  · intro idx _ hidx
    have hne : ∃ ℓ : Fin k, (jdx ℓ).val ≠ (idx ℓ).val := by
      by_contra h
      push_neg at h
      apply hidx
      funext ℓ
      apply Fin.ext
      exact (h ℓ).symm
    obtain ⟨ℓ, hℓ⟩ := hne
    have hℓ_pair : ℓ = i ∨ ℓ = j := by
      by_contra hnot
      have hdim_s : naturalPairFormat s i j ℓ = 1 := by
        unfold naturalPairFormat
        simp [hnot]
      have hidx_val : (idx ℓ).val = 0 := by
        have hlt : (idx ℓ).val < 1 := by
          simpa [hdim_s] using (idx ℓ).isLt
        omega
      have hjdx_val : (jdx ℓ).val = 0 := by
        have hdim_r : naturalPairFormat r i j ℓ = 1 := by
          unfold naturalPairFormat
          simp [hnot]
        have hlt : (jdx ℓ).val < 1 := by
          simpa [hdim_r] using (jdx ℓ).isLt
        omega
      exact hℓ (by rw [hjdx_val, hidx_val])
    have hzero :
        legMatrix ℓ (jdx ℓ) (idx ℓ) = 0 := by
      simp [legMatrix, hℓ_pair, hℓ]
    have hprod_zero :
        (∏ m : Fin k,
          legMatrix m (jdx m) (idx m)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ ℓ) hzero
    rw [hprod_zero, zero_mul]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

/-- **Lemma 3.6** (tex:1016-1021, `\label{lem:free-units}`).

If `F ∈ Δ(F, k)` and `F(⟨2⟩_{i,j}) = 1` for some `i ≠ j ∈ [k]`,
then `F(⟨m⟩_{i,j}) = 1` for every `m ≥ 1`.

Stated using the natural-format `unitPairTensor` (legs `i, j` of dim `r`,
others of dim `1`). -/
theorem free_units {k : ℕ} (Fspec : SpectralPoint k F)
    (i j : Fin k) (hij : i ≠ j)
    (h2 : Fspec.toFun (unitPairTensor (F := F) 2 i j hij) = 1)
    (m : ℕ+) :
    Fspec.toFun (unitPairTensor (F := F) m i j hij) = 1 := by
  classical
  let powTwo : ℕ → ℕ+ := fun a => ⟨2 ^ a, pow_pos (by norm_num : (0 : ℕ) < 2) a⟩
  have hpow : ∀ a : ℕ,
      Fspec.toFun (unitPairTensor (F := F) (powTwo a) i j hij) = 1 := by
    intro a
    induction a with
    | zero =>
        change Fspec.toFun (unitPairTensor (F := F) 1 i j hij) = 1
        exact Fspec.unitPair_one i j hij
    | succ a ih =>
        have hmul := Fspec.unitPair_mul i j hij (powTwo a) (2 : ℕ+)
        have hfmt : powTwo (a + 1) = powTwo a * (2 : ℕ+) := by
          apply PNat.coe_injective
          simp [powTwo, pow_succ, Nat.mul_comm]
        rw [hfmt, hmul, ih, h2, one_mul]
  have h_one_le_m : ((1 : ℕ+) : ℕ) ≤ (m : ℕ) := by
    exact m.2
  have h_m_le_pow : (m : ℕ) ≤ (powTwo (m : ℕ) : ℕ) := by
    exact le_of_lt (Nat.lt_pow_self (n := (m : ℕ)) (a := 2) (by norm_num : 1 < 2))
  have hle_low :
      (1 : ℝ) ≤ Fspec.toFun (unitPairTensor (F := F) m i j hij) := by
    have hmono := Fspec.mono (unitPairTensor (F := F) 1 i j hij)
      (unitPairTensor (F := F) m i j hij)
      (unitPairTensor_restricts_of_le (F := F) i j hij h_one_le_m)
    simpa [Fspec.unitPair_one i j hij] using hmono
  have hle_high :
      Fspec.toFun (unitPairTensor (F := F) m i j hij) ≤ 1 := by
    have hmono := Fspec.mono (unitPairTensor (F := F) m i j hij)
      (unitPairTensor (F := F) (powTwo (m : ℕ)) i j hij)
      (unitPairTensor_restricts_of_le (F := F) i j hij h_m_le_pow)
    simpa [hpow (m : ℕ)] using hmono
  exact le_antisymm hle_high hle_low

/-! ## Lemma 3.7 (tex:1029-1034). -/

/-- `φ` preserves restriction (paper tex:1029-1034).

If `S ≤ T` as `(k-1)`-tensors, then padding both tensors by the one-dimensional
last leg preserves the restriction. Concretely, the leg-wise matrices witnessing
`S ≤ T` are reused on the first `k-1` legs and the identity matrix is used on the
new last leg. -/
lemma phiMap_restricts {k : ℕ} (hk : 3 ≤ k) {eS eT : Fin (k - 1) → ℕ+}
    {S : KTensor F eS} {T : KTensor F eT}
    (hST : Restricts S T) :
    Restricts (phiMap (F := F) hk S) (phiMap (F := F) hk T) := by
  classical
  obtain ⟨A, hA⟩ := hST
  let legMatrix : ∀ ℓ : Fin k,
      Matrix (Fin (dPhi hk eS ℓ)) (Fin (dPhi hk eT ℓ)) F :=
    fun ℓ a b =>
      if hℓ : (ℓ : ℕ) < k - 1 then
        A ⟨ℓ, hℓ⟩
          (Fin.cast (by
            unfold dPhi
            simp only [dif_pos hℓ]) a)
          (Fin.cast (by
            unfold dPhi
            simp only [dif_pos hℓ]) b)
      else
        if a.val = b.val then 1 else 0
  refine ⟨legMatrix, ?_⟩
  intro jdx
  let pruneS : (∀ ℓ : Fin k, Fin (dPhi hk eS ℓ)) → (∀ i : Fin (k - 1), Fin (eS i)) :=
    fun idx i =>
      Fin.cast (by
        unfold dPhi
        simp only [dif_pos i.isLt]) (idx ⟨i, by omega⟩)
  let pruneT : (∀ ℓ : Fin k, Fin (dPhi hk eT ℓ)) → (∀ i : Fin (k - 1), Fin (eT i)) :=
    fun idx i =>
      Fin.cast (by
        unfold dPhi
        simp only [dif_pos i.isLt]) (idx ⟨i, by omega⟩)
  let liftT : (∀ i : Fin (k - 1), Fin (eT i)) → (∀ ℓ : Fin k, Fin (dPhi hk eT ℓ)) :=
    fun idx ℓ =>
      if hℓ : (ℓ : ℕ) < k - 1 then
        Fin.cast (by
          unfold dPhi
          simp only [dif_pos hℓ]) (idx ⟨ℓ, hℓ⟩)
      else
        Fin.cast (by
          unfold dPhi
          simp only [dif_neg hℓ, PNat.val_ofNat]) (0 : Fin 1)
  let idxEquiv : (∀ ℓ : Fin k, Fin (dPhi hk eT ℓ)) ≃
      (∀ i : Fin (k - 1), Fin (eT i)) :=
    { toFun := fun idx => pruneT idx
      invFun := fun idx => liftT idx
      left_inv := by
        intro idx
        funext ℓ
        by_cases hℓ : (ℓ : ℕ) < k - 1
        · simp [pruneT, liftT, hℓ]
        · have hdim : dPhi hk eT ℓ = 1 := by
            unfold dPhi
            simp only [dif_neg hℓ]
          apply Fin.ext
          have hidx : (idx ℓ).val = 0 := by
            have hlt : (idx ℓ).val < 1 := by
              simpa [hdim] using (idx ℓ).isLt
            omega
          have hlift : ((liftT (pruneT idx)) ℓ).val = 0 := by
            have hlt : ((liftT (pruneT idx)) ℓ).val < 1 := by
              simp [liftT, hℓ, hdim]
            omega
          rw [hidx, hlift]
      right_inv := by
        intro idx
        funext i
        simp [pruneT, liftT, i.isLt] }
  have hphiS : phiMap (F := F) hk S jdx = S (pruneS jdx) := by
    unfold phiMap pruneS
    rfl
  calc
    phiMap (F := F) hk S jdx = S (pruneS jdx) := hphiS
    _ = ∑ idx : (∀ i : Fin (k - 1), Fin (eT i)),
          (∏ i : Fin (k - 1), A i (pruneS jdx i) (idx i)) * T idx := hA (pruneS jdx)
    _ = ∑ idx : (∀ ℓ : Fin k, Fin (dPhi hk eT ℓ)),
          (∏ ℓ : Fin k, legMatrix ℓ (jdx ℓ) (idx ℓ)) * phiMap (F := F) hk T idx := by
      exact Fintype.sum_equiv idxEquiv.symm
        (fun idx : (∀ i : Fin (k - 1), Fin (eT i)) =>
          (∏ i : Fin (k - 1), A i (pruneS jdx i) (idx i)) * T idx)
        (fun idx : (∀ ℓ : Fin k, Fin (dPhi hk eT ℓ)) =>
          (∏ ℓ : Fin k, legMatrix ℓ (jdx ℓ) (idx ℓ)) * phiMap (F := F) hk T idx)
        (fun idx => by
      have hprod :
          (∏ ℓ : Fin k, legMatrix ℓ (jdx ℓ) ((idxEquiv.symm idx) ℓ)) =
            ∏ i : Fin (k - 1), A i (pruneS jdx i) (idx i) := by
        let firstLegs : Finset (Fin k) := Finset.univ.filter fun ℓ : Fin k => (ℓ : ℕ) < k - 1
        have hfirst_to_univ :
            (∏ ℓ ∈ firstLegs, legMatrix ℓ (jdx ℓ) ((idxEquiv.symm idx) ℓ)) =
              ∏ ℓ : Fin k, legMatrix ℓ (jdx ℓ) ((idxEquiv.symm idx) ℓ) := by
          simpa using (Finset.prod_subset
            (s₁ := firstLegs) (s₂ := (Finset.univ : Finset (Fin k)))
            (f := fun ℓ : Fin k => legMatrix ℓ (jdx ℓ) ((idxEquiv.symm idx) ℓ))
            (by intro ℓ hℓ; exact Finset.mem_univ ℓ)
            (by
              intro ℓ _ hℓ_not
              have hnot : ¬ (ℓ : ℕ) < k - 1 := by
                simpa [firstLegs] using hℓ_not
              have hjdx_val : (jdx ℓ).val = 0 := by
                have hdim : dPhi hk eS ℓ = 1 := by
                  unfold dPhi
                  simp only [dif_neg hnot]
                have hlt : (jdx ℓ).val < 1 := by
                  simpa [hdim] using (jdx ℓ).isLt
                omega
              have hidx_val : ((idxEquiv.symm idx) ℓ).val = 0 := by
                have hdim : dPhi hk eT ℓ = 1 := by
                  unfold dPhi
                  simp only [dif_neg hnot]
                have hlt : ((idxEquiv.symm idx) ℓ).val < 1 := by
                  simpa [hdim] using ((idxEquiv.symm idx) ℓ).isLt
                omega
              simp [legMatrix, hnot, hjdx_val, hidx_val]))
        rw [← hfirst_to_univ]
        change (∏ ℓ ∈ firstLegs, legMatrix ℓ (jdx ℓ) ((idxEquiv.symm idx) ℓ)) =
          ∏ i ∈ (Finset.univ : Finset (Fin (k - 1))), A i (pruneS jdx i) (idx i)
        apply Finset.prod_bij
          (fun ℓ hℓ => ⟨ℓ, by
            simpa [firstLegs] using hℓ⟩)
        · intro ℓ hℓ
          exact Finset.mem_univ _
        · intro ℓ hℓ m _ h
          apply Fin.ext
          exact congrArg (fun x : Fin (k - 1) => x.val) h
        · intro m _
          refine ⟨⟨m.1, by omega⟩, ?_, ?_⟩
          · simp [firstLegs, m.2]
          · apply Fin.ext
            rfl
        · intro ℓ hℓ
          have hlt : (ℓ : ℕ) < k - 1 := by
            simpa [firstLegs] using hℓ
          simp [legMatrix, pruneS, idxEquiv, pruneT, liftT, hlt]
      have hphiT : phiMap (F := F) hk T (idxEquiv.symm idx) = T idx := by
        have hprune : pruneT (idxEquiv.symm idx) = idx := idxEquiv.right_inv idx
        unfold phiMap
        change T (pruneT (idxEquiv.symm idx)) = T idx
        rw [hprune]
      change ((∏ i : Fin (k - 1), A i (pruneS jdx i) (idx i)) * T idx) =
        ((∏ ℓ : Fin k, legMatrix ℓ (jdx ℓ) ((idxEquiv.symm idx) ℓ)) *
          phiMap (F := F) hk T (idxEquiv.symm idx))
      rw [← hprod, hphiT])

/-- Explicit witness for the first structural comparison in Lemma 3.7
(paper tex:1033).

The paper's large-`m` construction can be witnessed by the last input dimension:
the extra pair-unit coordinate on legs `k-2,k-1` stores the split-off
`k-1`-coordinate while `φ(γ(T))` stores the merged `(k-2,k-1)` coordinate. -/
private lemma paper_tex_1039_tensor_le_phi_gamma_kronecker_unit_witness {k : ℕ}
    (hk : 3 ≤ k)
    (hij : (⟨k - 2, by omega⟩ : Fin k) ≠ ⟨k - 1, by omega⟩)
    {dT : Fin k → ℕ+} (T : KTensor F dT) :
    Restricts T
      (phiMap (F := F) hk (gammaMap (F := F) hk T) ⊠
        unitPairTensor (F := F) (dT ⟨k - 1, by omega⟩)
          ⟨k - 2, by omega⟩ ⟨k - 1, by omega⟩ hij) := by
  classical
  set i : Fin k := ⟨k - 2, by omega⟩ with hi
  set j : Fin k := ⟨k - 1, by omega⟩ with hj
  set m : ℕ+ := dT j with hm
  -- Format of the Kronecker target.
  set P : Fin k → ℕ+ := dPhi hk (dGamma hk dT) with hP
  set npf : Fin k → ℕ+ := naturalPairFormat m i j with hnpf
  -- Dimension facts.
  have hk2_lt : (k - 2 : ℕ) < k := by omega
  have hk1_lt : (k - 1 : ℕ) < k := by omega
  have hk2_ne_k1 : (k - 2 : ℕ) ≠ k - 1 := by omega
  -- `npf` values.
  have hnpf_i : (npf i : ℕ) = (m : ℕ) := by
    simp [hnpf, naturalPairFormat, hi]
  have hnpf_j : (npf j : ℕ) = (m : ℕ) := by
    simp [hnpf, naturalPairFormat, hj]
  have hi_val : (i : ℕ) = k - 2 := by rw [hi]
  have hj_val : (j : ℕ) = k - 1 := by rw [hj]
  have hnpf_lt : ∀ ℓ : Fin k, (ℓ : ℕ) < k - 2 → (npf ℓ : ℕ) = 1 := by
    intro ℓ hℓ
    have hℓi : ℓ ≠ i := by
      intro h; rw [h, hi_val] at hℓ; omega
    have hℓj : ℓ ≠ j := by
      intro h; rw [h, hj_val] at hℓ; omega
    simp [hnpf, naturalPairFormat, hℓi, hℓj]
  -- `P` values.
  have hP_lt : ∀ ℓ : Fin k, (ℓ : ℕ) < k - 2 → (P ℓ : ℕ) = (dT ℓ : ℕ) := by
    intro ℓ hℓ
    have h1 : (ℓ : ℕ) < k - 1 := by omega
    simp [hP, dPhi, dGamma, h1, hℓ]
  have hP_i : (P i : ℕ) = (dT i : ℕ) * (dT j : ℕ) := by
    have h1 : ((⟨k - 2, hk2_lt⟩ : Fin k) : ℕ) < k - 1 := by simp; omega
    have h2 : ¬ ((⟨(⟨k - 2, hk2_lt⟩ : Fin k), by omega⟩ : Fin (k - 1)) : ℕ) < k - 2 := by
      simp
    have hival : (P i : ℕ) = (dGamma hk dT ⟨k - 2, by omega⟩ : ℕ) := by
      simp only [hP, dPhi, hi]
      rw [dif_pos h1]
    rw [hival]
    simp only [dGamma, dif_neg h2, PNat.mul_coe, hi, hj]
  have hP_j : (P j : ℕ) = 1 := by
    have h1 : ¬ (j : ℕ) < k - 1 := by rw [hj_val]; omega
    simp [hP, dPhi, h1]
  -- Kron format value.
  have hQ : ∀ ℓ : Fin k, ((P ℓ * npf ℓ : ℕ+) : ℕ) = (P ℓ : ℕ) * (npf ℓ : ℕ) := by
    intro ℓ; rw [PNat.mul_coe]
  -- `kronLeftIndex`/`kronRightIndex` value formulas (divisor = right dim = `npf`).
  have hkL : ∀ (idx : ∀ ℓ : Fin k, Fin ((P ℓ * npf ℓ : ℕ+) : ℕ)) (ℓ : Fin k),
      (kronLeftIndex (dS := P) (dT := npf) idx ℓ).val = (idx ℓ).val / (npf ℓ : ℕ) := by
    intro idx ℓ
    simp [kronLeftIndex, finProdFinEquiv_symm_apply, Fin.divNat]
  have hkR : ∀ (idx : ∀ ℓ : Fin k, Fin ((P ℓ * npf ℓ : ℕ+) : ℕ)) (ℓ : Fin k),
      (kronRightIndex (dS := P) (dT := npf) idx ℓ).val = (idx ℓ).val % (npf ℓ : ℕ) := by
    intro idx ℓ
    simp [kronRightIndex, finProdFinEquiv_symm_apply, Fin.modNat]
  -- Evaluate `φ(γ(T))` at a left-index `L`: it equals `T` at the reconstructed
  -- index, where legs `< k-2` pass through, leg `k-2` is `L(k-2).val / d_{k-1}`,
  -- leg `k-1` is `L(k-2).val % d_{k-1}`.
  have hphigamma : ∀ (L : ∀ ℓ : Fin k, Fin (P ℓ)) (gg : ∀ ℓ : Fin k, Fin (dT ℓ)),
      (∀ ℓ : Fin k, (ℓ : ℕ) < k - 2 → (gg ℓ).val = (L ℓ).val) →
      ((gg i).val = (L i).val / (dT j : ℕ)) →
      ((gg j).val = (L i).val % (dT j : ℕ)) →
      phiMap (F := F) hk (gammaMap (F := F) hk T) L = T gg := by
    intro L gg hpass hk2 hk1
    unfold phiMap gammaMap
    apply congrArg T
    funext ℓ
    apply Fin.ext
    by_cases hℓ : (ℓ : ℕ) < k - 2
    · simp only [dif_pos hℓ]
      rw [hpass ℓ hℓ]
      simp only [Fin.val_cast]
    · by_cases hℓ2 : (ℓ : ℕ) = k - 2
      · have hℓi : ℓ = i := Fin.ext (by rw [hi_val]; exact hℓ2)
        rw [hℓi, hk2]
        simp only [dif_neg (show ¬ (i : ℕ) < k - 2 by rw [hi_val]; omega),
          dif_pos (show (i : ℕ) = k - 2 by rw [hi_val]),
          finProdFinEquiv_symm_apply, Fin.coe_divNat, Fin.val_cast]
        rw [hi, hj]
      · have hℓj : (ℓ : ℕ) = k - 1 := by have := ℓ.isLt; omega
        have hℓjeq : ℓ = j := Fin.ext (by rw [hj_val]; exact hℓj)
        rw [hℓjeq, hk1]
        simp only [dif_neg (show ¬ (j : ℕ) < k - 2 by rw [hj_val]; omega),
          dif_neg (show ¬ (j : ℕ) = k - 2 by rw [hj_val]; omega),
          finProdFinEquiv_symm_apply, Fin.coe_modNat, Fin.val_cast]
        rw [hi, hj]
  -- The witness leg-wise matrices.
  refine ⟨fun ℓ a b =>
      if (ℓ : ℕ) < k - 2 then (if b.val = a.val then 1 else 0)
      else if (ℓ : ℕ) = k - 2 then
        (if (b.val / (dT j : ℕ)) / (dT j : ℕ) = a.val ∧
            (b.val / (dT j : ℕ)) % (dT j : ℕ) = b.val % (dT j : ℕ) then 1 else 0)
      else (if b.val % (dT j : ℕ) = a.val then 1 else 0), ?_⟩
  intro jdx
  -- The left/right coordinates of the reconstructing index.
  have hjdx_i_lt : (jdx i).val < (dT i : ℕ) := (jdx i).isLt
  have hjdx_j_lt : (jdx j).val < (dT j : ℕ) := (jdx j).isLt
  -- left value on leg `i`: the merged coordinate.
  set Lval : Fin k → ℕ := fun ℓ =>
    if (ℓ : ℕ) < k - 2 then (jdx ℓ).val
    else if (ℓ : ℕ) = k - 2 then (jdx j).val + (dT j : ℕ) * (jdx i).val
    else 0 with hLval
  set Rval : Fin k → ℕ := fun ℓ =>
    if (ℓ : ℕ) < k - 2 then 0
    else (jdx j).val with hRval
  -- Value formulas for `Lval`, `Rval`.
  have hLval_eq_lt : ∀ ℓ : Fin k, (ℓ : ℕ) < k - 2 → Lval ℓ = (jdx ℓ).val := by
    intro ℓ hℓ; simp only [hLval]; rw [if_pos hℓ]
  have hLval_eq_i : Lval i = (jdx j).val + (dT j : ℕ) * (jdx i).val := by
    simp only [hLval]
    rw [if_neg (show ¬ (i : ℕ) < k - 2 by rw [hi_val]; omega),
      if_pos (show (i : ℕ) = k - 2 by rw [hi_val])]
  have hLval_eq_j : Lval j = 0 := by
    simp only [hLval]
    rw [if_neg (show ¬ (j : ℕ) < k - 2 by rw [hj_val]; omega),
      if_neg (show ¬ (j : ℕ) = k - 2 by rw [hj_val]; omega)]
  have hRval_eq_lt : ∀ ℓ : Fin k, (ℓ : ℕ) < k - 2 → Rval ℓ = 0 := by
    intro ℓ hℓ; simp only [hRval]; rw [if_pos hℓ]
  have hRval_eq_ge : ∀ ℓ : Fin k, ¬ (ℓ : ℕ) < k - 2 → Rval ℓ = (jdx j).val := by
    intro ℓ hℓ; simp only [hRval]; rw [if_neg hℓ]
  have hLval_lt : ∀ ℓ : Fin k, Lval ℓ < (P ℓ : ℕ) := by
    intro ℓ
    by_cases hℓ : (ℓ : ℕ) < k - 2
    · rw [hLval_eq_lt ℓ hℓ, hP_lt ℓ hℓ]; exact (jdx ℓ).isLt
    · by_cases hℓ2 : (ℓ : ℕ) = k - 2
      · have hℓi : ℓ = i := Fin.ext (by rw [hi_val]; exact hℓ2)
        rw [hℓi, hLval_eq_i, hP_i]
        calc (jdx j).val + (dT j : ℕ) * (jdx i).val
            < (dT j : ℕ) + (dT j : ℕ) * (jdx i).val := by omega
          _ = (dT j : ℕ) * ((jdx i).val + 1) := by ring
          _ ≤ (dT i : ℕ) * (dT j : ℕ) := by
              rw [Nat.mul_comm (dT i : ℕ)]
              exact Nat.mul_le_mul_left _ (by omega)
      · have hℓj : (ℓ : ℕ) = k - 1 := by have := ℓ.isLt; omega
        have hℓjeq : ℓ = j := Fin.ext (by rw [hj_val]; exact hℓj)
        rw [hℓjeq, hLval_eq_j, hP_j]; omega
  have hRval_lt : ∀ ℓ : Fin k, Rval ℓ < (npf ℓ : ℕ) := by
    intro ℓ
    by_cases hℓ : (ℓ : ℕ) < k - 2
    · rw [hRval_eq_lt ℓ hℓ, hnpf_lt ℓ hℓ]; omega
    · rw [hRval_eq_ge ℓ hℓ]
      by_cases hℓ2 : (ℓ : ℕ) = k - 2
      · have hℓi : ℓ = i := Fin.ext (by rw [hi_val]; exact hℓ2)
        rw [hℓi, hnpf_i, hm]; exact hjdx_j_lt
      · have hℓj : (ℓ : ℕ) = k - 1 := by have := ℓ.isLt; omega
        have hℓjeq : ℓ = j := Fin.ext (by rw [hj_val]; exact hℓj)
        rw [hℓjeq, hnpf_j, hm]; exact hjdx_j_lt
  -- The reconstructing kron-index.
  let idx0 : ∀ ℓ : Fin k, Fin ((P ℓ * npf ℓ : ℕ+) : ℕ) := fun ℓ =>
    ⟨Rval ℓ + (npf ℓ : ℕ) * Lval ℓ, by
      rw [hQ ℓ]
      calc Rval ℓ + (npf ℓ : ℕ) * Lval ℓ
          < (npf ℓ : ℕ) + (npf ℓ : ℕ) * Lval ℓ := by
            have := hRval_lt ℓ; omega
        _ = (npf ℓ : ℕ) * (Lval ℓ + 1) := by ring
        _ ≤ (npf ℓ : ℕ) * (P ℓ : ℕ) := Nat.mul_le_mul_left _ (by have := hLval_lt ℓ; omega)
        _ = (P ℓ : ℕ) * (npf ℓ : ℕ) := by ring⟩
  have hidx0_val : ∀ ℓ : Fin k, (idx0 ℓ).val = Rval ℓ + (npf ℓ : ℕ) * Lval ℓ := fun ℓ => rfl
  have hidx0_L : ∀ ℓ : Fin k, (idx0 ℓ).val / (npf ℓ : ℕ) = Lval ℓ := by
    intro ℓ
    rw [hidx0_val, Nat.add_mul_div_left _ _ (npf ℓ).pos, Nat.div_eq_of_lt (hRval_lt ℓ), zero_add]
  have hidx0_R : ∀ ℓ : Fin k, (idx0 ℓ).val % (npf ℓ : ℕ) = Rval ℓ := by
    intro ℓ
    rw [hidx0_val, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hRval_lt ℓ)]
  rw [Finset.sum_eq_single idx0]
  · -- Product = 1 at idx0; value = T jdx.
    have hprod : (∏ ℓ : Fin k,
        (if (ℓ : ℕ) < k - 2 then (if (idx0 ℓ).val = (jdx ℓ).val then (1 : F) else 0)
          else if (ℓ : ℕ) = k - 2 then
            (if ((idx0 ℓ).val / (dT j : ℕ)) / (dT j : ℕ) = (jdx ℓ).val ∧
                ((idx0 ℓ).val / (dT j : ℕ)) % (dT j : ℕ) = (idx0 ℓ).val % (dT j : ℕ)
              then 1 else 0)
          else (if (idx0 ℓ).val % (dT j : ℕ) = (jdx ℓ).val then 1 else 0))) = 1 := by
      apply Finset.prod_eq_one
      intro ℓ _
      by_cases hℓ : (ℓ : ℕ) < k - 2
      · rw [if_pos hℓ, if_pos]
        rw [hidx0_val, hRval_eq_lt ℓ hℓ, hnpf_lt ℓ hℓ, hLval_eq_lt ℓ hℓ, one_mul,
          zero_add]
      · by_cases hℓ2 : (ℓ : ℕ) = k - 2
        · have hℓi : ℓ = i := Fin.ext (by rw [hi_val]; exact hℓ2)
          rw [if_neg hℓ, if_pos hℓ2, if_pos]
          have hnpfi' : (npf ℓ : ℕ) = (dT j : ℕ) := by rw [hℓi, hnpf_i, hm]
          have hL : (idx0 ℓ).val / (dT j : ℕ) = Lval ℓ := by
            rw [← hnpfi']; exact hidx0_L ℓ
          have hR : (idx0 ℓ).val % (dT j : ℕ) = Rval ℓ := by
            rw [← hnpfi']; exact hidx0_R ℓ
          have hLval_i : Lval ℓ = (jdx j).val + (dT j : ℕ) * (jdx i).val := by
            rw [hℓi]; exact hLval_eq_i
          have hRval_i : Rval ℓ = (jdx j).val := hRval_eq_ge ℓ hℓ
          refine ⟨?_, ?_⟩
          · rw [hL, hLval_i, Nat.add_mul_div_left _ _ (dT j).pos,
              Nat.div_eq_of_lt hjdx_j_lt, zero_add, hℓi]
          · rw [hL, hR, hLval_i, hRval_i, Nat.add_mul_mod_self_left,
              Nat.mod_eq_of_lt hjdx_j_lt]
        · have hℓj : (ℓ : ℕ) = k - 1 := by have := ℓ.isLt; omega
          have hℓjeq : ℓ = j := Fin.ext (by rw [hj_val]; exact hℓj)
          rw [if_neg hℓ, if_neg hℓ2, if_pos]
          have hnpfj' : (npf ℓ : ℕ) = (dT j : ℕ) := by rw [hℓjeq, hnpf_j, hm]
          have hR : (idx0 ℓ).val % (dT j : ℕ) = Rval ℓ := by
            rw [← hnpfj']; exact hidx0_R ℓ
          rw [hR, hRval_eq_ge ℓ hℓ, hℓjeq]
    -- Replace the product (matrix entries at idx0) by `hprod`.
    have hcoef : (∏ ℓ : Fin k,
        (fun ℓ a b =>
          if (ℓ : ℕ) < k - 2 then (if b.val = a.val then (1 : F) else 0)
          else if (ℓ : ℕ) = k - 2 then
            (if (b.val / (dT j : ℕ)) / (dT j : ℕ) = a.val ∧
                (b.val / (dT j : ℕ)) % (dT j : ℕ) = b.val % (dT j : ℕ) then 1 else 0)
          else (if b.val % (dT j : ℕ) = a.val then 1 else 0)) ℓ (jdx ℓ) (idx0 ℓ)) = 1 := hprod
    rw [hcoef, one_mul]
    -- Now compute the Kronecker tensor at idx0.
    symm
    change phiMap (F := F) hk (gammaMap (F := F) hk T) (kronLeftIndex idx0) *
        unitPairTensor (F := F) m i j hij (kronRightIndex idx0) = T jdx
    have hkLeq : ∀ ℓ : Fin k, (kronLeftIndex idx0 ℓ).val = Lval ℓ := by
      intro ℓ; rw [hkL idx0 ℓ]; exact hidx0_L ℓ
    have hkReq : ∀ ℓ : Fin k, (kronRightIndex idx0 ℓ).val = Rval ℓ := by
      intro ℓ; rw [hkR idx0 ℓ]; exact hidx0_R ℓ
    -- `φ(γ(T))` part.
    have hphi : phiMap (F := F) hk (gammaMap (F := F) hk T) (kronLeftIndex idx0) = T jdx := by
      apply hphigamma
      · intro ℓ hℓ; rw [hkLeq ℓ, hLval_eq_lt ℓ hℓ]
      · rw [hkLeq i, hLval_eq_i,
          Nat.add_mul_div_left _ _ (dT j).pos, Nat.div_eq_of_lt hjdx_j_lt, zero_add]
      · rw [hkLeq i, hLval_eq_i, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hjdx_j_lt]
    -- unit pair part = 1.
    have hunit : unitPairTensor (F := F) m i j hij (kronRightIndex idx0) = 1 := by
      unfold unitPairTensor
      rw [if_pos]
      rw [hkReq i, hkReq j, hRval_eq_ge i (by rw [hi_val]; omega),
        hRval_eq_ge j (by rw [hj_val]; omega)]
    rw [hphi, hunit, mul_one]
  · -- Off-diagonal indices contribute 0: either the coefficient product is 0, or
    -- the pair-unit indicator kills the Kronecker tensor, or `idx = idx0`.
    intro idx _ hidx
    by_cases hprod0 : (∏ ℓ : Fin k,
        (fun ℓ a b =>
          if (ℓ : ℕ) < k - 2 then (if b.val = a.val then (1 : F) else 0)
          else if (ℓ : ℕ) = k - 2 then
            (if (b.val / (dT j : ℕ)) / (dT j : ℕ) = a.val ∧
                (b.val / (dT j : ℕ)) % (dT j : ℕ) = b.val % (dT j : ℕ) then 1 else 0)
          else (if b.val % (dT j : ℕ) = a.val then 1 else 0)) ℓ (jdx ℓ) (idx ℓ)) = 0
    · rw [hprod0, zero_mul]
    · -- Nonzero product: every factor is nonzero.
      have hfac : ∀ ℓ : Fin k,
          (fun ℓ a b =>
            if (ℓ : ℕ) < k - 2 then (if b.val = a.val then (1 : F) else 0)
            else if (ℓ : ℕ) = k - 2 then
              (if (b.val / (dT j : ℕ)) / (dT j : ℕ) = a.val ∧
                  (b.val / (dT j : ℕ)) % (dT j : ℕ) = b.val % (dT j : ℕ) then 1 else 0)
            else (if b.val % (dT j : ℕ) = a.val then 1 else 0)) ℓ (jdx ℓ) (idx ℓ) ≠ 0 := by
        intro ℓ hf0
        exact hprod0 (Finset.prod_eq_zero (Finset.mem_univ ℓ) hf0)
      -- Constraints from `hfac` on each leg.
      have hlt_legs : ∀ ℓ : Fin k, (ℓ : ℕ) < k - 2 → (idx ℓ).val = (jdx ℓ).val := by
        intro ℓ hℓ
        have := hfac ℓ; simp only [if_pos hℓ] at this
        by_contra hc; rw [if_neg hc] at this; exact this rfl
      -- Leg i (= k-2): two div/mod constraints.
      have hfi := hfac i
      simp only [if_neg (show ¬ (i : ℕ) < k - 2 by rw [hi_val]; omega),
        if_pos (show (i : ℕ) = k - 2 by rw [hi_val])] at hfi
      obtain ⟨hdi, hmodi⟩ : (((idx i).val / (dT j : ℕ)) / (dT j : ℕ) = (jdx i).val ∧
          ((idx i).val / (dT j : ℕ)) % (dT j : ℕ) = (idx i).val % (dT j : ℕ)) := by
        by_contra hc; rw [if_neg hc] at hfi; exact hfi rfl
      -- Leg j (= k-1): rightcoord = jdx j.
      have hfj := hfac j
      simp only [if_neg (show ¬ (j : ℕ) < k - 2 by rw [hj_val]; omega),
        if_neg (show ¬ (j : ℕ) = k - 2 by rw [hj_val]; omega)] at hfj
      have hmodj : (idx j).val % (dT j : ℕ) = (jdx j).val := by
        by_contra hc; rw [if_neg hc] at hfj; exact hfj rfl
      -- `idx j` lives in `Fin (1 * dT j)`, so it equals its own mod by `dT j`.
      have hPnpf_j : ((P j * npf j : ℕ+) : ℕ) = (dT j : ℕ) := by
        rw [hQ j, hP_j, one_mul, hnpf_j, hm]
      have hidxj_lt : (idx j).val < (dT j : ℕ) :=
        Nat.lt_of_lt_of_le (idx j).isLt (le_of_eq hPnpf_j)
      have hidxj_val : (idx j).val = (jdx j).val := by
        rw [← Nat.mod_eq_of_lt hidxj_lt]; exact hmodj
      -- The pair-unit indicator at `idx` compares rightcoords at legs i, j.
      have hkRi : (kronRightIndex idx i).val = (idx i).val % (dT j : ℕ) := by
        rw [hkR idx i, hnpf_i, hm]
      have hkRj : (kronRightIndex idx j).val = (idx j).val % (dT j : ℕ) := by
        rw [hkR idx j, hnpf_j, hm]
      -- Split on whether the pair-unit indicator survives.
      by_cases hpair : (idx i).val % (dT j : ℕ) = (jdx j).val
      · -- Then `idx = idx0`, contradicting `hidx`.
        refine absurd ?_ hidx
        funext ℓ; apply Fin.ext
        by_cases hℓ : (ℓ : ℕ) < k - 2
        · rw [hlt_legs ℓ hℓ, hidx0_val, hRval_eq_lt ℓ hℓ, hnpf_lt ℓ hℓ,
            hLval_eq_lt ℓ hℓ, one_mul, zero_add]
        · by_cases hℓ2 : (ℓ : ℕ) = k - 2
          · have hℓi : ℓ = i := Fin.ext (by rw [hi_val]; exact hℓ2)
            have hLval_eq_iℓ : Lval ℓ = (jdx j).val + (dT j : ℕ) * (jdx i).val := by
              rw [hℓi]; exact hLval_eq_i
            rw [hℓi, hidx0_val, hnpf_i, hm, hRval_eq_ge i (by rw [hi_val]; omega),
              show Lval i = (jdx j).val + (dT j : ℕ) * (jdx i).val from hLval_eq_i]
            -- Reconstruct `(idx i).val`.
            have e1 : (dT j : ℕ) * ((idx i).val / (dT j : ℕ)) + (idx i).val % (dT j : ℕ)
                = (idx i).val := Nat.div_add_mod _ _
            have e2 : (dT j : ℕ) * (((idx i).val / (dT j : ℕ)) / (dT j : ℕ))
                + ((idx i).val / (dT j : ℕ)) % (dT j : ℕ) = (idx i).val / (dT j : ℕ) :=
              Nat.div_add_mod _ _
            rw [hdi, hmodi, hpair] at e2
            rw [← e1, ← e2, hpair]; ring
          · have hℓj : (ℓ : ℕ) = k - 1 := by have := ℓ.isLt; omega
            have hℓjeq : ℓ = j := Fin.ext (by rw [hj_val]; exact hℓj)
            rw [hℓjeq, hidxj_val, hidx0_val, hRval_eq_ge j (by rw [hj_val]; omega),
              hLval_eq_j]; ring
      · -- Pair-unit indicator is 0, so the Kronecker tensor vanishes at `idx`.
        apply mul_eq_zero_of_right
        change phiMap (F := F) hk (gammaMap (F := F) hk T) (kronLeftIndex idx) *
            unitPairTensor (F := F) m i j hij (kronRightIndex idx) = 0
        apply mul_eq_zero_of_right
        unfold unitPairTensor
        rw [if_neg]
        rw [hkRi, hkRj, hidxj_val, Nat.mod_eq_of_lt hjdx_j_lt]
        exact hpair
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

/-- Structural comparison from Lemma 3.7 (paper tex:1033).

For sufficiently large `m`, the original tensor restricts to
`φ(γ(T)) ⊠ ⟨m⟩_{k-1,k}`. This is the first displayed restriction comparison in
tex:1033, with paper indices `k-1,k` represented by `Fin k` indices
`⟨k - 2, _⟩, ⟨k - 1, _⟩`. -/
lemma exists_tensor_le_phi_gamma_kronecker_unit {k : ℕ} (hk : 3 ≤ k)
    (hij : (⟨k - 2, by omega⟩ : Fin k) ≠ ⟨k - 1, by omega⟩)
    {dT : Fin k → ℕ+} (T : KTensor F dT) :
    ∃ m : ℕ+,
      Restricts T
        (phiMap (F := F) hk (gammaMap (F := F) hk T) ⊠
          unitPairTensor (F := F) m ⟨k - 2, by omega⟩ ⟨k - 1, by omega⟩ hij) := by
  exact ⟨dT ⟨k - 1, by omega⟩,
    paper_tex_1039_tensor_le_phi_gamma_kronecker_unit_witness (F := F) hk hij T⟩

/-- Structural comparison from Lemma 3.7 (paper tex:1033).

For sufficiently large `m`, `φ(γ(T))` restricts to
`T ⊠ ⟨m⟩_{k-1,k}`. This is the second displayed restriction comparison in
tex:1033, with paper indices `k-1,k` represented by `Fin k` indices
`⟨k - 2, _⟩, ⟨k - 1, _⟩`. -/
lemma exists_phi_gamma_le_tensor_kronecker_unit {k : ℕ} (hk : 3 ≤ k)
    (hij : (⟨k - 2, by omega⟩ : Fin k) ≠ ⟨k - 1, by omega⟩)
    {dT : Fin k → ℕ+} (T : KTensor F dT) :
    ∃ m : ℕ+,
      Restricts (phiMap (F := F) hk (gammaMap (F := F) hk T))
        (T ⊠ unitPairTensor (F := F) m ⟨k - 2, by omega⟩ ⟨k - 1, by omega⟩ hij) := by
  classical
  refine ⟨dT ⟨k - 1, by omega⟩, ?_⟩
  set i : Fin k := ⟨k - 2, by omega⟩ with hi
  set j : Fin k := ⟨k - 1, by omega⟩ with hj
  set m : ℕ+ := dT j with hm
  set P : Fin k → ℕ+ := dPhi hk (dGamma hk dT) with hP
  set npf : Fin k → ℕ+ := naturalPairFormat m i j with hnpf
  have hk2_lt : (k - 2 : ℕ) < k := by omega
  have hk1_lt : (k - 1 : ℕ) < k := by omega
  have hi_val : (i : ℕ) = k - 2 := by rw [hi]
  have hj_val : (j : ℕ) = k - 1 := by rw [hj]
  have hnpf_i : (npf i : ℕ) = (m : ℕ) := by simp [hnpf, naturalPairFormat, hi]
  have hnpf_j : (npf j : ℕ) = (m : ℕ) := by simp [hnpf, naturalPairFormat, hj]
  have hnpf_lt : ∀ ℓ : Fin k, (ℓ : ℕ) < k - 2 → (npf ℓ : ℕ) = 1 := by
    intro ℓ hℓ
    have hℓi : ℓ ≠ i := by intro h; rw [h, hi_val] at hℓ; omega
    have hℓj : ℓ ≠ j := by intro h; rw [h, hj_val] at hℓ; omega
    simp [hnpf, naturalPairFormat, hℓi, hℓj]
  have hP_lt : ∀ ℓ : Fin k, (ℓ : ℕ) < k - 2 → (P ℓ : ℕ) = (dT ℓ : ℕ) := by
    intro ℓ hℓ
    have h1 : (ℓ : ℕ) < k - 1 := by omega
    simp [hP, dPhi, dGamma, h1, hℓ]
  have hP_i : (P i : ℕ) = (dT i : ℕ) * (dT j : ℕ) := by
    have h1 : ((⟨k - 2, hk2_lt⟩ : Fin k) : ℕ) < k - 1 := by simp; omega
    have h2 : ¬ ((⟨(⟨k - 2, hk2_lt⟩ : Fin k), by omega⟩ : Fin (k - 1)) : ℕ) < k - 2 := by simp
    have hival : (P i : ℕ) = (dGamma hk dT ⟨k - 2, by omega⟩ : ℕ) := by
      simp only [hP, dPhi, hi]; rw [dif_pos h1]
    rw [hival]; simp only [dGamma, dif_neg h2, PNat.mul_coe, hi, hj]
  have hP_j : (P j : ℕ) = 1 := by
    have h1 : ¬ (j : ℕ) < k - 1 := by rw [hj_val]; omega
    simp [hP, dPhi, h1]
  have hQ : ∀ ℓ : Fin k, ((dT ℓ * npf ℓ : ℕ+) : ℕ) = (dT ℓ : ℕ) * (npf ℓ : ℕ) := by
    intro ℓ; rw [PNat.mul_coe]
  have hkL : ∀ (idx : ∀ ℓ : Fin k, Fin ((dT ℓ * npf ℓ : ℕ+) : ℕ)) (ℓ : Fin k),
      (kronLeftIndex (dS := dT) (dT := npf) idx ℓ).val = (idx ℓ).val / (npf ℓ : ℕ) := by
    intro idx ℓ; simp [kronLeftIndex, finProdFinEquiv_symm_apply, Fin.divNat]
  have hkR : ∀ (idx : ∀ ℓ : Fin k, Fin ((dT ℓ * npf ℓ : ℕ+) : ℕ)) (ℓ : Fin k),
      (kronRightIndex (dS := dT) (dT := npf) idx ℓ).val = (idx ℓ).val % (npf ℓ : ℕ) := by
    intro idx ℓ; simp [kronRightIndex, finProdFinEquiv_symm_apply, Fin.modNat]
  -- `φ(γ(T))` evaluated at a source index `jdx`: legs `< k-2` pass through, leg
  -- `k-2` splits the merged coordinate `jdx i` via `divNat`/`modNat` by `d_{k-1}`.
  have hphigamma : ∀ (jdx : ∀ ℓ : Fin k, Fin (P ℓ)) (gg : ∀ ℓ : Fin k, Fin (dT ℓ)),
      (∀ ℓ : Fin k, (ℓ : ℕ) < k - 2 → (gg ℓ).val = (jdx ℓ).val) →
      ((gg i).val = (jdx i).val / (dT j : ℕ)) →
      ((gg j).val = (jdx i).val % (dT j : ℕ)) →
      phiMap (F := F) hk (gammaMap (F := F) hk T) jdx = T gg := by
    intro jdx gg hpass hk2 hk1
    unfold phiMap gammaMap
    apply congrArg T
    funext ℓ
    apply Fin.ext
    by_cases hℓ : (ℓ : ℕ) < k - 2
    · simp only [dif_pos hℓ]; rw [hpass ℓ hℓ]; simp only [Fin.val_cast]
    · by_cases hℓ2 : (ℓ : ℕ) = k - 2
      · have hℓi : ℓ = i := Fin.ext (by rw [hi_val]; exact hℓ2)
        rw [hℓi, hk2]
        simp only [dif_neg (show ¬ (i : ℕ) < k - 2 by rw [hi_val]; omega),
          dif_pos (show (i : ℕ) = k - 2 by rw [hi_val]),
          finProdFinEquiv_symm_apply, Fin.coe_divNat, Fin.val_cast]
        rw [hi, hj]
      · have hℓj : (ℓ : ℕ) = k - 1 := by have := ℓ.isLt; omega
        have hℓjeq : ℓ = j := Fin.ext (by rw [hj_val]; exact hℓj)
        rw [hℓjeq, hk1]
        simp only [dif_neg (show ¬ (j : ℕ) < k - 2 by rw [hj_val]; omega),
          dif_neg (show ¬ (j : ℕ) = k - 2 by rw [hj_val]; omega),
          finProdFinEquiv_symm_apply, Fin.coe_modNat, Fin.val_cast]
        rw [hi, hj]
  -- Witness leg-wise matrices.
  refine ⟨fun ℓ a b =>
      if (ℓ : ℕ) < k - 2 then (if b.val = a.val then 1 else 0)
      else if (ℓ : ℕ) = k - 2 then
        (if b.val / (dT j : ℕ) = a.val / (dT j : ℕ) ∧
            b.val % (dT j : ℕ) = a.val % (dT j : ℕ) then 1 else 0)
      else (if b.val / (dT j : ℕ) = b.val % (dT j : ℕ) then 1 else 0), ?_⟩
  intro jdx
  have hjdx_i_lt : (jdx i).val < (P i : ℕ) := (jdx i).isLt
  -- `c := jdx i % d_{k-1}` is the split-off `k-1` coordinate.
  set c : ℕ := (jdx i).val % (dT j : ℕ) with hc
  have hc_lt : c < (dT j : ℕ) := Nat.mod_lt _ (dT j).pos
  have hdivlt : (jdx i).val / (dT j : ℕ) < (dT i : ℕ) := by
    have hlt : (jdx i).val < (dT i : ℕ) * (dT j : ℕ) := hP_i ▸ (jdx i).isLt
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hlt)
  -- target-index left/right values.
  set Lval : Fin k → ℕ := fun ℓ =>
    if (ℓ : ℕ) < k - 2 then (jdx ℓ).val
    else if (ℓ : ℕ) = k - 2 then (jdx i).val / (dT j : ℕ)
    else c with hLval
  set Rval : Fin k → ℕ := fun ℓ =>
    if (ℓ : ℕ) < k - 2 then 0
    else c with hRval
  have hLval_eq_lt : ∀ ℓ : Fin k, (ℓ : ℕ) < k - 2 → Lval ℓ = (jdx ℓ).val := by
    intro ℓ hℓ; simp only [hLval]; rw [if_pos hℓ]
  have hLval_eq_i : Lval i = (jdx i).val / (dT j : ℕ) := by
    simp only [hLval]
    rw [if_neg (show ¬ (i : ℕ) < k - 2 by rw [hi_val]; omega),
      if_pos (show (i : ℕ) = k - 2 by rw [hi_val])]
  have hLval_eq_j : Lval j = c := by
    simp only [hLval]
    rw [if_neg (show ¬ (j : ℕ) < k - 2 by rw [hj_val]; omega),
      if_neg (show ¬ (j : ℕ) = k - 2 by rw [hj_val]; omega)]
  have hRval_eq_lt : ∀ ℓ : Fin k, (ℓ : ℕ) < k - 2 → Rval ℓ = 0 := by
    intro ℓ hℓ; simp only [hRval]; rw [if_pos hℓ]
  have hRval_eq_ge : ∀ ℓ : Fin k, ¬ (ℓ : ℕ) < k - 2 → Rval ℓ = c := by
    intro ℓ hℓ; simp only [hRval]; rw [if_neg hℓ]
  have hLval_lt : ∀ ℓ : Fin k, Lval ℓ < (dT ℓ : ℕ) := by
    intro ℓ
    by_cases hℓ : (ℓ : ℕ) < k - 2
    · rw [hLval_eq_lt ℓ hℓ, ← hP_lt ℓ hℓ]; exact (jdx ℓ).isLt
    · by_cases hℓ2 : (ℓ : ℕ) = k - 2
      · have hℓi : ℓ = i := Fin.ext (by rw [hi_val]; exact hℓ2)
        rw [hℓi, hLval_eq_i]; exact hdivlt
      · have hℓj : (ℓ : ℕ) = k - 1 := by have := ℓ.isLt; omega
        have hℓjeq : ℓ = j := Fin.ext (by rw [hj_val]; exact hℓj)
        rw [hℓjeq, hLval_eq_j]; exact hc_lt
  have hRval_lt : ∀ ℓ : Fin k, Rval ℓ < (npf ℓ : ℕ) := by
    intro ℓ
    by_cases hℓ : (ℓ : ℕ) < k - 2
    · rw [hRval_eq_lt ℓ hℓ, hnpf_lt ℓ hℓ]; omega
    · rw [hRval_eq_ge ℓ hℓ]
      by_cases hℓ2 : (ℓ : ℕ) = k - 2
      · have hℓi : ℓ = i := Fin.ext (by rw [hi_val]; exact hℓ2)
        rw [hℓi, hnpf_i, hm]; exact hc_lt
      · have hℓj : (ℓ : ℕ) = k - 1 := by have := ℓ.isLt; omega
        have hℓjeq : ℓ = j := Fin.ext (by rw [hj_val]; exact hℓj)
        rw [hℓjeq, hnpf_j, hm]; exact hc_lt
  let idx0 : ∀ ℓ : Fin k, Fin ((dT ℓ * npf ℓ : ℕ+) : ℕ) := fun ℓ =>
    ⟨Rval ℓ + (npf ℓ : ℕ) * Lval ℓ, by
      rw [hQ ℓ]
      calc Rval ℓ + (npf ℓ : ℕ) * Lval ℓ
          < (npf ℓ : ℕ) + (npf ℓ : ℕ) * Lval ℓ := by have := hRval_lt ℓ; omega
        _ = (npf ℓ : ℕ) * (Lval ℓ + 1) := by ring
        _ ≤ (npf ℓ : ℕ) * (dT ℓ : ℕ) := Nat.mul_le_mul_left _ (by have := hLval_lt ℓ; omega)
        _ = (dT ℓ : ℕ) * (npf ℓ : ℕ) := by ring⟩
  have hidx0_val : ∀ ℓ : Fin k, (idx0 ℓ).val = Rval ℓ + (npf ℓ : ℕ) * Lval ℓ := fun ℓ => rfl
  have hidx0_L : ∀ ℓ : Fin k, (idx0 ℓ).val / (npf ℓ : ℕ) = Lval ℓ := by
    intro ℓ
    rw [hidx0_val, Nat.add_mul_div_left _ _ (npf ℓ).pos, Nat.div_eq_of_lt (hRval_lt ℓ), zero_add]
  have hidx0_R : ∀ ℓ : Fin k, (idx0 ℓ).val % (npf ℓ : ℕ) = Rval ℓ := by
    intro ℓ
    rw [hidx0_val, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hRval_lt ℓ)]
  rw [Finset.sum_eq_single idx0]
  · -- Value at idx0.
    have hprod : (∏ ℓ : Fin k,
        (if (ℓ : ℕ) < k - 2 then (if (idx0 ℓ).val = (jdx ℓ).val then (1 : F) else 0)
          else if (ℓ : ℕ) = k - 2 then
            (if (idx0 ℓ).val / (dT j : ℕ) = (jdx ℓ).val / (dT j : ℕ) ∧
                (idx0 ℓ).val % (dT j : ℕ) = (jdx ℓ).val % (dT j : ℕ) then 1 else 0)
          else (if (idx0 ℓ).val / (dT j : ℕ) = (idx0 ℓ).val % (dT j : ℕ) then 1 else 0))) = 1 := by
      apply Finset.prod_eq_one
      intro ℓ _
      by_cases hℓ : (ℓ : ℕ) < k - 2
      · rw [if_pos hℓ, if_pos]
        rw [hidx0_val, hRval_eq_lt ℓ hℓ, hnpf_lt ℓ hℓ, hLval_eq_lt ℓ hℓ, one_mul, zero_add]
      · by_cases hℓ2 : (ℓ : ℕ) = k - 2
        · have hℓi : ℓ = i := Fin.ext (by rw [hi_val]; exact hℓ2)
          rw [if_neg hℓ, if_pos hℓ2, if_pos]
          have hnpfi' : (npf ℓ : ℕ) = (dT j : ℕ) := by rw [hℓi, hnpf_i, hm]
          have hL : (idx0 ℓ).val / (dT j : ℕ) = Lval ℓ := by rw [← hnpfi']; exact hidx0_L ℓ
          have hR : (idx0 ℓ).val % (dT j : ℕ) = Rval ℓ := by rw [← hnpfi']; exact hidx0_R ℓ
          have hLval_iℓ : Lval ℓ = (jdx i).val / (dT j : ℕ) := by rw [hℓi]; exact hLval_eq_i
          have hRval_iℓ : Rval ℓ = c := hRval_eq_ge ℓ hℓ
          refine ⟨?_, ?_⟩
          · rw [hL, hLval_iℓ, hℓi]
          · rw [hR, hRval_iℓ, hℓi, hc]
        · have hℓj : (ℓ : ℕ) = k - 1 := by have := ℓ.isLt; omega
          have hℓjeq : ℓ = j := Fin.ext (by rw [hj_val]; exact hℓj)
          rw [if_neg hℓ, if_neg hℓ2, if_pos]
          have hnpfj' : (npf ℓ : ℕ) = (dT j : ℕ) := by rw [hℓjeq, hnpf_j, hm]
          have hL : (idx0 ℓ).val / (dT j : ℕ) = Lval ℓ := by rw [← hnpfj']; exact hidx0_L ℓ
          have hR : (idx0 ℓ).val % (dT j : ℕ) = Rval ℓ := by rw [← hnpfj']; exact hidx0_R ℓ
          rw [hL, hR, hRval_eq_ge ℓ hℓ, show Lval ℓ = c from by rw [hℓjeq]; exact hLval_eq_j]
    have hcoef : (∏ ℓ : Fin k,
        (fun ℓ a b =>
          if (ℓ : ℕ) < k - 2 then (if b.val = a.val then (1 : F) else 0)
          else if (ℓ : ℕ) = k - 2 then
            (if b.val / (dT j : ℕ) = a.val / (dT j : ℕ) ∧
                b.val % (dT j : ℕ) = a.val % (dT j : ℕ) then 1 else 0)
          else (if b.val / (dT j : ℕ) = b.val % (dT j : ℕ) then 1 else 0))
        ℓ (jdx ℓ) (idx0 ℓ)) = 1 := hprod
    rw [hcoef, one_mul]
    change phiMap (F := F) hk (gammaMap (F := F) hk T) jdx =
        T (kronLeftIndex idx0) * unitPairTensor (F := F) m i j hij (kronRightIndex idx0)
    have hkLeq : ∀ ℓ : Fin k, (kronLeftIndex idx0 ℓ).val = Lval ℓ := by
      intro ℓ; rw [hkL idx0 ℓ]; exact hidx0_L ℓ
    have hkReq : ∀ ℓ : Fin k, (kronRightIndex idx0 ℓ).val = Rval ℓ := by
      intro ℓ; rw [hkR idx0 ℓ]; exact hidx0_R ℓ
    have hunit : unitPairTensor (F := F) m i j hij (kronRightIndex idx0) = 1 := by
      unfold unitPairTensor
      rw [if_pos]
      rw [hkReq i, hkReq j, hRval_eq_ge i (by rw [hi_val]; omega),
        hRval_eq_ge j (by rw [hj_val]; omega)]
    rw [hunit, mul_one]
    -- `φ(γ(T)) jdx = T (kronLeftIndex idx0)`.
    apply hphigamma
    · intro ℓ hℓ; rw [hkLeq ℓ, hLval_eq_lt ℓ hℓ]
    · rw [hkLeq i, hLval_eq_i]
    · rw [hkLeq j, hLval_eq_j, hc]
  · -- Off-diagonal indices contribute 0.
    intro idx _ hidx
    by_cases hprod0 : (∏ ℓ : Fin k,
        (fun ℓ a b =>
          if (ℓ : ℕ) < k - 2 then (if b.val = a.val then (1 : F) else 0)
          else if (ℓ : ℕ) = k - 2 then
            (if b.val / (dT j : ℕ) = a.val / (dT j : ℕ) ∧
                b.val % (dT j : ℕ) = a.val % (dT j : ℕ) then 1 else 0)
          else (if b.val / (dT j : ℕ) = b.val % (dT j : ℕ) then 1 else 0))
        ℓ (jdx ℓ) (idx ℓ)) = 0
    · rw [hprod0, zero_mul]
    · have hfac : ∀ ℓ : Fin k,
          (fun ℓ a b =>
            if (ℓ : ℕ) < k - 2 then (if b.val = a.val then (1 : F) else 0)
            else if (ℓ : ℕ) = k - 2 then
              (if b.val / (dT j : ℕ) = a.val / (dT j : ℕ) ∧
                  b.val % (dT j : ℕ) = a.val % (dT j : ℕ) then 1 else 0)
            else (if b.val / (dT j : ℕ) = b.val % (dT j : ℕ) then 1 else 0))
          ℓ (jdx ℓ) (idx ℓ) ≠ 0 := by
        intro ℓ hf0
        exact hprod0 (Finset.prod_eq_zero (Finset.mem_univ ℓ) hf0)
      have hlt_legs : ∀ ℓ : Fin k, (ℓ : ℕ) < k - 2 → (idx ℓ).val = (jdx ℓ).val := by
        intro ℓ hℓ
        have := hfac ℓ; simp only [if_pos hℓ] at this
        by_contra hcc; rw [if_neg hcc] at this; exact this rfl
      have hfi := hfac i
      simp only [if_neg (show ¬ (i : ℕ) < k - 2 by rw [hi_val]; omega),
        if_pos (show (i : ℕ) = k - 2 by rw [hi_val])] at hfi
      obtain ⟨hdi, hmodi⟩ : ((idx i).val / (dT j : ℕ) = (jdx i).val / (dT j : ℕ) ∧
          (idx i).val % (dT j : ℕ) = (jdx i).val % (dT j : ℕ)) := by
        by_contra hcc; rw [if_neg hcc] at hfi; exact hfi rfl
      have hfj := hfac j
      simp only [if_neg (show ¬ (j : ℕ) < k - 2 by rw [hj_val]; omega),
        if_neg (show ¬ (j : ℕ) = k - 2 by rw [hj_val]; omega)] at hfj
      have hjeq : (idx j).val / (dT j : ℕ) = (idx j).val % (dT j : ℕ) := by
        by_contra hcc; rw [if_neg hcc] at hfj; exact hfj rfl
      -- Rightcoords for the pair-unit.
      have hkRi : (kronRightIndex idx i).val = (idx i).val % (dT j : ℕ) := by
        rw [hkR idx i, hnpf_i, hm]
      have hkRj : (kronRightIndex idx j).val = (idx j).val % (dT j : ℕ) := by
        rw [hkR idx j, hnpf_j, hm]
      by_cases hpair : (idx i).val % (dT j : ℕ) = (idx j).val % (dT j : ℕ)
      · -- `idx = idx0`, contradicting `hidx`.
        refine absurd ?_ hidx
        funext ℓ; apply Fin.ext
        by_cases hℓ : (ℓ : ℕ) < k - 2
        · rw [hlt_legs ℓ hℓ, hidx0_val, hRval_eq_lt ℓ hℓ, hnpf_lt ℓ hℓ,
            hLval_eq_lt ℓ hℓ, one_mul, zero_add]
        · by_cases hℓ2 : (ℓ : ℕ) = k - 2
          · have hℓi : ℓ = i := Fin.ext (by rw [hi_val]; exact hℓ2)
            rw [hℓi, hidx0_val, hnpf_i, hm,
              show Rval i = c from hRval_eq_ge i (by rw [hi_val]; omega),
              show Lval i = (jdx i).val / (dT j : ℕ) from hLval_eq_i]
            have e1 : (dT j : ℕ) * ((idx i).val / (dT j : ℕ)) + (idx i).val % (dT j : ℕ)
                = (idx i).val := Nat.div_add_mod _ _
            -- `c = jdx i % dT j = idx i % dT j` (from `hmodi`).
            have hci : (idx i).val % (dT j : ℕ) = c := by rw [hmodi]
            rw [← e1, hdi, hci]; ring
          · have hℓj : (ℓ : ℕ) = k - 1 := by have := ℓ.isLt; omega
            have hℓjeq : ℓ = j := Fin.ext (by rw [hj_val]; exact hℓj)
            -- `idx j` is determined by `idx j / dT j = idx j % dT j` and the pair.
            rw [hℓjeq, hidx0_val,
              show Rval j = c from hRval_eq_ge j (by rw [hj_val]; omega),
              show Lval j = c from hLval_eq_j, hnpf_j, hm]
            have e1 : (dT j : ℕ) * ((idx j).val / (dT j : ℕ)) + (idx j).val % (dT j : ℕ)
                = (idx j).val := Nat.div_add_mod _ _
            -- `idx j % dT j = idx i % dT j = jdx i % dT j = c`.
            have hcj : (idx j).val % (dT j : ℕ) = c := by
              rw [← hpair, hmodi]
            rw [← e1, hjeq, hcj]; ring
      · -- Pair-unit indicator is 0; Kronecker tensor vanishes.
        apply mul_eq_zero_of_right
        change T (kronLeftIndex idx) * unitPairTensor (F := F) m i j hij (kronRightIndex idx) = 0
        apply mul_eq_zero_of_right
        unfold unitPairTensor
        rw [if_neg]
        rw [hkRi, hkRj]; exact hpair
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

/-- Lemma 3.7 helper (paper tex:1029-1034).

Under the free-unit hypothesis, every tensor has the same spectral value as its
split-then-merged form `φ(γ(T))`. The proof applies the two tex:1033 structural
comparisons, multiplicativity, monotonicity, and Lemma 3.6 (`free_units`). -/
lemma phi_gamma_F_eq {k : ℕ} (hk : 3 ≤ k) (Fspec : SpectralPoint k F)
    (hij : (⟨k - 2, by omega⟩ : Fin k) ≠ ⟨k - 1, by omega⟩)
    (h2 : Fspec.toFun
        (unitPairTensor (F := F) 2 ⟨k - 2, by omega⟩ ⟨k - 1, by omega⟩ hij) = 1)
    {dT : Fin k → ℕ+} (T : KTensor F dT) :
    Fspec.toFun (phiMap (F := F) hk (gammaMap (F := F) hk T)) = Fspec.toFun T := by
  classical
  let i : Fin k := ⟨k - 2, by omega⟩
  let j : Fin k := ⟨k - 1, by omega⟩
  obtain ⟨m₁, hm₁⟩ := exists_tensor_le_phi_gamma_kronecker_unit
    (F := F) hk hij T
  obtain ⟨m₂, hm₂⟩ := exists_phi_gamma_le_tensor_kronecker_unit
    (F := F) hk hij T
  have hunit₁ :
      Fspec.toFun (unitPairTensor (F := F) m₁ i j hij) = 1 := by
    simpa [i, j] using free_units (F := F) Fspec i j hij (by simpa [i, j] using h2) m₁
  have hunit₂ :
      Fspec.toFun (unitPairTensor (F := F) m₂ i j hij) = 1 := by
    simpa [i, j] using free_units (F := F) Fspec i j hij (by simpa [i, j] using h2) m₂
  have hle_low :
      Fspec.toFun T ≤ Fspec.toFun (phiMap (F := F) hk (gammaMap (F := F) hk T)) := by
    have hmono := Fspec.mono T
      (phiMap (F := F) hk (gammaMap (F := F) hk T) ⊠
        unitPairTensor (F := F) m₁ i j hij) (by simpa [i, j] using hm₁)
    have hmult := Fspec.mult (phiMap (F := F) hk (gammaMap (F := F) hk T))
      (unitPairTensor (F := F) m₁ i j hij)
    simpa [hmult, hunit₁] using hmono
  have hle_high :
      Fspec.toFun (phiMap (F := F) hk (gammaMap (F := F) hk T)) ≤ Fspec.toFun T := by
    have hmono := Fspec.mono (phiMap (F := F) hk (gammaMap (F := F) hk T))
      (T ⊠ unitPairTensor (F := F) m₂ i j hij) (by simpa [i, j] using hm₂)
    have hmult := Fspec.mult T (unitPairTensor (F := F) m₂ i j hij)
    simpa [hmult, hunit₂] using hmono
  exact le_antisymm hle_high hle_low

/-- **Lemma 3.7** (tex:1029-1034, `\label{lem:free-splitting}`).

If `F ∈ Δ(F, k)` (with `k ≥ 3`) and `F(⟨2⟩_{k-1,k}) = 1`, then for any two
`k`-tensors `S, T` (of possibly different formats) with `γ(S) ∼ γ(T)`,
we have `F(S) = F(T)`.

The `k-1, k` in the paper correspond to `Fin k`-indices `⟨k-2, _⟩, ⟨k-1, _⟩`. -/
theorem free_splitting {k : ℕ} (hk : 3 ≤ k) (Fspec : SpectralPoint k F)
    (hij : (⟨k - 2, by omega⟩ : Fin k) ≠ ⟨k - 1, by omega⟩)
    (h2 : Fspec.toFun
        (unitPairTensor (F := F) 2 ⟨k - 2, by omega⟩ ⟨k - 1, by omega⟩ hij) = 1)
    {dS dT : Fin k → ℕ+} (S : KTensor F dS) (T : KTensor F dT)
    (h : gammaMap (F := F) hk S ∼ₜ gammaMap (F := F) hk T) :
    Fspec.toFun S = Fspec.toFun T := by
  classical
  have hphi_le :
      Restricts (phiMap (F := F) hk (gammaMap (F := F) hk S))
        (phiMap (F := F) hk (gammaMap (F := F) hk T)) :=
    phiMap_restricts (F := F) hk h.1
  have hphi_ge :
      Restricts (phiMap (F := F) hk (gammaMap (F := F) hk T))
        (phiMap (F := F) hk (gammaMap (F := F) hk S)) :=
    phiMap_restricts (F := F) hk h.2
  have hphi_eq :
      Fspec.toFun (phiMap (F := F) hk (gammaMap (F := F) hk S)) =
        Fspec.toFun (phiMap (F := F) hk (gammaMap (F := F) hk T)) := by
    exact le_antisymm
      (Fspec.mono (phiMap (F := F) hk (gammaMap (F := F) hk S))
        (phiMap (F := F) hk (gammaMap (F := F) hk T)) hphi_le)
      (Fspec.mono (phiMap (F := F) hk (gammaMap (F := F) hk T))
        (phiMap (F := F) hk (gammaMap (F := F) hk S)) hphi_ge)
  calc
    Fspec.toFun S = Fspec.toFun (phiMap (F := F) hk (gammaMap (F := F) hk S)) := by
      exact (phi_gamma_F_eq (F := F) hk Fspec hij h2 S).symm
    _ = Fspec.toFun (phiMap (F := F) hk (gammaMap (F := F) hk T)) := hphi_eq
    _ = Fspec.toFun T := phi_gamma_F_eq (F := F) hk Fspec hij h2 T

/-! ## Lemma 3.8 (tex:1038-1045). -/

set_option linter.flexible false in
/-- Tensor-format identity used in Lemma 3.8 multiplicativity (paper tex:1042).

Merging after padding the Kronecker product agrees, up to restriction-equivalence,
with merging after taking the Kronecker product of the padded tensors. -/
lemma gamma_phi_kron_equiv {k : ℕ} (hk : 3 ≤ k) {eS eT : Fin (k - 1) → ℕ+}
    (S : KTensor F eS) (T : KTensor F eT) :
    gammaMap (F := F) hk (phiMap (F := F) hk S ⊠ phiMap (F := F) hk T) ∼ₜ
      gammaMap (F := F) hk (phiMap (F := F) hk (S ⊠ T)) := by
  classical
  have hfmt : ∀ i : Fin (k - 1),
      (dGamma hk (fun i : Fin k => dPhi hk eS i * dPhi hk eT i) i : ℕ) =
        (dGamma hk (dPhi hk (fun i : Fin (k - 1) => eS i * eT i)) i : ℕ) := by
    intro i
    by_cases hi : (i : ℕ) < k - 2
    · simp [dGamma, dPhi, hi]
    · have hi_eq : (i : ℕ) = k - 2 := by
        have := i.isLt
        omega
      have hkm2_lt_km1 : k - 2 < k - 1 := by omega
      simp [dGamma, dPhi, hi_eq, hkm2_lt_km1, PNat.mul_coe]
  constructor
  · apply Restricts.of_eq_cast hfmt
    intro jdx
    simp [gammaMap, phiMap, kroneckerTensor, kronLeftIndex, kronRightIndex]
    congr 1
    · apply congrArg S
      funext i
      by_cases hi : (i : ℕ) < k - 2
      · ext
        simp [hi, kronLeftIndex, Fin.divNat, dPhi]
      · have hi_eq : (i : ℕ) = k - 2 := by
          have := i.isLt
          omega
        have hi_fin : i = ⟨k - 2, by omega⟩ := Fin.ext hi_eq
        have hkm2_lt_km1 : k - 2 < k - 1 := by omega
        ext
        simp [hi_fin, hkm2_lt_km1, kronLeftIndex, Fin.divNat, dPhi, Nat.div_one]
    · apply congrArg T
      funext i
      by_cases hi : (i : ℕ) < k - 2
      · ext
        simp [hi, kronRightIndex, Fin.modNat, dPhi]
      · have hi_eq : (i : ℕ) = k - 2 := by
          have := i.isLt
          omega
        have hi_fin : i = ⟨k - 2, by omega⟩ := Fin.ext hi_eq
        have hkm2_lt_km1 : k - 2 < k - 1 := by omega
        ext
        simp [hi_fin, hkm2_lt_km1, kronRightIndex, Fin.modNat, dPhi]
  · apply Restricts.of_eq_cast (fun i => (hfmt i).symm)
    intro jdx
    simp [gammaMap, phiMap, kroneckerTensor, kronLeftIndex, kronRightIndex]
    congr 1
    · apply congrArg S
      funext i
      by_cases hi : (i : ℕ) < k - 2
      · ext
        simp [hi, kronLeftIndex, Fin.divNat, dPhi]
      · have hi_eq : (i : ℕ) = k - 2 := by
          have := i.isLt
          omega
        have hi_fin : i = ⟨k - 2, by omega⟩ := Fin.ext hi_eq
        have hkm2_lt_km1 : k - 2 < k - 1 := by omega
        ext
        simp [hi_fin, hkm2_lt_km1, kronLeftIndex, Fin.divNat, dPhi, Nat.div_one]
    · apply congrArg T
      funext i
      by_cases hi : (i : ℕ) < k - 2
      · ext
        simp [hi, kronRightIndex, Fin.modNat, dPhi]
      · have hi_eq : (i : ℕ) = k - 2 := by
          have := i.isLt
          omega
        have hi_fin : i = ⟨k - 2, by omega⟩ := Fin.ext hi_eq
        have hkm2_lt_km1 : k - 2 < k - 1 := by omega
        ext
        simp [hi_fin, hkm2_lt_km1, kronRightIndex, Fin.modNat, dPhi]

/-- Value of `directSumTensor S T` at a multi-index, split by block (paper tex:1042).

If all legs of `idx` lie in the `S`-block (`< dS`), the value is `S` at the
restricted index; if all lie in the `T`-block (`≥ dS`), the value is `T` at the
shifted index; otherwise it is `0`. -/
private lemma directSumTensor_apply_block {k : ℕ} {dS dT : Fin k → ℕ+}
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

/-- Value of `γ(W)` at a `(k-1)`-index in terms of a `k`-index `gg` (paper tex:1042):
legs `< k-2` pass through, leg `k-2` is the merged coordinate `divNat` by `d_{k-1}`,
leg `k-1` is the merged coordinate `modNat` by `d_{k-1}`. -/
private lemma gammaMap_apply_decode {k : ℕ} (hk : 3 ≤ k) {d : Fin k → ℕ+}
    (W : KTensor F d) (jdx : ∀ ℓ : Fin (k - 1), Fin (dGamma hk d ℓ))
    (gg : ∀ ℓ : Fin k, Fin (d ℓ))
    (hpass : ∀ ℓ : Fin k, (hℓ : (ℓ : ℕ) < k - 2) →
      (gg ℓ).val = (jdx ⟨ℓ, by omega⟩).val)
    (hk2 : (gg ⟨k - 2, by omega⟩).val
      = (jdx ⟨k - 2, by omega⟩).val / (d ⟨k - 1, by omega⟩ : ℕ))
    (hk1 : (gg ⟨k - 1, by omega⟩).val
      = (jdx ⟨k - 2, by omega⟩).val % (d ⟨k - 1, by omega⟩ : ℕ)) :
    gammaMap (F := F) hk W jdx = W gg := by
  classical
  unfold gammaMap
  apply congrArg W
  funext ℓ
  apply Fin.ext
  by_cases hℓ : (ℓ : ℕ) < k - 2
  · simp only [dif_pos hℓ]
    rw [hpass ℓ hℓ]
    simp only [Fin.val_cast]
  · by_cases hℓ2 : (ℓ : ℕ) = k - 2
    · have hℓi : ℓ = ⟨k - 2, by omega⟩ := Fin.ext hℓ2
      simp only [dif_neg hℓ, dif_pos hℓ2, finProdFinEquiv_symm_apply,
        Fin.coe_divNat, Fin.val_cast]
      rw [hℓi]; exact hk2.symm
    · have hℓj : (ℓ : ℕ) = k - 1 := by have := ℓ.isLt; omega
      have hℓjeq : ℓ = ⟨k - 1, by omega⟩ := Fin.ext hℓj
      simp only [dif_neg hℓ, dif_neg hℓ2, finProdFinEquiv_symm_apply,
        Fin.coe_modNat, Fin.val_cast]
      rw [hℓjeq]; exact hk1.symm

/-- Tensor-format identity used in Lemma 3.8 additivity (paper tex:1042).

Merging after padding the direct sum agrees, up to restriction-equivalence, with
merging after taking the direct sum of the padded tensors. -/
private lemma gamma_phi_add_equiv_witness {k : ℕ} (hk : 3 ≤ k) {eS eT : Fin (k - 1) → ℕ+}
    (S : KTensor F eS) (T : KTensor F eT) :
    gammaMap (F := F) hk (phiMap (F := F) hk S ⊕ₜ phiMap (F := F) hk T) ∼ₜ
      gammaMap (F := F) hk (phiMap (F := F) hk (S ⊕ₜ T)) := by
  -- Tensor-format identity from paper tex:1042.  The nontrivial merged leg
  -- records the direct-sum block tag introduced by padding; the witnesses are
  -- the block-compatible embedding and projection, with identity/cast matrices
  -- on all earlier legs.
  classical
  -- Abbreviations.
  set s2 : ℕ := (eS ⟨k - 2, by omega⟩ : ℕ) with hs2
  -- Inner k-tensor formats.
  set DL : Fin k → ℕ+ := fun ℓ => dPhi hk eS ℓ + dPhi hk eT ℓ with hDL
  set DR : Fin k → ℕ+ := dPhi hk (fun i : Fin (k - 1) => eS i + eT i) with hDR
  -- Merged (γ) formats.
  set eL : Fin (k - 1) → ℕ+ := dGamma hk DL with heL
  set eR : Fin (k - 1) → ℕ+ := dGamma hk DR with heR
  -- Last-leg dims of the inner formats.
  have hDL_last : (DL ⟨k - 1, by omega⟩ : ℕ) = 2 := by
    simp only [hDL, dPhi, PNat.add_coe,
      dif_neg (show ¬ ((⟨k - 1, by omega⟩ : Fin k) : ℕ) < k - 1 by simp), PNat.one_coe]
  have hDR_last : (DR ⟨k - 1, by omega⟩ : ℕ) = 1 := by
    simp only [hDR, dPhi,
      dif_neg (show ¬ ((⟨k - 1, by omega⟩ : Fin k) : ℕ) < k - 1 by simp), PNat.one_coe]
  -- Merged-leg dims.
  set st2 : ℕ := (eS ⟨k - 2, by omega⟩ + eT ⟨k - 2, by omega⟩ : ℕ) with hst2
  have hDL_k2 : (DL ⟨k - 2, by omega⟩ : ℕ) = st2 := by
    simp only [hDL, dPhi, hst2, PNat.add_coe,
      dif_pos (show ((⟨k - 2, by omega⟩ : Fin k) : ℕ) < k - 1 by simp; omega)]
  have hDR_k2 : (DR ⟨k - 2, by omega⟩ : ℕ) = st2 := by
    simp only [hDR, dPhi, hst2,
      dif_pos (show ((⟨k - 2, by omega⟩ : Fin k) : ℕ) < k - 1 by simp; omega), PNat.add_coe]
  have heL_last : (eL ⟨k - 2, by omega⟩ : ℕ) = st2 * 2 := by
    have h2 : ¬ ((⟨k - 2, by omega⟩ : Fin (k - 1)) : ℕ) < k - 2 := by simp
    simp only [heL, dGamma, dif_neg h2, PNat.mul_coe, hDL_k2, hDL_last]
  have heR_last : (eR ⟨k - 2, by omega⟩ : ℕ) = st2 := by
    have h2 : ¬ ((⟨k - 2, by omega⟩ : Fin (k - 1)) : ℕ) < k - 2 := by simp
    simp only [heR, dGamma, dif_neg h2, PNat.mul_coe, hDR_k2, hDR_last, Nat.mul_one]
  have heL_lt : ∀ ℓ : Fin (k - 1), (ℓ : ℕ) < k - 2 →
      (eL ℓ : ℕ) = (eS ℓ + eT ℓ : ℕ) := by
    intro ℓ hℓ
    have hℓ1 : (ℓ : ℕ) < k - 1 := by omega
    simp only [heL, hDL, dGamma, dPhi, dif_pos hℓ, dif_pos hℓ1, PNat.add_coe]
  have heR_lt : ∀ ℓ : Fin (k - 1), (ℓ : ℕ) < k - 2 →
      (eR ℓ : ℕ) = (eS ℓ + eT ℓ : ℕ) := by
    intro ℓ hℓ
    have hℓ1 : (ℓ : ℕ) < k - 1 := by omega
    simp only [heR, hDR, dGamma, dPhi, dif_pos hℓ, dif_pos hℓ1, PNat.add_coe]
  -- Format equality for the RHS γ-format and the direct-sum `S⊕T` format.
  have hfmtR : ∀ ℓ : Fin (k - 1), (eR ℓ : ℕ) = ((eS ℓ + eT ℓ : ℕ+) : ℕ) := by
    intro ℓ
    by_cases hℓ : (ℓ : ℕ) < k - 2
    · rw [heR_lt ℓ hℓ, PNat.add_coe]
    · have hval : (ℓ : ℕ) = k - 2 := by have := ℓ.isLt; omega
      have hℓi : ℓ = ⟨k - 2, by omega⟩ := Fin.ext hval
      rw [hℓi, heR_last, PNat.add_coe, hst2]
  -- ============ hR : γ(φ(S⊕T)) ∼ₜ (S⊕T) ============
  -- The dim-1 pad makes the merged leg carry the `S⊕T`-coordinate directly.
  -- Dim match: `eR ⟨ℓ⟩ = DR ℓ` for `ℓ < k-1` (the γ-format leg equals the inner
  -- format leg, since the pad does not affect legs `< k-1`).
  have heR_DR : ∀ (ℓ : Fin k) (hℓ : (ℓ : ℕ) < k - 1),
      (eR ⟨(ℓ : ℕ), by omega⟩ : ℕ) = (DR ℓ : ℕ) := by
    intro ℓ hℓ
    by_cases hℓ2 : (ℓ : ℕ) < k - 2
    · rw [heR_lt ⟨(ℓ : ℕ), by omega⟩ hℓ2]
      simp only [hDR, dPhi, dif_pos hℓ, PNat.add_coe]
    · have hval : (ℓ : ℕ) = k - 2 := by omega
      have : (⟨(ℓ : ℕ), by omega⟩ : Fin (k - 1)) = ⟨k - 2, by omega⟩ := Fin.ext hval
      rw [this, heR_last, hst2]
      have hℓi : ℓ = ⟨k - 2, by omega⟩ := Fin.ext hval
      rw [hℓi, hDR_k2, hst2]
  -- The lifted `k`-index for `gammaMap` decode (legs `< k-1` from `jdx`, pad `0`).
  have hRval : ∀ jdx : ∀ ℓ : Fin (k - 1), Fin (eR ℓ),
      gammaMap (F := F) hk (phiMap (F := F) hk (S ⊕ₜ T)) jdx
        = (S ⊕ₜ T) (fun i => Fin.cast (hfmtR i) (jdx i)) := by
    intro jdx
    set gg : ∀ ℓ : Fin k, Fin (DR ℓ) := fun ℓ =>
      if hℓ : (ℓ : ℕ) < k - 1 then
        Fin.cast (heR_DR ℓ hℓ) (jdx ⟨(ℓ : ℕ), by omega⟩)
      else Fin.cast (by
        have hval : (ℓ : ℕ) = k - 1 := by have := ℓ.isLt; omega
        have hℓi : ℓ = ⟨k - 1, by omega⟩ := Fin.ext hval
        rw [hℓi, hDR_last]) (0 : Fin 1) with hgg
    have hgg_lt : ∀ ℓ : Fin k, (hℓ : (ℓ : ℕ) < k - 1) →
        (gg ℓ).val = (jdx ⟨(ℓ : ℕ), by omega⟩).val := by
      intro ℓ hℓ; simp only [hgg, dif_pos hℓ, Fin.val_cast]
    have hgg_last : (gg ⟨k - 1, by omega⟩).val = 0 := by
      simp only [hgg, dif_neg (show ¬ ((⟨k - 1, by omega⟩ : Fin k) : ℕ) < k - 1 by simp),
        Fin.val_cast, Fin.val_zero]
    rw [gammaMap_apply_decode (F := F) hk (phiMap (F := F) hk (S ⊕ₜ T)) jdx gg
      (fun ℓ hℓ => hgg_lt ℓ (by omega))
      (by rw [hgg_lt ⟨k - 2, by omega⟩ (by simp; omega)]
          conv_rhs => rw [show ((DR ⟨k - 1, by omega⟩ : ℕ)) = 1 from hDR_last]
          rw [Nat.div_one])
      (by rw [hgg_last]
          conv_rhs => rw [show ((DR ⟨k - 1, by omega⟩ : ℕ)) = 1 from hDR_last]
          rw [Nat.mod_one])]
    -- `phiMap (S⊕T) gg = (S⊕T)(prune gg)`, prune legs `< k-1` of `gg` = `cast jdx`.
    unfold phiMap
    apply congrArg (S ⊕ₜ T)
    funext i
    apply Fin.ext
    have hi : (i : ℕ) < k - 1 := i.isLt
    simp only [Fin.val_cast, hgg_lt ⟨(i : ℕ), by omega⟩ hi]
  -- ============ hR : γ(φ(S⊕T)) ∼ₜ (S⊕T) ============
  have hR : RestrictsEquiv (F := F) (gammaMap (F := F) hk (phiMap (F := F) hk (S ⊕ₜ T)))
      (S ⊕ₜ T) := by
    constructor
    · exact Restricts.of_eq_cast hfmtR (fun jdx => hRval jdx)
    · refine Restricts.of_eq_cast (fun ℓ => (hfmtR ℓ).symm) ?_
      intro jdx
      rw [hRval (fun i => Fin.cast (hfmtR i).symm (jdx i))]
      apply congrArg (S ⊕ₜ T)
      funext i
      apply Fin.ext
      simp only [Fin.val_cast]
  -- ============ LHS evaluation ============
  -- `dPhi eS`/`dPhi eT` leg dims (for the block conditions of `φS ⊕ φT`).
  have hdPhiS_lt : ∀ (ℓ : Fin k) (hℓ : (ℓ : ℕ) < k - 1),
      (dPhi hk eS ℓ : ℕ) = (eS ⟨(ℓ : ℕ), by omega⟩ : ℕ) := by
    intro ℓ hℓ; simp only [dPhi, dif_pos hℓ]
  have hdPhiS_last : (dPhi hk eS ⟨k - 1, by omega⟩ : ℕ) = 1 := by
    simp only [dPhi, dif_neg (show ¬ ((⟨k - 1, by omega⟩ : Fin k) : ℕ) < k - 1 by simp),
      PNat.one_coe]
  -- LHS value: decode `jdx` to `gg`, then split `φS ⊕ φT` into blocks.
  -- We package the underlying `S⊕T`-index `w` and the tag/block test.
  -- For a given LHS-index `jdx`, set `mL = jdx⟨k-2⟩ / 2`, `tag = jdx⟨k-2⟩ % 2`.
  have hLval : ∀ (jdx : ∀ ℓ : Fin (k - 1), Fin (eL ℓ))
      (w : ∀ i : Fin (k - 1), Fin ((eS i + eT i : ℕ+) : ℕ)),
      (∀ ℓ : Fin (k - 1), (ℓ : ℕ) < k - 2 → (w ℓ).val = (jdx ℓ).val) →
      ((w ⟨k - 2, by omega⟩).val = (jdx ⟨k - 2, by omega⟩).val / 2) →
      gammaMap (F := F) hk (phiMap (F := F) hk S ⊕ₜ phiMap (F := F) hk T) jdx
        = if (jdx ⟨k - 2, by omega⟩).val % 2
              = (if (∀ i : Fin (k - 1), (w i).val < (eS i : ℕ)) then 0 else 1) then
            (S ⊕ₜ T) w
          else 0 := by
    intro jdx w hpass hk2
    -- Dim match for `gg` legs `< k-2`: `eL ⟨ℓ⟩ = DL ℓ`.
    have heL_DL_lt : ∀ (ℓ : Fin k) (hℓ : (ℓ : ℕ) < k - 2),
        (eL ⟨(ℓ : ℕ), by omega⟩ : ℕ) = (DL ℓ : ℕ) := by
      intro ℓ hℓ
      rw [heL_lt ⟨(ℓ : ℕ), by omega⟩ hℓ]
      simp only [hDL, dPhi, dif_pos (show (ℓ : ℕ) < k - 1 by omega), PNat.add_coe]
    have hjdx_k2_lt : (jdx ⟨k - 2, by omega⟩).val < st2 * 2 :=
      heL_last ▸ (jdx ⟨k - 2, by omega⟩).isLt
    have hmL_lt : (jdx ⟨k - 2, by omega⟩).val / 2 < (DL ⟨k - 2, by omega⟩ : ℕ) := by
      rw [hDL_k2]; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hjdx_k2_lt)
    have htag_lt : (jdx ⟨k - 2, by omega⟩).val % 2 < (DL ⟨k - 1, by omega⟩ : ℕ) := by
      rw [hDL_last]; exact Nat.mod_lt _ (by norm_num)
    -- Decoded `k`-index.
    set gg : ∀ ℓ : Fin k, Fin (DL ℓ) := fun ℓ =>
      if hℓ : (ℓ : ℕ) < k - 2 then
        Fin.cast (heL_DL_lt ℓ hℓ) (jdx ⟨(ℓ : ℕ), by omega⟩)
      else if hℓ2 : (ℓ : ℕ) = k - 2 then
        Fin.cast (by rw [show ℓ = ⟨k - 2, by omega⟩ from Fin.ext hℓ2])
          ⟨(jdx ⟨k - 2, by omega⟩).val / 2, hmL_lt⟩
      else
        Fin.cast (by
          rw [show ℓ = ⟨k - 1, by omega⟩ from Fin.ext (show (ℓ : ℕ) = k - 1 by
            have h1 : ¬ (ℓ : ℕ) < k - 2 := hℓ
            have h2 : ¬ (ℓ : ℕ) = k - 2 := hℓ2
            have := ℓ.isLt; omega)])
          ⟨(jdx ⟨k - 2, by omega⟩).val % 2, htag_lt⟩ with hgg
    have hgg_lt : ∀ ℓ : Fin k, (hℓ : (ℓ : ℕ) < k - 2) →
        (gg ℓ).val = (jdx ⟨(ℓ : ℕ), by omega⟩).val := by
      intro ℓ hℓ; simp only [hgg, dif_pos hℓ, Fin.val_cast]
    have hgg_k2 : (gg ⟨k - 2, by omega⟩).val = (jdx ⟨k - 2, by omega⟩).val / 2 := by
      simp only [hgg, dif_neg (show ¬ ((⟨k - 2, by omega⟩ : Fin k) : ℕ) < k - 2 by simp),
        ↓reduceDIte, Fin.val_cast]
    have hgg_k1 : (gg ⟨k - 1, by omega⟩).val = (jdx ⟨k - 2, by omega⟩).val % 2 := by
      simp only [hgg, dif_neg (show ¬ ((⟨k - 1, by omega⟩ : Fin k) : ℕ) < k - 2 by simp; omega),
        dif_neg (show ¬ ((⟨k - 1, by omega⟩ : Fin k) : ℕ) = k - 2 by simp; omega), Fin.val_cast]
    rw [gammaMap_apply_decode (F := F) hk (phiMap (F := F) hk S ⊕ₜ phiMap (F := F) hk T) jdx gg
      (fun ℓ hℓ => hgg_lt ℓ hℓ)
      (by rw [hgg_k2]; congr 1; rw [hDL_last])
      (by rw [hgg_k1]; congr 1; rw [hDL_last])]
    -- Relate `gg` legs to `w` legs (via `jdx`).
    have hgg_w : ∀ i : Fin (k - 1), (gg ⟨(i : ℕ), by omega⟩).val = (w i).val := by
      intro i
      by_cases hi : (i : ℕ) < k - 2
      · rw [hgg_lt ⟨(i : ℕ), by omega⟩ hi, hpass i hi]
      · have hval : (i : ℕ) = k - 2 := by have := i.isLt; omega
        have hii : i = ⟨k - 2, by omega⟩ := Fin.ext hval
        have hii2 : (⟨(i : ℕ), by omega⟩ : Fin k) = ⟨k - 2, by omega⟩ := Fin.ext hval
        rw [hii2, hgg_k2, hii, hk2]
    -- `dPhi eS` value at the `i`-lifted leg.
    have hdPhiS_i : ∀ i : Fin (k - 1), (dPhi hk eS ⟨(i : ℕ), by omega⟩ : ℕ) = (eS i : ℕ) := by
      intro i
      rw [hdPhiS_lt ⟨(i : ℕ), by omega⟩ (by have := i.isLt; omega)]
    -- S-block equivalence: `(φS⊕φT) gg` all-S ⟺ (`w` all-S) ∧ tag = 0.
    have hSblock : (∀ ℓ : Fin k, (gg ℓ).val < (dPhi hk eS ℓ : ℕ)) ↔
        ((∀ i : Fin (k - 1), (w i).val < (eS i : ℕ)) ∧
          (jdx ⟨k - 2, by omega⟩).val % 2 = 0) := by
      constructor
      · intro h
        refine ⟨fun i => ?_, ?_⟩
        · have := h ⟨(i : ℕ), by omega⟩
          rw [hgg_w i, hdPhiS_i i] at this; exact this
        · have := h ⟨k - 1, by omega⟩
          rw [hgg_k1, show (dPhi hk eS ⟨k - 1, by omega⟩ : ℕ) = 1 from hdPhiS_last] at this
          omega
      · rintro ⟨hw, htag⟩ ℓ
        by_cases hℓ : (ℓ : ℕ) < k - 1
        · have hℓi : ℓ = ⟨(ℓ : ℕ), by omega⟩ := Fin.ext rfl
          have hwlt := hw ⟨(ℓ : ℕ), by omega⟩
          rw [← hgg_w ⟨(ℓ : ℕ), by omega⟩, ← hdPhiS_i ⟨(ℓ : ℕ), by omega⟩] at hwlt
          convert hwlt using 2
        · have hval : (ℓ : ℕ) = k - 1 := by have := ℓ.isLt; omega
          have hℓi : ℓ = ⟨k - 1, by omega⟩ := Fin.ext hval
          rw [hℓi, hgg_k1, show (dPhi hk eS ⟨k - 1, by omega⟩ : ℕ) = 1 from hdPhiS_last, htag]
          norm_num
    -- T-block equivalence.
    have hTblock : (∀ ℓ : Fin k, (dPhi hk eS ℓ : ℕ) ≤ (gg ℓ).val) ↔
        ((∀ i : Fin (k - 1), (eS i : ℕ) ≤ (w i).val) ∧
          (jdx ⟨k - 2, by omega⟩).val % 2 = 1) := by
      constructor
      · intro h
        refine ⟨fun i => ?_, ?_⟩
        · have := h ⟨(i : ℕ), by omega⟩
          rw [hgg_w i, hdPhiS_i i] at this; exact this
        · have := h ⟨k - 1, by omega⟩
          rw [hgg_k1, show (dPhi hk eS ⟨k - 1, by omega⟩ : ℕ) = 1 from hdPhiS_last] at this
          have hmod : (jdx ⟨k - 2, by omega⟩).val % 2 < 2 := Nat.mod_lt _ (by norm_num)
          omega
      · rintro ⟨hw, htag⟩ ℓ
        by_cases hℓ : (ℓ : ℕ) < k - 1
        · have hℓi : ℓ = ⟨(ℓ : ℕ), by omega⟩ := Fin.ext rfl
          have hwle := hw ⟨(ℓ : ℕ), by omega⟩
          rw [← hgg_w ⟨(ℓ : ℕ), by omega⟩, ← hdPhiS_i ⟨(ℓ : ℕ), by omega⟩] at hwle
          convert hwle using 2
        · have hval : (ℓ : ℕ) = k - 1 := by have := ℓ.isLt; omega
          have hℓi : ℓ = ⟨k - 1, by omega⟩ := Fin.ext hval
          rw [hℓi, hgg_k1, show (dPhi hk eS ⟨k - 1, by omega⟩ : ℕ) = 1 from hdPhiS_last, htag]
    -- Now evaluate both direct sums by block and match.
    rw [directSumTensor_apply_block (F := F) (phiMap (F := F) hk S) (phiMap (F := F) hk T) gg,
      directSumTensor_apply_block (F := F) S T w]
    -- Block condition for `φS⊕φT gg` is over `dPhi eS`; for `S⊕T w` over `eS`.
    by_cases hwS : ∀ i : Fin (k - 1), (w i).val < (eS i : ℕ)
    · -- `w` in `S`-block.
      have htagval : (if (∀ i : Fin (k - 1), (w i).val < (eS i : ℕ)) then (0 : ℕ) else 1) = 0 := by
        rw [if_pos hwS]
      rw [if_pos hwS]
      by_cases hggS : ∀ ℓ : Fin k, (gg ℓ).val < (dPhi hk eS ℓ : ℕ)
      · -- `gg` in `S`-block: tag = 0.
        have htag0 : (jdx ⟨k - 2, by omega⟩).val % 2 = 0 := (hSblock.mp hggS).2
        rw [dif_pos hggS, if_pos htag0, dif_pos hwS]
        -- Both pick the `S` block: `φS(restrict) = S(prune)` and `S w`.
        unfold phiMap
        apply congrArg S
        funext i
        apply Fin.ext
        have hi : (i : ℕ) < k - 1 := i.isLt
        simp only [Fin.val_cast]
        rw [hgg_w i]
      · -- `gg` not in `S`-block: contradiction with `w` in S-block and ... actually
        -- if `w` in S-block but `gg` not, tag = 1.  Then the `if` test fails (0 ≠ 1).
        rw [dif_neg hggS]
        have htag1 : (jdx ⟨k - 2, by omega⟩).val % 2 = 1 := by
          by_contra hne
          have hmod : (jdx ⟨k - 2, by omega⟩).val % 2 < 2 := Nat.mod_lt _ (by norm_num)
          have htag0 : (jdx ⟨k - 2, by omega⟩).val % 2 = 0 := by omega
          exact hggS (hSblock.mpr ⟨hwS, htag0⟩)
        rw [if_neg (by rw [htag1]; norm_num)]
        -- `gg` not S-block and `w` in S-block ⟹ `gg` not T-block either (legs `<k-1` are
        -- in S-block), so `(φS⊕φT) gg = 0`.
        rw [dif_neg]
        intro hggT
        have := (hTblock.mp hggT).1 ⟨0, by omega⟩
        have hlt := hwS ⟨0, by omega⟩
        omega
    · -- `w` not in `S`-block.
      rw [if_neg hwS]
      have hggS_neg : ¬ ∀ ℓ : Fin k, (gg ℓ).val < (dPhi hk eS ℓ : ℕ) := by
        intro hggS
        exact hwS (hSblock.mp hggS).1
      rw [dif_neg hggS_neg]
      by_cases hwT : ∀ i : Fin (k - 1), (eS i : ℕ) ≤ (w i).val
      · -- `w` in `T`-block.
        by_cases hggT : ∀ ℓ : Fin k, (dPhi hk eS ℓ : ℕ) ≤ (gg ℓ).val
        · have htag1 : (jdx ⟨k - 2, by omega⟩).val % 2 = 1 := (hTblock.mp hggT).2
          rw [dif_pos hggT, if_pos htag1, dif_neg hwS, dif_pos hwT]
          unfold phiMap
          apply congrArg T
          funext i
          apply Fin.ext
          have hi : (i : ℕ) < k - 1 := i.isLt
          simp only [Fin.val_cast]
          rw [hgg_w i, hdPhiS_i i]
        · rw [dif_neg hggT]
          have htag0 : (jdx ⟨k - 2, by omega⟩).val % 2 = 0 := by
            by_contra hne
            have hmod : (jdx ⟨k - 2, by omega⟩).val % 2 < 2 := Nat.mod_lt _ (by norm_num)
            have htag1 : (jdx ⟨k - 2, by omega⟩).val % 2 = 1 := by omega
            exact hggT (hTblock.mpr ⟨hwT, htag1⟩)
          rw [if_neg (by rw [htag0]; norm_num)]
      · -- `w` in neither block: `(S⊕T) w = 0` and the `if` gives `0` too.
        rw [dif_neg hwT]
        by_cases hggT : ∀ ℓ : Fin k, (dPhi hk eS ℓ : ℕ) ≤ (gg ℓ).val
        · exact absurd (hTblock.mp hggT).1 hwT
        · rw [dif_neg hggT, dif_neg hwS, ite_self]
  -- ============ hL : γ(φS⊕φT) ∼ₜ (S⊕T) ============
  -- Format equality for legs `< k-2`; the merged leg `k-2` differs by the factor 2.
  set sval : ℕ := (eS ⟨k - 2, by omega⟩ : ℕ) with hsval
  -- The `(S⊕T)`-index `w0 jdx` decoded from an `eL`-index `jdx`.
  have hLeg_lt : ∀ (jdx : ∀ ℓ : Fin (k - 1), Fin (eL ℓ)) (ℓ : Fin (k - 1)),
      (ℓ : ℕ) < k - 2 → (jdx ℓ).val < ((eS ℓ + eT ℓ : ℕ+) : ℕ) := by
    intro jdx ℓ hℓ
    have h := (jdx ℓ).isLt
    have he : (eL ℓ : ℕ) = ((eS ℓ + eT ℓ : ℕ+) : ℕ) := by rw [heL_lt ℓ hℓ, PNat.add_coe]
    omega
  have hLeg_k2 : ∀ (jdx : ∀ ℓ : Fin (k - 1), Fin (eL ℓ)),
      (jdx ⟨k - 2, by omega⟩).val / 2
        < ((eS ⟨k - 2, by omega⟩ + eT ⟨k - 2, by omega⟩ : ℕ+) : ℕ) := by
    intro jdx
    have h : (jdx ⟨k - 2, by omega⟩).val < st2 * 2 := heL_last ▸ (jdx ⟨k - 2, by omega⟩).isLt
    rw [PNat.add_coe, ← hst2]
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
  let w0 : (∀ ℓ : Fin (k - 1), Fin (eL ℓ)) → ∀ i : Fin (k - 1), Fin ((eS i + eT i : ℕ+) : ℕ) :=
    fun jdx i =>
      if hi : (i : ℕ) < k - 2 then ⟨(jdx i).val, hLeg_lt jdx i hi⟩
      else ⟨(jdx ⟨k - 2, by omega⟩).val / 2, by
        have hival : (i : ℕ) = k - 2 := by have := i.isLt; omega
        have hii : i = ⟨k - 2, by omega⟩ := Fin.ext hival
        have hk2 := hLeg_k2 jdx
        have hdimeq : ((eS i + eT i : ℕ+) : ℕ)
            = ((eS ⟨k - 2, by omega⟩ + eT ⟨k - 2, by omega⟩ : ℕ+) : ℕ) := by
          simp only [hii]
        omega⟩
  have hw0_lt : ∀ (jdx : ∀ ℓ : Fin (k - 1), Fin (eL ℓ)) (ℓ : Fin (k - 1)),
      (ℓ : ℕ) < k - 2 → (w0 jdx ℓ).val = (jdx ℓ).val := by
    intro jdx ℓ hℓ; simp only [w0, dif_pos hℓ]
  have hw0_k2 : ∀ (jdx : ∀ ℓ : Fin (k - 1), Fin (eL ℓ)),
      (w0 jdx ⟨k - 2, by omega⟩).val = (jdx ⟨k - 2, by omega⟩).val / 2 := by
    intro jdx
    simp only [w0, dif_neg (show ¬ ((⟨k - 2, by omega⟩ : Fin (k - 1)) : ℕ) < k - 2 by simp)]
  have hL : RestrictsEquiv (F := F)
      (gammaMap (F := F) hk (phiMap (F := F) hk S ⊕ₜ phiMap (F := F) hk T)) (S ⊕ₜ T) := by
    constructor
    · -- Forward.
      refine ⟨fun ℓ a b =>
        if (ℓ : ℕ) < k - 2 then (if a.val = b.val then 1 else 0)
        else (if b.val = a.val / 2 ∧
            a.val % 2 = (if b.val < sval then 0 else 1) then 1 else 0), ?_⟩
      intro jdx
      rw [hLval jdx (w0 jdx)
        (fun ℓ hℓ => hw0_lt jdx ℓ hℓ) (hw0_k2 jdx)]
      rw [Finset.sum_eq_single (w0 jdx)]
      · -- Main term: product collapses to the leg-`(k-2)` tag gate.
        have hprodgate : (∏ i : Fin (k - 1),
            (if (i : ℕ) < k - 2 then (if (jdx i).val = (w0 jdx i).val then (1 : F) else 0)
              else (if (w0 jdx i).val = (jdx i).val / 2 ∧
                (jdx i).val % 2 = (if (w0 jdx i).val < sval then 0 else 1) then 1 else 0)))
              = (if (jdx ⟨k - 2, by omega⟩).val % 2
                  = (if (w0 jdx ⟨k - 2, by omega⟩).val < sval then 0 else 1)
                then (1 : F) else 0) := by
          rw [Finset.prod_eq_single (⟨k - 2, by omega⟩ : Fin (k - 1))]
          · rw [if_neg (show ¬ ((⟨k - 2, by omega⟩ : Fin (k - 1)) : ℕ) < k - 2 by simp), hw0_k2]
            simp only [true_and]
          · intro b _ hb
            have hbval : (b : ℕ) < k - 2 := by
              have := b.isLt
              have : (b : ℕ) ≠ k - 2 := fun h => hb (Fin.ext h)
              omega
            rw [if_pos hbval, hw0_lt jdx b hbval, if_pos rfl]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hprodgate]
        by_cases hz : (S ⊕ₜ T) (w0 jdx) = 0
        · rw [hz, mul_zero, ite_self]
        · have hsv : sval = (eS ⟨k - 2, by omega⟩ : ℕ) := hsval
          -- Nonzero value ⟹ `w0 jdx` is a pure block (all-`S` or all-`T`).
          have hdich : (∀ i : Fin (k - 1), (w0 jdx i).val < (eS i : ℕ)) ∨
              (∀ i : Fin (k - 1), (eS i : ℕ) ≤ (w0 jdx i).val) := by
            by_contra hcon
            push_neg at hcon
            obtain ⟨⟨iS, hiS⟩, ⟨iT, hiT⟩⟩ := hcon
            apply hz
            rw [directSumTensor_apply_block (F := F) S T (w0 jdx)]
            rw [dif_neg (by push_neg; exact ⟨iS, hiS⟩), dif_neg (by push_neg; exact ⟨iT, by omega⟩)]
          -- The all-`S` gate agrees with the single leg-`(k-2)` matrix gate.
          have hgate : (if (∀ i : Fin (k - 1), (w0 jdx i).val < (eS i : ℕ)) then (0 : ℕ) else 1)
              = (if (w0 jdx ⟨k - 2, by omega⟩).val < sval then (0 : ℕ) else 1) := by
            rcases hdich with hS | hT
            · rw [if_pos hS, if_pos (by rw [hsv]; exact hS ⟨k - 2, by omega⟩)]
            · have hk2 := hT ⟨k - 2, by omega⟩
              rw [if_neg (by intro hall; have := hall ⟨k - 2, by omega⟩; omega),
                if_neg (by rw [hsv]; omega)]
          rw [hgate]
          by_cases hcond : (jdx ⟨k - 2, by omega⟩).val % 2
              = (if (w0 jdx ⟨k - 2, by omega⟩).val < sval then (0 : ℕ) else 1)
          · rw [if_pos hcond, if_pos hcond, one_mul]
          · rw [if_neg hcond, if_neg hcond, zero_mul]
      · -- Off-diagonal: any `b ≠ w0 jdx` kills the product.
        intro b _ hbne
        have hex : ∃ i : Fin (k - 1), (b i).val ≠ (w0 jdx i).val := by
          by_contra hcon
          push_neg at hcon
          exact hbne (funext fun i => Fin.ext (hcon i))
        obtain ⟨i, hi⟩ := hex
        have hfac : (if (i : ℕ) < k - 2 then (if (jdx i).val = (b i).val then (1 : F) else 0)
            else (if (b i).val = (jdx i).val / 2 ∧
              (jdx i).val % 2 = (if (b i).val < sval then 0 else 1) then 1 else 0)) = 0 := by
          by_cases hik : (i : ℕ) < k - 2
          · rw [if_pos hik, if_neg (by rw [← hw0_lt jdx i hik]; exact fun h => hi h.symm)]
          · rw [if_neg hik]
            have hival : (i : ℕ) = k - 2 := by have := i.isLt; omega
            have hii : i = ⟨k - 2, by omega⟩ := Fin.ext hival
            rw [if_neg]
            rintro ⟨hb1, _⟩
            apply hi
            rw [hb1, hii, hw0_k2]
        rw [Finset.prod_eq_zero (Finset.mem_univ i) hfac, zero_mul]
      · -- Membership.
        intro h; exact absurd (Finset.mem_univ _) h
    · -- Reverse: `(S⊕T) ≤ γ(φS⊕φT)` via the block-embedding leg matrix.
      refine ⟨fun i a b =>
        if (i : ℕ) < k - 2 then (if a.val = b.val then 1 else 0)
        else (if b.val = 2 * a.val + (if a.val < sval then 0 else 1) then 1 else 0), ?_⟩
      intro idx
      have hfmtL : ∀ ℓ : Fin (k - 1), (ℓ : ℕ) < k - 2 →
          ((eS ℓ + eT ℓ : ℕ+) : ℕ) = (eL ℓ : ℕ) := by
        intro ℓ hℓ; rw [heL_lt ℓ hℓ, PNat.add_coe]
      -- Embedded `eL`-index `jL idx`: legs `< k-2` pass through, leg `k-2` is
      -- `2 * idx⟨k-2⟩ + blockTag`, where `blockTag` records the direct-sum block.
      -- The value and bound are split into named facts so that unfolding `jL`
      -- never needs to reconstruct anonymous `let`-body proof terms.
      set jLval : Fin (k - 1) → ℕ := fun ℓ =>
        if (ℓ : ℕ) < k - 2 then (idx ℓ).val
        else 2 * (idx ⟨k - 2, by omega⟩).val
          + (if (idx ⟨k - 2, by omega⟩).val < sval then 0 else 1) with hjLval
      have hjLval_lt : ∀ ℓ : Fin (k - 1), (ℓ : ℕ) < k - 2 → jLval ℓ = (idx ℓ).val := by
        intro ℓ hℓ; simp only [hjLval, if_pos hℓ]
      have hjLval_k2 : jLval ⟨k - 2, by omega⟩ = 2 * (idx ⟨k - 2, by omega⟩).val
          + (if (idx ⟨k - 2, by omega⟩).val < sval then 0 else 1) := by
        simp only [hjLval, if_neg (show ¬ ((⟨k - 2, by omega⟩ : Fin (k - 1)) : ℕ) < k - 2 by simp)]
      have hjLbound : ∀ ℓ : Fin (k - 1), jLval ℓ < (eL ℓ : ℕ) := by
        intro ℓ
        by_cases hℓ : (ℓ : ℕ) < k - 2
        · rw [hjLval_lt ℓ hℓ, ← hfmtL ℓ hℓ]; exact (idx ℓ).isLt
        · have hval : (ℓ : ℕ) = k - 2 := by have := ℓ.isLt; omega
          have hii : ℓ = ⟨k - 2, by omega⟩ := Fin.ext hval
          have hb : (idx ⟨k - 2, by omega⟩).val
              < ((eS ⟨k - 2, by omega⟩ + eT ⟨k - 2, by omega⟩ : ℕ+) : ℕ) :=
            (idx ⟨k - 2, by omega⟩).isLt
          have he : ((eS ⟨k - 2, by omega⟩ + eT ⟨k - 2, by omega⟩ : ℕ+) : ℕ) = st2 := by
            rw [PNat.add_coe, ← hst2]
          rw [hii, hjLval_k2, heL_last]
          split <;> omega
      let jL : ∀ ℓ : Fin (k - 1), Fin (eL ℓ) := fun ℓ => ⟨jLval ℓ, hjLbound ℓ⟩
      have hjL_lt : ∀ ℓ : Fin (k - 1), (ℓ : ℕ) < k - 2 → (jL ℓ).val = (idx ℓ).val := by
        intro ℓ hℓ; exact hjLval_lt ℓ hℓ
      have hjL_k2 : (jL ⟨k - 2, by omega⟩).val = 2 * (idx ⟨k - 2, by omega⟩).val
          + (if (idx ⟨k - 2, by omega⟩).val < sval then 0 else 1) := hjLval_k2
      -- `w0 (jL idx) = idx`.
      have hw0jL : ∀ i : Fin (k - 1), (w0 jL i).val = (idx i).val := by
        intro i
        by_cases hi : (i : ℕ) < k - 2
        · rw [hw0_lt jL i hi, hjL_lt i hi]
        · have hival : (i : ℕ) = k - 2 := by have := i.isLt; omega
          have hii : i = ⟨k - 2, by omega⟩ := Fin.ext hival
          rw [hii, hw0_k2, hjL_k2]
          split <;> omega
      -- Parity of leg `k-2` of `jL` is the block tag.
      have htagpar : (jL ⟨k - 2, by omega⟩).val % 2
          = (if (idx ⟨k - 2, by omega⟩).val < sval then 0 else 1) := by
        rw [hjL_k2]; split <;> omega
      rw [Finset.sum_eq_single jL]
      · -- Main term: product is 1, `gammaMap jL = (S⊕T) idx`.
        have hprod : (∏ i : Fin (k - 1),
            (if (i : ℕ) < k - 2 then (if (idx i).val = (jL i).val then (1 : F) else 0)
              else (if (jL i).val = 2 * (idx i).val
                + (if (idx i).val < sval then 0 else 1) then 1 else 0))) = 1 := by
          apply Finset.prod_eq_one
          intro i _
          by_cases hi : (i : ℕ) < k - 2
          · rw [if_pos hi, hjL_lt i hi, if_pos rfl]
          · have hival : (i : ℕ) = k - 2 := by have := i.isLt; omega
            have hii : i = ⟨k - 2, by omega⟩ := Fin.ext hival
            rw [if_neg hi, if_pos (by rw [hii, hjL_k2])]
        rw [hprod, one_mul]
        rw [hLval jL (w0 jL) (fun ℓ hℓ => by rw [hw0jL ℓ, ← hjL_lt ℓ hℓ])
          (by rw [hw0_k2 jL])]
        rw [htagpar]
        -- `w0 jL = idx` as a function.
        have hw0jL_eq : w0 jL = idx := funext fun i => Fin.ext (hw0jL i)
        rw [hw0jL_eq]
        by_cases hz : (S ⊕ₜ T) idx = 0
        · rw [hz, ite_self]
        · have hsv : sval = (eS ⟨k - 2, by omega⟩ : ℕ) := hsval
          have hdich : (∀ i : Fin (k - 1), (idx i).val < (eS i : ℕ)) ∨
              (∀ i : Fin (k - 1), (eS i : ℕ) ≤ (idx i).val) := by
            by_contra hcon
            push_neg at hcon
            obtain ⟨⟨iS, hiS⟩, ⟨iT, hiT⟩⟩ := hcon
            apply hz
            rw [directSumTensor_apply_block (F := F) S T idx]
            rw [dif_neg (by push_neg; exact ⟨iS, hiS⟩), dif_neg (by push_neg; exact ⟨iT, by omega⟩)]
          have hgate : (if (idx ⟨k - 2, by omega⟩).val < sval then (0 : ℕ) else 1)
              = (if (∀ i : Fin (k - 1), (idx i).val < (eS i : ℕ)) then (0 : ℕ) else 1) := by
            rcases hdich with hS | hT
            · rw [if_pos hS, if_pos (by rw [hsv]; exact hS ⟨k - 2, by omega⟩)]
            · have hk2 := hT ⟨k - 2, by omega⟩
              rw [if_neg (by rw [hsv]; omega),
                if_neg (by intro hall; have := hall ⟨k - 2, by omega⟩; omega)]
          rw [hgate, if_pos rfl]
      · -- Off-diagonal: any `jdx ≠ jL` kills the product.
        intro jdx _ hjne
        have hex : ∃ i : Fin (k - 1), (jL i).val ≠ (jdx i).val := by
          by_contra hcon
          push_neg at hcon
          exact hjne (funext fun i => Fin.ext (hcon i)).symm
        obtain ⟨i, hi⟩ := hex
        have hfac : (if (i : ℕ) < k - 2 then (if (idx i).val = (jdx i).val then (1 : F) else 0)
            else (if (jdx i).val = 2 * (idx i).val
              + (if (idx i).val < sval then 0 else 1) then 1 else 0)) = 0 := by
          by_cases hik : (i : ℕ) < k - 2
          · rw [if_pos hik, if_neg (by rw [← hjL_lt i hik]; exact hi)]
          · have hival : (i : ℕ) = k - 2 := by have := i.isLt; omega
            have hii : i = ⟨k - 2, by omega⟩ := Fin.ext hival
            rw [if_neg hik, if_neg (by
              intro hjdxeq
              apply hi
              rw [hii, hjL_k2] at *
              rw [hjdxeq])]
        rw [Finset.prod_eq_zero (Finset.mem_univ i) hfac, zero_mul]
      · -- Membership.
        intro h; exact absurd (Finset.mem_univ _) h
  -- Combine: `γ(φS⊕φT) ∼ (S⊕T) ∼ γ(φ(S⊕T))`.
  exact ⟨hL.1.trans hR.2, hR.1.trans hL.2⟩

lemma gamma_phi_add_equiv {k : ℕ} (hk : 3 ≤ k) {eS eT : Fin (k - 1) → ℕ+}
    (S : KTensor F eS) (T : KTensor F eT) :
    gammaMap (F := F) hk (phiMap (F := F) hk S ⊕ₜ phiMap (F := F) hk T) ∼ₜ
      gammaMap (F := F) hk (phiMap (F := F) hk (S ⊕ₜ T)) := by
  exact gamma_phi_add_equiv_witness (F := F) hk S T

/-- Decoded coordinate of a `γ(⟨r⟩)`-index on leg `i : Fin k` (paper tex:1042):
legs `< k-2` pass through, the merged last leg splits via `divNat`/`modNat`. -/
private def rUnitCoord {k : ℕ} (hk : 3 ≤ k) (r : ℕ+)
    (idx : ∀ ℓ : Fin (k - 1), Fin (dGamma hk (fun _ : Fin k => r) ℓ)) (i : Fin k) : ℕ :=
  if h : (i : ℕ) < k - 2 then (idx ⟨i, by omega⟩).val
  else if (i : ℕ) = k - 2 then (idx ⟨k - 2, by omega⟩).val / (r : ℕ)
  else (idx ⟨k - 2, by omega⟩).val % (r : ℕ)

/-- Value of `γ(⟨r⟩)` as an indicator on the decoded coordinates (paper tex:1042). -/
private lemma gammaUnit_eq_allEq {k : ℕ} (hk : 3 ≤ k) (r : ℕ+)
    (idx : ∀ ℓ : Fin (k - 1), Fin (dGamma hk (fun _ : Fin k => r) ℓ)) :
    gammaMap (F := F) hk (unitTensor (F := F) (k := k) r) idx =
      (if (∀ i j : Fin k, rUnitCoord hk r idx i = rUnitCoord hk r idx j) then (1 : F) else 0) := by
  classical
  simp only [gammaMap, unitTensor]
  congr 1
  apply propext
  simp only [Fin.ext_iff, rUnitCoord, finProdFinEquiv_symm_apply, Fin.coe_divNat,
    Fin.coe_modNat, Fin.val_cast, apply_dite Fin.val, dite_eq_ite]

/-- Decoded coordinate of a `γ(φ(⟨r⟩))`-index on leg `i : Fin (k-1)` (paper tex:1042):
legs `< k-2` pass through; the merged last leg (dimension `r*1`) splits via `divNat`
with divisor `1`, hence equals the raw value. -/
private def lUnitCoord {k : ℕ} (hk : 3 ≤ k) (r : ℕ+)
    (jdx : ∀ ℓ : Fin (k - 1), Fin (dGamma hk (dPhi hk (fun _ : Fin (k - 1) => r)) ℓ))
    (i : Fin (k - 1)) : ℕ :=
  if (i : ℕ) < k - 2 then (jdx ⟨i, by omega⟩).val
  else if (i : ℕ) = k - 2 then (jdx ⟨k - 2, by omega⟩).val / (1 : ℕ)
  else (jdx ⟨k - 2, by omega⟩).val % (1 : ℕ)

-- `dif_neg` simp arg below forces dependent `if`-branch reduction (dite→ite) and
-- is load-bearing despite the unusedSimpArgs linter flagging it.
set_option linter.unusedSimpArgs false in
/-- Value of `γ(φ(⟨r⟩))` as an indicator on the decoded coordinates (paper tex:1042). -/
private lemma gammaPhiUnit_eq_allEq {k : ℕ} (hk : 3 ≤ k) (r : ℕ+)
    (jdx : ∀ ℓ : Fin (k - 1), Fin (dGamma hk (dPhi hk (fun _ : Fin (k - 1) => r)) ℓ)) :
    gammaMap (F := F) hk (phiMap (F := F) hk (unitTensor (F := F) (k := k - 1) r)) jdx =
      (if (∀ i j : Fin (k - 1), lUnitCoord hk r jdx i = lUnitCoord hk r jdx j) then (1 : F)
        else 0) := by
  classical
  simp only [gammaMap, phiMap, unitTensor]
  congr 1
  apply propext
  simp only [Fin.ext_iff, lUnitCoord, finProdFinEquiv_symm_apply, Fin.coe_divNat,
    Fin.coe_modNat, Fin.val_cast, apply_dite Fin.val, dite_eq_ite, dPhi, lt_irrefl,
    dif_neg, if_false, PNat.one_coe]
  rfl

private lemma gamma_phi_unit_diagonal_restriction_helper {k : ℕ} (hk : 3 ≤ k) (r : ℕ+) :
    gammaMap (F := F) hk
        (phiMap (F := F) hk (unitTensor (F := F) (k := k - 1) r)) ∼ₜ
      gammaMap (F := F) hk (unitTensor (F := F) (k := k) r) := by
  -- Paper tex:1042 diagonal restriction step.  The forward last-leg matrix is
  -- `Fin r → Fin (r*r)`, `i ↦ finProdFinEquiv (i, i)`, and the reverse matrix
  -- is its transpose; identity/cast matrices are used on all earlier legs.
  classical
  -- Abbreviations for the two formats.
  -- LHS format `eL ℓ`: legs `< k-2` are `r`, last leg is `r*1`.
  -- RHS format `eR ℓ`: legs `< k-2` are `r`, last leg is `r*r`.
  set eL : Fin (k - 1) → ℕ+ := dGamma hk (dPhi hk (fun _ : Fin (k - 1) => r)) with heL
  set eR : Fin (k - 1) → ℕ+ := dGamma hk (fun _ : Fin k => r) with heR
  -- The diagonal index assignment: `eL`-index `jdx` lifts to the `eR`-index that
  -- agrees on legs `< k-2` and stores `(a, a)` on the last leg, where
  -- `a = (jdx last).val`.
  have hlast_lt : ∀ (jdx : ∀ ℓ : Fin (k - 1), Fin (eL ℓ)),
      (jdx ⟨k - 2, by omega⟩).val < (r : ℕ) := by
    intro jdx
    have h := (jdx ⟨k - 2, by omega⟩).isLt
    have hdim : (eL ⟨k - 2, by omega⟩ : ℕ) = (r : ℕ) := by
      simp only [heL, dGamma, dPhi]
      rw [dif_neg (show ¬ ((⟨k - 2, by omega⟩ : Fin (k - 1)) : ℕ) < k - 2 by simp),
        dif_pos (show k - 2 < k - 1 by omega),
        dif_neg (show ¬ k - 1 < k - 1 by omega), PNat.mul_coe,
        PNat.one_coe, Nat.mul_one]
    omega
  constructor
  · -- Forward: `LHS ≤ RHS` via the diagonal last-leg matrix.
    refine ⟨fun ℓ a b =>
        if (ℓ : ℕ) < k - 2 then (if a.val = b.val then 1 else 0)
        else (if b.val = a.val + r * a.val then 1 else 0), ?_⟩
    intro jdx
    -- The diagonal lift of `jdx`.
    have heRlast : (eR ⟨k - 2, by omega⟩ : ℕ) = (r : ℕ) * (r : ℕ) := by
      simp only [heR, dGamma]
      have h1 : ¬ ((⟨k - 2, by omega⟩ : Fin (k - 1)) : ℕ) < k - 2 := by simp
      simp only [dif_neg h1, PNat.mul_coe]
    have heReq : ∀ ℓ : Fin (k - 1), (ℓ : ℕ) < k - 2 → (eR ℓ : ℕ) = (r : ℕ) := by
      intro ℓ hℓ
      simp only [heR, dGamma, dif_pos hℓ]
    have heLeq : ∀ ℓ : Fin (k - 1), (ℓ : ℕ) < k - 2 → (eL ℓ : ℕ) = (r : ℕ) := by
      intro ℓ hℓ
      have hℓ' : (ℓ : ℕ) < k - 1 := by omega
      simp only [heL, dGamma, dPhi, dif_pos hℓ, dif_pos hℓ']
    set a : ℕ := (jdx ⟨k - 2, by omega⟩).val with ha
    have ha_lt : a < (r : ℕ) := hlast_lt jdx
    have hdiag_lt : a + r * a < (eR ⟨k - 2, by omega⟩ : ℕ) := by
      rw [heRlast]; nlinarith [ha_lt, r.pos]
    let idx0 : ∀ ℓ : Fin (k - 1), Fin (eR ℓ) := fun ℓ =>
      if hℓ : (ℓ : ℕ) < k - 2 then
        Fin.cast (by rw [heReq ℓ hℓ, ← heLeq ℓ hℓ]) (jdx ℓ)
      else
        ⟨a + r * a, by
          have hℓ2 : ¬ (ℓ : ℕ) < k - 2 := hℓ
          have hval : (ℓ : ℕ) = k - 2 := by have := ℓ.isLt; omega
          have : ℓ = ⟨k - 2, by omega⟩ := Fin.ext hval
          rw [this]; exact hdiag_lt⟩
    -- Helper: `idx0 ℓ` value on each leg.
    have hidx0_lt : ∀ ℓ : Fin (k - 1), (ℓ : ℕ) < k - 2 →
        (idx0 ℓ).val = (jdx ℓ).val := by
      intro ℓ hℓ; simp only [idx0, dif_pos hℓ, Fin.val_cast]
    have hidx0_last : (idx0 ⟨k - 2, by omega⟩).val = a + r * a := by
      have hnot : ¬ ((⟨k - 2, by omega⟩ : Fin (k - 1)) : ℕ) < k - 2 := by simp
      simp only [idx0, dif_neg hnot]
    rw [Finset.sum_eq_single idx0]
    · -- The product over legs is `1`.
      have hprod : (∏ i : Fin (k - 1),
          (if (i : ℕ) < k - 2 then (if (jdx i).val = (idx0 i).val then (1 : F) else 0)
            else (if (idx0 i).val = (jdx i).val + r * (jdx i).val then 1 else 0))) = 1 := by
        apply Finset.prod_eq_one
        intro i _
        by_cases hi : (i : ℕ) < k - 2
        · rw [if_pos hi, hidx0_lt i hi, if_pos rfl]
        · rw [if_neg hi]
          have hival : (i : ℕ) = k - 2 := by have := i.isLt; omega
          have hi_eq : i = ⟨k - 2, by omega⟩ := Fin.ext hival
          rw [if_pos]
          rw [hi_eq, hidx0_last]
      rw [hprod, one_mul]
      -- Now both sides are indicator `if`s; show the conditions agree.
      rw [gammaPhiUnit_eq_allEq (F := F) hk r jdx,
          gammaUnit_eq_allEq (F := F) hk r idx0]
      -- Arithmetic facts for the diagonal store `a + r*a`.
      have hdiv : (a + r * a) / (r : ℕ) = a := by
        rw [Nat.add_mul_div_left _ _ r.pos, Nat.div_eq_of_lt ha_lt, zero_add]
      have hmod : (a + r * a) % (r : ℕ) = a := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha_lt]
      -- Per-coordinate values of `rUnitCoord idx0`.
      have hRval : ∀ ℓ : Fin k, (hℓ : (ℓ : ℕ) < k - 2) →
          rUnitCoord hk r idx0 ℓ = (jdx ⟨ℓ, by omega⟩).val := by
        intro ℓ hℓ
        simp only [rUnitCoord, dif_pos hℓ]
        exact hidx0_lt ⟨ℓ, by omega⟩ hℓ
      have hRval_k2 : rUnitCoord hk r idx0 ⟨k - 2, by omega⟩ = a := by
        simp only [rUnitCoord, dif_neg (show ¬ (k - 2 : ℕ) < k - 2 by omega), if_true]
        rw [hidx0_last, hdiv]
      have hRval_k1 : rUnitCoord hk r idx0 ⟨k - 1, by omega⟩ = a := by
        simp only [rUnitCoord, dif_neg (show ¬ (k - 1 : ℕ) < k - 2 by omega),
          if_neg (show ¬ (k - 1 : ℕ) = k - 2 by omega)]
        rw [hidx0_last, hmod]
      -- Per-coordinate values of `lUnitCoord jdx`.
      have hLval : ∀ ℓ : Fin (k - 1), (hℓ : (ℓ : ℕ) < k - 2) →
          lUnitCoord hk r jdx ℓ = (jdx ℓ).val := by
        intro ℓ hℓ; simp only [lUnitCoord, if_pos hℓ]
      have hLval_k2 : lUnitCoord hk r jdx ⟨k - 2, by omega⟩ = a := by
        simp only [lUnitCoord, if_neg (show ¬ (k - 2 : ℕ) < k - 2 by omega), if_true,
          Nat.div_one]
        exact ha.symm
      -- `rUnitCoord idx0` and `lUnitCoord jdx` each constant iff all `jdx`-legs equal `a`.
      have hRiff : (∀ i j : Fin k, rUnitCoord hk r idx0 i = rUnitCoord hk r idx0 j) ↔
          (∀ i : Fin (k - 1), (jdx i).val = a) := by
        constructor
        · intro h i
          have hi2 : (i : ℕ) < k - 2 ∨ (i : ℕ) = k - 2 := by have := i.isLt; omega
          rcases hi2 with hlt | heq
          · have key := h ⟨i.val, by omega⟩ ⟨k - 1, by omega⟩
            rw [hRval ⟨i.val, by omega⟩ hlt, hRval_k1] at key
            have hi : (⟨i.val, by omega⟩ : Fin (k - 1)) = i := rfl
            rw [hi] at key; exact key
          · have hii : i = ⟨k - 2, by omega⟩ := Fin.ext heq
            rw [hii, ha]
        · intro h i j
          have hcoord : ∀ ℓ : Fin k, rUnitCoord hk r idx0 ℓ = a := by
            intro ℓ
            rcases (by have := ℓ.isLt; omega :
                (ℓ : ℕ) < k - 2 ∨ (ℓ : ℕ) = k - 2 ∨ (ℓ : ℕ) = k - 1) with hlt | heq | heq
            · rw [hRval ℓ hlt]; exact h _
            · have : ℓ = ⟨k - 2, by omega⟩ := Fin.ext heq
              rw [this, hRval_k2]
            · have : ℓ = ⟨k - 1, by omega⟩ := Fin.ext heq
              rw [this, hRval_k1]
          rw [hcoord i, hcoord j]
      have hLiff : (∀ i j : Fin (k - 1), lUnitCoord hk r jdx i = lUnitCoord hk r jdx j) ↔
          (∀ i : Fin (k - 1), (jdx i).val = a) := by
        constructor
        · intro h i
          have hi2 : (i : ℕ) < k - 2 ∨ (i : ℕ) = k - 2 := by have := i.isLt; omega
          rcases hi2 with hlt | heq
          · have key := h i ⟨k - 2, by omega⟩
            rw [hLval i hlt, hLval_k2] at key; exact key
          · have hii : i = ⟨k - 2, by omega⟩ := Fin.ext heq
            rw [hii, ha]
        · intro h i j
          have hcoord : ∀ ℓ : Fin (k - 1), lUnitCoord hk r jdx ℓ = a := by
            intro ℓ
            rcases (by have := ℓ.isLt; omega : (ℓ : ℕ) < k - 2 ∨ (ℓ : ℕ) = k - 2) with hlt | heq
            · rw [hLval ℓ hlt]; exact h _
            · have : ℓ = ⟨k - 2, by omega⟩ := Fin.ext heq
              rw [this, hLval_k2]
          rw [hcoord i, hcoord j]
      congr 1
      apply propext
      rw [hLiff, hRiff]
    · -- Off-diagonal indices contribute `0`.
      intro idx _ hidx
      -- Find a leg where `idx` and `idx0` differ.
      have hne : ∃ ℓ : Fin (k - 1), (idx ℓ).val ≠ (idx0 ℓ).val := by
        by_contra h
        push_neg at h
        exact hidx (funext fun ℓ => Fin.ext (h ℓ))
      obtain ⟨ℓ, hℓ⟩ := hne
      apply mul_eq_zero_of_left
      apply Finset.prod_eq_zero (Finset.mem_univ ℓ)
      by_cases hlt : (ℓ : ℕ) < k - 2
      · simp only [if_pos hlt]
        rw [if_neg]
        rw [hidx0_lt ℓ hlt] at hℓ
        exact fun h => hℓ h.symm
      · have hℓ_val : (ℓ : ℕ) = k - 2 := by have := ℓ.isLt; omega
        have hℓ_eq : ℓ = ⟨k - 2, by omega⟩ := Fin.ext hℓ_val
        simp only [if_neg hlt]
        rw [hℓ_eq, hidx0_last] at hℓ
        rw [hℓ_eq, if_neg]
        intro h
        exact hℓ h
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  · -- Reverse: `RHS ≤ LHS` via the transpose diagonal last-leg matrix.
    refine ⟨fun ℓ a b =>
        if (ℓ : ℕ) < k - 2 then (if a.val = b.val then 1 else 0)
        else (if a.val = b.val + r * b.val then 1 else 0), ?_⟩
    intro jdx
    -- Format facts.
    have heRlast : (eR ⟨k - 2, by omega⟩ : ℕ) = (r : ℕ) * (r : ℕ) := by
      simp only [heR, dGamma]
      rw [dif_neg (show ¬ ((⟨k - 2, by omega⟩ : Fin (k - 1)) : ℕ) < k - 2 by simp), PNat.mul_coe]
    have heLlast : (eL ⟨k - 2, by omega⟩ : ℕ) = (r : ℕ) := by
      simp only [heL, dGamma, dPhi]
      rw [dif_neg (show ¬ ((⟨k - 2, by omega⟩ : Fin (k - 1)) : ℕ) < k - 2 by simp),
        dif_pos (show k - 2 < k - 1 by omega),
        dif_neg (show ¬ k - 1 < k - 1 by omega), PNat.mul_coe,
        PNat.one_coe, Nat.mul_one]
    have heReq : ∀ ℓ : Fin (k - 1), (ℓ : ℕ) < k - 2 → (eR ℓ : ℕ) = (r : ℕ) := by
      intro ℓ hℓ; simp only [heR, dGamma, dif_pos hℓ]
    have heLeq : ∀ ℓ : Fin (k - 1), (ℓ : ℕ) < k - 2 → (eL ℓ : ℕ) = (r : ℕ) := by
      intro ℓ hℓ
      have hℓ' : (ℓ : ℕ) < k - 1 := by omega
      simp only [heL, dGamma, dPhi, dif_pos hℓ, dif_pos hℓ']
    -- The split coordinate stored in `jdx`'s last leg.
    set c : ℕ := (jdx ⟨k - 2, by omega⟩).val % (r : ℕ) with hc
    have hr_pos : 0 < (r : ℕ) := r.pos
    have hc_lt : c < (r : ℕ) := Nat.mod_lt _ hr_pos
    -- The candidate `LHS`-index: legs `< k-2` copy `jdx`, last leg stores `c`.
    have hc_lt' : c < (eL ⟨k - 2, by omega⟩ : ℕ) := by rw [heLlast]; exact hc_lt
    let idx0 : ∀ ℓ : Fin (k - 1), Fin (eL ℓ) := fun ℓ =>
      if hℓ : (ℓ : ℕ) < k - 2 then
        Fin.cast (by rw [heLeq ℓ hℓ, ← heReq ℓ hℓ]) (jdx ℓ)
      else
        ⟨c, by
          have hℓ2 : ¬ (ℓ : ℕ) < k - 2 := hℓ
          have hval : (ℓ : ℕ) = k - 2 := by have := ℓ.isLt; omega
          have : ℓ = ⟨k - 2, by omega⟩ := Fin.ext hval
          rw [this]; exact hc_lt'⟩
    have hidx0_lt : ∀ ℓ : Fin (k - 1), (ℓ : ℕ) < k - 2 →
        (idx0 ℓ).val = (jdx ℓ).val := by
      intro ℓ hℓ; simp only [idx0, dif_pos hℓ, Fin.val_cast]
    have hidx0_last : (idx0 ⟨k - 2, by omega⟩).val = c := by
      simp only [idx0, dif_neg (show ¬ ((⟨k - 2, by omega⟩ : Fin (k - 1)) : ℕ) < k - 2 by simp)]
    -- Rewrite both sides as indicators.
    rw [gammaUnit_eq_allEq (F := F) hk r jdx]
    by_cases hdiag : (∀ i j : Fin k, rUnitCoord hk r jdx i = rUnitCoord hk r jdx j)
    · -- `jdx` is on the diagonal: the unique contributing index is `idx0`.
      rw [if_pos hdiag]
      -- From `hdiag`, the merged last leg satisfies `divNat = modNat = c`.
      have hdivmod : (jdx ⟨k - 2, by omega⟩).val / (r : ℕ) = c := by
        have := hdiag ⟨k - 2, by omega⟩ ⟨k - 1, by omega⟩
        simp only [rUnitCoord, dif_neg (show ¬ (k - 2 : ℕ) < k - 2 by omega), if_true,
          dif_neg (show ¬ (k - 1 : ℕ) < k - 2 by omega),
          if_neg (show ¬ (k - 1 : ℕ) = k - 2 by omega)] at this
        rw [hc]; exact this
      have hjdx_last : (jdx ⟨k - 2, by omega⟩).val = c + r * c := by
        conv_lhs => rw [← Nat.div_add_mod (jdx ⟨k - 2, by omega⟩).val (r : ℕ)]
        rw [hdivmod, ← hc, Nat.mul_comm, Nat.add_comm]
      rw [Finset.sum_eq_single idx0]
      · -- product = 1.
        have hprod : (∏ i : Fin (k - 1),
            (if (i : ℕ) < k - 2 then (if (jdx i).val = (idx0 i).val then (1 : F) else 0)
              else (if (jdx i).val = (idx0 i).val + r * (idx0 i).val then 1 else 0))) = 1 := by
          apply Finset.prod_eq_one
          intro i _
          by_cases hi : (i : ℕ) < k - 2
          · rw [if_pos hi, hidx0_lt i hi, if_pos rfl]
          · have hival : (i : ℕ) = k - 2 := by have := i.isLt; omega
            have hi_eq : i = ⟨k - 2, by omega⟩ := Fin.ext hival
            rw [if_neg hi, if_pos]
            rw [hi_eq, hidx0_last]; exact hjdx_last
        rw [hprod, one_mul, gammaPhiUnit_eq_allEq (F := F) hk r idx0, if_pos]
        -- `idx0` is constant: legs `< k-2` equal `jdx`, last equals `c`; all equal `c`.
        intro i j
        have hcoord : ∀ ℓ : Fin (k - 1), lUnitCoord hk r idx0 ℓ = c := by
          intro ℓ
          rcases (by have := ℓ.isLt; omega : (ℓ : ℕ) < k - 2 ∨ (ℓ : ℕ) = k - 2) with hlt | heq
          · simp only [lUnitCoord, if_pos hlt, hidx0_lt ℓ hlt]
            have := hdiag ⟨ℓ, by omega⟩ ⟨k - 1, by omega⟩
            simp only [rUnitCoord, dif_pos hlt,
              dif_neg (show ¬ (k - 1 : ℕ) < k - 2 by omega),
              if_neg (show ¬ (k - 1 : ℕ) = k - 2 by omega)] at this
            rw [this, hc]
          · simp only [lUnitCoord, if_neg (show ¬ (ℓ : ℕ) < k - 2 by omega),
              if_pos heq, Nat.div_one]
            exact hidx0_last
        rw [hcoord i, hcoord j]
      · -- off-diagonal LHS-indices contribute 0.
        intro idx _ hidx
        have hne : ∃ ℓ : Fin (k - 1), (idx ℓ).val ≠ (idx0 ℓ).val := by
          by_contra h; push_neg at h
          exact hidx (funext fun ℓ => Fin.ext (h ℓ))
        obtain ⟨ℓ, hℓ⟩ := hne
        apply mul_eq_zero_of_left
        apply Finset.prod_eq_zero (Finset.mem_univ ℓ)
        by_cases hlt : (ℓ : ℕ) < k - 2
        · simp only [if_pos hlt]; rw [if_neg]
          rw [hidx0_lt ℓ hlt] at hℓ; exact fun h => hℓ h.symm
        · have hℓval : (ℓ : ℕ) = k - 2 := by have := ℓ.isLt; omega
          have hℓ_eq : ℓ = ⟨k - 2, by omega⟩ := Fin.ext hℓval
          simp only [if_neg hlt]; rw [if_neg]
          rw [hℓ_eq, hidx0_last] at hℓ
          rw [hℓ_eq, hjdx_last]
          intro h
          -- `idx ℓ`.val `= idx.val + r * idx.val = c + r*c` would force `idx ℓ = c`.
          have hlt2 : (idx ⟨k - 2, by omega⟩).val < (r : ℕ) := by
            have hii := (idx ⟨k - 2, by omega⟩).isLt; omega
          have hcc : (idx ⟨k - 2, by omega⟩).val = c := by nlinarith [hlt2, hc_lt, h]
          exact hℓ hcc
      · intro hnot; exact (hnot (Finset.mem_univ _)).elim
    · -- `jdx` is off the diagonal: both sides are `0`.
      rw [if_neg hdiag]
      symm
      apply Finset.sum_eq_zero
      intro idx _
      -- Either the product vanishes, or `LHS idx = 0`.
      by_cases hprodne : (∏ i : Fin (k - 1),
          (if (i : ℕ) < k - 2 then (if (jdx i).val = (idx i).val then (1 : F) else 0)
            else (if (jdx i).val = (idx i).val + r * (idx i).val then 1 else 0))) = 0
      · rw [hprodne, zero_mul]
      · -- Nonzero product forces `idx` to copy `jdx` on legs `< k-2` and `jdx`-last
        -- to be diagonal (`idx`-last `= b` with `jdx`-last `= b + r*b`).  Then the
        -- decoded coordinates of `idx` equal those of `jdx`, so `LHS idx = 0`.
        -- Extract the per-leg constraints from the nonzero product.
        have hfac : ∀ i : Fin (k - 1),
            (if (i : ℕ) < k - 2 then (if (jdx i).val = (idx i).val then (1 : F) else 0)
              else (if (jdx i).val = (idx i).val + r * (idx i).val then 1 else 0)) ≠ 0 := by
          intro i hi0
          exact hprodne (Finset.prod_eq_zero (Finset.mem_univ i) hi0)
        have hlt_legs : ∀ i : Fin (k - 1), (i : ℕ) < k - 2 → (jdx i).val = (idx i).val := by
          intro i hi
          have := hfac i
          rw [if_pos hi] at this
          by_contra hc2; rw [if_neg hc2] at this; exact this rfl
        have hlast : (jdx ⟨k - 2, by omega⟩).val =
            (idx ⟨k - 2, by omega⟩).val + r * (idx ⟨k - 2, by omega⟩).val := by
          have := hfac ⟨k - 2, by omega⟩
          rw [if_neg (show ¬ ((⟨k - 2, by omega⟩ : Fin (k - 1)) : ℕ) < k - 2 by simp)] at this
          by_contra hc2; rw [if_neg hc2] at this; exact this rfl
        set b : ℕ := (idx ⟨k - 2, by omega⟩).val with hb
        have hb_lt : b < (r : ℕ) := by
          have hii : (idx ⟨k - 2, by omega⟩).val < (eL ⟨k - 2, by omega⟩ : ℕ) :=
            (idx ⟨k - 2, by omega⟩).isLt
          omega
        have hjdiv : (jdx ⟨k - 2, by omega⟩).val / (r : ℕ) = b := by
          rw [hlast, Nat.add_mul_div_left _ _ r.pos, Nat.div_eq_of_lt hb_lt, zero_add]
        have hjmod : (jdx ⟨k - 2, by omega⟩).val % (r : ℕ) = b := by
          rw [hlast, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb_lt]
        -- `LHS idx = 0`: its condition equals `hdiag`'s (false) condition.
        rw [gammaPhiUnit_eq_allEq (F := F) hk r idx, if_neg, mul_zero]
        intro hall
        apply hdiag
        intro i j
        -- `lUnitCoord idx` is constant, equal to its value at leg `k-2`, which is `b`.
        have hlcoord_k2 : lUnitCoord hk r idx ⟨k - 2, by omega⟩ = b := by
          simp only [lUnitCoord, if_neg (show ¬ (k - 2 : ℕ) < k - 2 by omega), if_true,
            Nat.div_one]
          exact hb.symm
        -- Every `rUnitCoord jdx` coordinate equals `b`.
        have hr_const : ∀ ℓ : Fin k, rUnitCoord hk r jdx ℓ = b := by
          intro ℓ
          rcases (by have := ℓ.isLt; omega :
              (ℓ : ℕ) < k - 2 ∨ (ℓ : ℕ) = k - 2 ∨ (ℓ : ℕ) = k - 1) with hlt | heq | heq
          · simp only [rUnitCoord, dif_pos hlt]
            rw [hlt_legs ⟨ℓ, by omega⟩ hlt]
            have hl := hall ⟨ℓ, by omega⟩ ⟨k - 2, by omega⟩
            rw [hlcoord_k2] at hl
            simp only [lUnitCoord, if_pos (show ((⟨ℓ, by omega⟩ : Fin (k - 1)) : ℕ) < k - 2
              from hlt)] at hl
            exact hl
          · simp only [rUnitCoord, dif_neg (show ¬ (ℓ : ℕ) < k - 2 by omega), if_pos heq]
            rw [hjdiv]
          · simp only [rUnitCoord, dif_neg (show ¬ (ℓ : ℕ) < k - 2 by omega),
              if_neg (show ¬ (ℓ : ℕ) = k - 2 by omega)]
            rw [hjmod]
        rw [hr_const i, hr_const j]

/-- Tensor-format identity used in Lemma 3.8 normalization (paper tex:1042).

Merging the padded `(k-1)`-unit agrees, up to restriction-equivalence, with
merging the `k`-unit. -/
private lemma gamma_phi_unit_equiv_witness {k : ℕ} (hk : 3 ≤ k) (r : ℕ+) :
    gammaMap (F := F) hk
        (phiMap (F := F) hk (unitTensor (F := F) (k := k - 1) r)) ∼ₜ
      gammaMap (F := F) hk (unitTensor (F := F) (k := k) r) := by
  exact gamma_phi_unit_diagonal_restriction_helper (F := F) hk r

lemma gamma_phi_unit_equiv {k : ℕ} (hk : 3 ≤ k) (r : ℕ+) :
    gammaMap (F := F) hk
        (phiMap (F := F) hk (unitTensor (F := F) (k := k - 1) r)) ∼ₜ
      gammaMap (F := F) hk (unitTensor (F := F) (k := k) r) := by
  exact gamma_phi_unit_equiv_witness (F := F) hk r

set_option linter.flexible false in
/-- Tensor-format identity used in Lemma 3.8 descent equation (paper tex:1042).

Merging after splitting and re-padding agrees, up to restriction-equivalence, with
the original merged tensor. -/
lemma gamma_phi_gamma_equiv {k : ℕ} (hk : 3 ≤ k) {d : Fin k → ℕ+}
    (T : KTensor F d) :
    gammaMap (F := F) hk (phiMap (F := F) hk (gammaMap (F := F) hk T)) ∼ₜ
      gammaMap (F := F) hk T := by
  classical
  have hfmt : ∀ i : Fin (k - 1),
      (dGamma hk (dPhi hk (dGamma hk d)) i : ℕ) = (dGamma hk d i : ℕ) := by
    intro i
    by_cases hi : (i : ℕ) < k - 2
    · simp [dGamma, dPhi, hi]
    · have hi_eq : (i : ℕ) = k - 2 := by
        have := i.isLt
        omega
      have hkm2_lt_km1 : k - 2 < k - 1 := by omega
      simp [dGamma, dPhi, hi_eq, hkm2_lt_km1, PNat.mul_coe]
  constructor
  · apply Restricts.of_eq_cast hfmt
    intro jdx
    simp [gammaMap, phiMap]
    apply congrArg T
    funext j
    by_cases hj : (j : ℕ) < k - 2
    · simp [hj]
    · by_cases hj2 : (j : ℕ) = k - 2
      · ext
        simp [hj2, Fin.divNat, dPhi, Nat.div_one]
      · have hj1 : (j : ℕ) = k - 1 := by
          have := j.isLt
          omega
        have hnot_lt : ¬ k - 1 < k - 2 := by omega
        have hnot_eq : ¬ k - 1 = k - 2 := by omega
        ext
        simp [hj1, hnot_lt, hnot_eq, Fin.divNat, Fin.modNat, dPhi, Nat.div_one]
  · apply Restricts.of_eq_cast (fun i => (hfmt i).symm)
    intro jdx
    simp [gammaMap, phiMap]
    apply congrArg T
    funext j
    by_cases hj : (j : ℕ) < k - 2
    · simp [hj]
    · by_cases hj2 : (j : ℕ) = k - 2
      · ext
        simp [hj2, Fin.divNat, dPhi, Nat.div_one]
      · have hj1 : (j : ℕ) = k - 1 := by
          have := j.isLt
          omega
        have hnot_lt : ¬ k - 1 < k - 2 := by omega
        have hnot_eq : ¬ k - 1 = k - 2 := by omega
        ext
        simp [hj1, hnot_lt, hnot_eq, Fin.divNat, Fin.modNat, dPhi, Nat.div_one]

/-- **Lemma 3.8** (tex:1038-1045, `\label{lem:spec-descend}`).

If `F ∈ Δ(F, k)` (with `k ≥ 3`) and `F(⟨2⟩_{k-1,k}) = 1`, then there exists
`F' ∈ Δ(F, k-1)` such that:
  (a) `F'(U) = F(φ(U))` for every `(k-1)`-tensor `U` (i.e. `F ∘ φ ∈ Δ(F, k-1)`);
  (b) `F(T) = F'(γ(T))` for every `k`-tensor `T` (i.e. `F = F ∘ φ ∘ γ`).

In particular, `F` and `F'` take the same set of values. -/
theorem spec_descend {k : ℕ} (hk : 3 ≤ k) (Fspec : SpectralPoint k F)
    (hij : (⟨k - 2, by omega⟩ : Fin k) ≠ ⟨k - 1, by omega⟩)
    (h2 : Fspec.toFun
        (unitPairTensor (F := F) 2 ⟨k - 2, by omega⟩ ⟨k - 1, by omega⟩ hij) = 1) :
    ∃ Fspec' : SpectralPoint (k - 1) F,
      (∀ {e : Fin (k - 1) → ℕ+} (U : KTensor F e),
          Fspec'.toFun U = Fspec.toFun (phiMap (F := F) hk U))
      ∧ (∀ {d : Fin k → ℕ+} (T : KTensor F d),
          Fspec.toFun T = Fspec'.toFun (gammaMap (F := F) hk T)) := by
  classical
  let Fspec' : SpectralPoint (k - 1) F :=
    { toFun := fun {_e} U => Fspec.toFun (phiMap (F := F) hk U)
      mult := by
        intro eS eT S T
        have hsplit :
            Fspec.toFun (phiMap (F := F) hk (S ⊠ T)) =
              Fspec.toFun (phiMap (F := F) hk S ⊠ phiMap (F := F) hk T) := by
          have heq := gamma_phi_kron_equiv (F := F) hk S T
          exact free_splitting (F := F) hk Fspec hij h2
            (phiMap (F := F) hk (S ⊠ T))
            (phiMap (F := F) hk S ⊠ phiMap (F := F) hk T) ⟨heq.2, heq.1⟩
        calc
          Fspec.toFun (phiMap (F := F) hk (S ⊠ T))
              = Fspec.toFun (phiMap (F := F) hk S ⊠ phiMap (F := F) hk T) := hsplit
          _ = Fspec.toFun (phiMap (F := F) hk S) *
              Fspec.toFun (phiMap (F := F) hk T) := Fspec.mult _ _
      add := by
        intro eS eT S T
        have hsplit :
            Fspec.toFun (phiMap (F := F) hk (S ⊕ₜ T)) =
              Fspec.toFun (phiMap (F := F) hk S ⊕ₜ phiMap (F := F) hk T) := by
          have heq := gamma_phi_add_equiv (F := F) hk S T
          exact free_splitting (F := F) hk Fspec hij h2
            (phiMap (F := F) hk (S ⊕ₜ T))
            (phiMap (F := F) hk S ⊕ₜ phiMap (F := F) hk T) ⟨heq.2, heq.1⟩
        calc
          Fspec.toFun (phiMap (F := F) hk (S ⊕ₜ T))
              = Fspec.toFun (phiMap (F := F) hk S ⊕ₜ phiMap (F := F) hk T) := hsplit
          _ = Fspec.toFun (phiMap (F := F) hk S) +
              Fspec.toFun (phiMap (F := F) hk T) := Fspec.add _ _
      normalize := by
        intro r
        have hsplit :
            Fspec.toFun (phiMap (F := F) hk (unitTensor (F := F) (k := k - 1) r)) =
              Fspec.toFun (unitTensor (F := F) (k := k) r) := by
          exact free_splitting (F := F) hk Fspec hij h2
            (phiMap (F := F) hk (unitTensor (F := F) (k := k - 1) r))
            (unitTensor (F := F) (k := k) r)
            (gamma_phi_unit_equiv (F := F) hk r)
        calc
          Fspec.toFun (phiMap (F := F) hk (unitTensor (F := F) (k := k - 1) r))
              = Fspec.toFun (unitTensor (F := F) (k := k) r) := hsplit
          _ = (r : ℕ) := Fspec.normalize r
      mono := by
        intro eS eT S T hST
        exact Fspec.mono (phiMap (F := F) hk S) (phiMap (F := F) hk T)
          (phiMap_restricts (F := F) hk hST) }
  refine ⟨Fspec', ?_, ?_⟩
  · intro e U
    rfl
  · intro d T
    exact free_splitting (F := F) hk Fspec hij h2 T
      (phiMap (F := F) hk (gammaMap (F := F) hk T))
      ⟨(gamma_phi_gamma_equiv (F := F) hk T).2,
        (gamma_phi_gamma_equiv (F := F) hk T).1⟩

end Semicontinuity
