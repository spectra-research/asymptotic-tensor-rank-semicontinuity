/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.TensorSemiring
import AsymptoticTensorRankSemicontinuity.TensorRank
import AsymptoticTensorRankSemicontinuity.Prerequisites.AsymptoticSpectrumDuality.Defs

/-!
# The `StrassenPreorder` on `TensorClass F k`

This file equips the commutative semiring `TensorClass F k` (built in
`TensorSemiring.lean`) with a `StrassenPreorder` (`AsymptoticSpectrumDuality.Defs`),
the restriction preorder `≤ₜ` lifted to classes. Together with the semiring it is
component 2 of the Strassen-duality bridge.

* the `natCast = unitTensor` glue: the semiring `Nat.cast` (which is
  `1 + 1 + ⋯`) equals the class of the rank-`n` unit tensor;
* the `StrassenPreorder` itself (`tensorStrassenPreorder`), with the
  relation `rel a b := Restricts a.2 b.2` and the eight Strassen-preorder fields.

Source: Strassen (1988); restriction `≤ₜ` is the paper's tensor restriction
(`MaxRankBound.lean`, tex:392).
-/

namespace Semicontinuity

open AsymptoticSpectrumDuality

universe u

variable {F : Type u} [Field F] {k : ℕ} [NeZero k]

/-! ## The `natCast = unitTensor` glue. -/

/-- The class of the rank-`n` unit `k`-tensor, with `0 ↦ 0` (`zeroT`). -/
noncomputable def unitClass (n : ℕ) : TensorClass F k :=
  if h : 0 < n then TensorClass.mk ⟨_, unitTensor F (k := k) ⟨n, h⟩⟩ else 0

@[simp] lemma unitClass_zero : unitClass (F := F) (k := k) 0 = 0 := by
  simp [unitClass]

lemma unitClass_one : unitClass (F := F) (k := k) 1 = 1 := by
  rw [unitClass, dif_pos (by norm_num : 0 < 1)]
  rfl

omit [NeZero k] in
/-- Per-leg cardinality of the format of `unitTensor n ⊕ₜ unitTensor 1`. -/
private lemma unitSucc_fmt (n : ℕ+) (_i : Fin k) :
    (((n + 1 : ℕ+) : ℕ)) = ((n : ℕ+) + (1 : ℕ+) : ℕ+) := by
  rw [PNat.add_coe]

omit [NeZero k] in
/-- **Value identity** for `unitTensor_succ`: evaluating `unitTensor (n+1)` at
`jdx` equals evaluating `unitTensor n ⊕ₜ unitTensor 1` at the cast image. -/
private lemma unitSucc_value (n : ℕ+) (jdx : ∀ _i : Fin k, Fin ((n + 1 : ℕ+) : ℕ)) :
    (unitTensor F (k := k) (n + 1)) jdx
      = ((unitTensor F (k := k) n) ⊕ₜ (unitTensor F (k := k) 1))
          (fun i => Fin.cast (unitSucc_fmt n i) (jdx i)) := by
  classical
  set jdx' : ∀ i : Fin k, Fin (((n : ℕ+) + (1 : ℕ+) : ℕ+) : ℕ) :=
    fun i => Fin.cast (unitSucc_fmt n i) (jdx i) with hjdx'
  have hval : ∀ i, (jdx' i).val = (jdx i).val := fun i => rfl
  -- Uniform upper bound on each leg coordinate: `< n + 1`.
  have hub : ∀ i, (jdx i).val < (n : ℕ) + 1 := by
    intro i
    have h1 : (jdx i).val < ((n + 1 : ℕ+) : ℕ) := (jdx i).isLt
    have h2 : ((n + 1 : ℕ+) : ℕ) = (n : ℕ) + 1 := by rw [PNat.add_coe]; simp
    omega
  rw [directSumTensor_apply_block']
  -- LHS unitTensor (n+1): `1` iff all legs equal.
  change (if ∀ i j : Fin k, jdx i = jdx j then (1 : F) else 0) = _
  by_cases hlow : ∀ i, (jdx' i).val < (n : ℕ)
  · -- all in the `unitTensor n` block.
    rw [dif_pos hlow]
    change _ = (if ∀ i j : Fin k, (⟨(jdx' i).val, hlow i⟩ : Fin (n : ℕ)) = ⟨(jdx' j).val, hlow j⟩
        then (1 : F) else 0)
    congr 1
    apply propext
    constructor
    · intro hall i j; apply Fin.ext; simpa [hval] using congrArg Fin.val (hall i j)
    · intro hall i j; apply Fin.ext
      have := congrArg Fin.val (hall i j); simpa [hval] using this
  · by_cases hhigh : ∀ i, (n : ℕ) ≤ (jdx' i).val
    · -- all in the `unitTensor 1` block: every leg `= n`, hence all equal ⟹ `1 = 1`.
      rw [dif_neg hlow, dif_pos hhigh]
      have hallEq : ∀ i j : Fin k, jdx i = jdx j := by
        intro i j; apply Fin.ext
        have hi := hhigh i; have hj := hhigh j; rw [hval] at hi hj
        have := hub i; have := hub j; omega
      rw [if_pos hallEq, unitTensor_one_eq]
    · -- mixed: LHS not-all-equal (some leg `< n`, some `= n`), RHS `0`.
      rw [dif_neg hlow, dif_neg hhigh]
      rw [if_neg]
      intro hall
      obtain ⟨iL, hiL⟩ := not_forall.1 hlow   -- jdx' iL ≥ n
      obtain ⟨iH, hiH⟩ := not_forall.1 hhigh  -- jdx' iH < n
      push_neg at hiL
      have heq := congrArg Fin.val (hall iL iH)
      rw [hval] at hiL hiH
      omega

omit [NeZero k] in
/-- `unitTensor (n+1) ∼ₜ unitTensor n ⊕ₜ unitTensor 1`: split off one diagonal
coordinate as the rank-`1` block. -/
lemma unitTensor_succ (n : ℕ+) :
    (unitTensor F (k := k) (n + 1)) ∼ₜ
      ((unitTensor F (k := k) n) ⊕ₜ (unitTensor F (k := k) 1)) :=
  ⟨Restricts.of_eq_cast (fun i => unitSucc_fmt n i) (unitSucc_value n),
   Restricts.of_eq_cast (fun i => (unitSucc_fmt n i).symm)
     (fun jdx => by rw [unitSucc_value n]; congr 1)⟩

/-- `unitClass (n+1) = unitClass n + 1` (the additive recursion of the unit
classes), via `unitTensor_succ`. -/
lemma unitClass_succ (n : ℕ) :
    unitClass (F := F) (k := k) (n + 1) = unitClass (F := F) (k := k) n + 1 := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [unitClass_one]
  · -- `n ≥ 1`: both `unitClass n` and `unitClass (n+1)` are unit-tensor classes.
    rw [unitClass, dif_pos (Nat.succ_pos n), unitClass, dif_pos hn, TensorClass.one_def,
      TensorClass.mk_add]
    -- `unitTensor (n+1) ∼ₜ unitTensor n ⊕ₜ unitTensor 1` as `ℕ+`.
    apply TensorClass.mk_eq_of_equiv
    -- Reconcile `⟨n+1, _⟩ : ℕ+` with `(⟨n, hn⟩ : ℕ+) + 1`.
    have hpn : (⟨n + 1, Nat.succ_pos n⟩ : ℕ+) = (⟨n, hn⟩ : ℕ+) + 1 := by
      apply PNat.coe_injective
      change n + 1 = ((⟨n, hn⟩ : ℕ+) : ℕ) + 1
      rfl
    rw [hpn]
    exact unitTensor_succ (⟨n, hn⟩ : ℕ+)

/-- **`Nat.cast = unitClass`**: the semiring `Nat.cast` of `n` (which is
`1 + 1 + ⋯`) equals the class `unitClass n` of the rank-`n` unit tensor. -/
lemma natCast_eq_unitClass (n : ℕ) :
    ((n : ℕ) : TensorClass F k) = unitClass (F := F) (k := k) n := by
  induction n with
  | zero => simp
  | succ m ih => rw [Nat.cast_succ, ih, unitClass_succ]

/-! ## The `StrassenPreorder` on `TensorClass F k`. -/

/-- The lifted restriction relation on classes: `Restricts a.2 b.2`, well-defined
because `Restricts` is `∼ₜ`-invariant in both arguments. -/
def relClass : TensorClass F k → TensorClass F k → Prop :=
  Quotient.lift₂ (fun a b => Restricts a.2 b.2)
    (by
      intro a₁ b₁ a₂ b₂ ha hb
      apply propext
      constructor
      · intro h
        exact (ha.2.trans h).trans hb.1
      · intro h
        exact (ha.1.trans h).trans hb.2)

@[simp] lemma relClass_mk (a b : TT F k) :
    relClass (TensorClass.mk a) (TensorClass.mk b) = Restricts a.2 b.2 := rfl

/-- The zero tensor restricts into any tensor (leg matrices all `0`). -/
lemma zeroT_restricts {d : Fin k → ℕ+} (T : KTensor F d) :
    Restricts (zeroT : KTensor F (fun _ => (1 : ℕ+))) T := by
  classical
  have hne : Nonempty (Fin k) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩⟩
  refine ⟨fun _ => 0, fun jdx => ?_⟩
  change (0 : F) = _
  symm
  apply Finset.sum_eq_zero
  intro idx _
  rw [Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary (Fin k))) rfl, zero_mul]

omit [NeZero k] in
/-- **Monotonicity of unit tensors under restriction** (coordinate inclusion):
`r ≤ s ⟹ unitTensor r ≤ₜ unitTensor s`. The leg matrices are the identity
inclusion `Fin r ↪ Fin s` on every leg. -/
lemma unitTensor_restricts_of_le {r s : ℕ+} (hrs : (r : ℕ) ≤ (s : ℕ)) :
    Restricts (unitTensor F (k := k) r) (unitTensor F (k := k) s) := by
  classical
  -- Leg matrix: `1` iff the `Fin r` row coordinate equals the `Fin s` column one.
  refine ⟨fun _ a b => if a.val = b.val then 1 else 0, ?_⟩
  intro jdx
  -- The unique nonzero column is the coordinate inclusion of `jdx`.
  let idx0 : ∀ i : Fin k, Fin (s : ℕ) :=
    fun i => ⟨(jdx i).val, lt_of_lt_of_le (jdx i).isLt hrs⟩
  rw [Finset.sum_eq_single idx0]
  · have hprod : (∏ i, (if (jdx i).val = (idx0 i).val then (1 : F) else 0)) = 1 := by
      apply Finset.prod_eq_one; intro i _; rw [if_pos rfl]
    rw [hprod, one_mul]
    -- `unitTensor r jdx = unitTensor s idx0`: both `1` iff all legs equal.
    simp only [unitTensor]
    congr 1
    apply propext
    constructor
    · intro hall i j; apply Fin.ext; simpa [idx0] using congrArg Fin.val (hall i j)
    · intro hall i j; apply Fin.ext
      have := congrArg Fin.val (hall i j); simpa [idx0] using this
  · intro col _ hcol
    have hne : ∃ i, col i ≠ idx0 i := by
      by_contra h; push_neg at h; exact hcol (funext h)
    obtain ⟨i₀, hi₀⟩ := hne
    have hzero : (if (jdx i₀).val = (col i₀).val then (1 : F) else 0) = 0 := by
      rw [if_neg]; intro h; apply hi₀; apply Fin.ext
      simp only [idx0]; exact h.symm
    rw [Finset.prod_eq_zero (Finset.mem_univ i₀) hzero, zero_mul]
  · intro hnot; exact (hnot (Finset.mem_univ _)).elim

omit [NeZero k] in
/-- **Restriction is monotone for the `{j}`-flattening rank** (paper tex:379).
If `S ≤ₜ T` then `flatRank S {j} ≤ flatRank T {j}`. The leg-wise linear maps
realizing the restriction factor the `{j}`-flattening of `S` through that of `T`,
and matrix rank only decreases under multiplication.

Version of `Restricts.flatRank_mono` used for the Strassen preorder. -/
lemma Restricts.flatRank_mono {dS dT : Fin k → ℕ+}
    {S : KTensor F dS} {T : KTensor F dT} (h : Restricts S T) (j : Fin k) :
    flatRank S {j} ≤ flatRank T {j} := by
  classical
  obtain ⟨A, hA⟩ := h
  set RowS : Type _ := ∀ i : {i : Fin k // i ∈ ({j} : Finset (Fin k))}, Fin (dS i.val)
  set RowT : Type _ := ∀ i : {i : Fin k // i ∈ ({j} : Finset (Fin k))}, Fin (dT i.val)
  set ColS : Type _ := ∀ i : {i : Fin k // i ∉ ({j} : Finset (Fin k))}, Fin (dS i.val)
  set ColT : Type _ := ∀ i : {i : Fin k // i ∉ ({j} : Finset (Fin k))}, Fin (dT i.val)
  let Pmat : Matrix RowS RowT F :=
    fun rS rT => ∏ i : {i : Fin k // i ∈ ({j} : Finset (Fin k))}, A i.val (rS i) (rT i)
  let Cmat : Matrix ColT ColS F :=
    fun cT cS => ∏ i : {i : Fin k // i ∉ ({j} : Finset (Fin k))}, A i.val (cS i) (cT i)
  let eT := Equiv.piEquivPiSubtypeProd (fun i => i ∈ ({j} : Finset (Fin k)))
    (fun i => Fin (dT i))
  have hfact : flattenMatrix S {j} = Pmat * (flattenMatrix T {j} * Cmat) := by
    funext rS cS
    show flattenMatrix S {j} rS cS = (Pmat * (flattenMatrix T {j} * Cmat)) rS cS
    rw [flattenMatrix, hA]
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply]
    rw [← Equiv.sum_comp eT.symm
      (fun idx : (∀ i, Fin (dT i)) =>
        (∏ i, A i (if h : i ∈ ({j} : Finset (Fin k))
          then rS ⟨i, h⟩ else cS ⟨i, h⟩) (idx i)) * T idx)]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl ?_
    intro rT _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro cT _
    have hsplit_prod :
        (∏ i, A i (if h : i ∈ ({j} : Finset (Fin k))
            then rS ⟨i, h⟩ else cS ⟨i, h⟩) (eT.symm (rT, cT) i))
          = Pmat rS rT * Cmat cT cS := by
      rw [← Fintype.prod_subtype_mul_prod_subtype
        (fun i => i ∈ ({j} : Finset (Fin k)))
        (fun i => A i (if h : i ∈ ({j} : Finset (Fin k))
          then rS ⟨i, h⟩ else cS ⟨i, h⟩) (eT.symm (rT, cT) i))]
      refine congr_arg₂ (· * ·) ?_ ?_
      · simp only [Pmat]
        refine Finset.prod_congr (by ext; simp) (fun x _ => ?_)
        obtain ⟨i, hi⟩ := x
        simp only [dif_pos hi]
        have hval : eT.symm (rT, cT) i = rT ⟨i, hi⟩ := by
          simp only [eT, Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos hi]
        rw [hval]
      · simp only [Cmat]
        refine Finset.prod_congr (by ext; simp) (fun x _ => ?_)
        obtain ⟨i, hi⟩ := x
        simp only [dif_neg hi]
        have hval : eT.symm (rT, cT) i = cT ⟨i, hi⟩ := by
          simp only [eT, Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg hi]
        rw [hval]
    rw [hsplit_prod]
    have harg : (eT.symm (rT, cT))
        = (fun i => if h : i ∈ ({j} : Finset (Fin k))
            then rT ⟨i, h⟩ else cT ⟨i, h⟩) := by
      funext i
      simp only [eT, Equiv.piEquivPiSubtypeProd_symm_apply]
    have hT_entry : T (eT.symm (rT, cT)) = flattenMatrix T {j} rT cT := by
      rw [flattenMatrix, harg]
    rw [hT_entry]
    ring
  unfold flatRank
  rw [hfact]
  calc (Pmat * (flattenMatrix T {j} * Cmat)).rank
      ≤ (flattenMatrix T {j} * Cmat).rank := Matrix.rank_mul_le_right _ _
    _ ≤ (flattenMatrix T {j}).rank := Matrix.rank_mul_le_left _ _

/-- The singleton-leg row-index type of the `{i₀}`-flattening is in bijection with
`Fin r` (via the unique element `i₀` of the subtype). Built explicitly so that the
forward map is the constant tuple. -/
private def flatRowEquiv (i₀ : Fin k) (r : ℕ+) :
    Fin (r : ℕ) ≃ (∀ _p : {i : Fin k // i ∈ ({i₀} : Finset (Fin k))}, Fin (r : ℕ)) where
  toFun a := fun _ => a
  invFun f := f ⟨i₀, by simp⟩
  left_inv a := rfl
  right_inv f := by
    funext p
    have hp : p = ⟨i₀, by simp⟩ := by
      apply Subtype.ext
      exact Finset.mem_singleton.1 p.2
    rw [hp]

omit [NeZero k] in
/-- The row-equiv sends `a` to the constant tuple `a` on the singleton subtype. -/
private lemma flatRowEquiv_apply (i₀ : Fin k) (r : ℕ+) (a : Fin (r : ℕ))
    (p : {i : Fin k // i ∈ ({i₀} : Finset (Fin k))}) :
    (flatRowEquiv (k := k) i₀ r) a p = a := rfl

omit [NeZero k] in
/-- **Flattening rank of a unit tensor** (paper tex:378-380): for `k ≥ 2` and any
leg `i₀`, `flatRank (unitTensor r) {i₀} = r`. The `{i₀}`-flattening has an `r × r`
identity submatrix (columns where all other legs are constant), giving rank `≥ r`,
while it has only `r` rows, giving rank `≤ r`. -/
lemma flatRank_unitTensor (hk : 2 ≤ k) (i₀ : Fin k) (r : ℕ+) :
    flatRank (unitTensor F (k := k) r) {i₀} = (r : ℕ) := by
  classical
  -- A distinct "other" leg `j₀ ≠ i₀` exists since `k ≥ 2`.
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin k, j₀ ≠ i₀ := by
    by_contra h; push_neg at h
    have : Fintype.card (Fin k) ≤ 1 := Fintype.card_le_one_iff.2 (fun a b => (h a).trans (h b).symm)
    simp only [Fintype.card_fin] at this; omega
  have huniq : Unique {i : Fin k // i ∈ ({i₀} : Finset (Fin k))} := by
    refine ⟨⟨⟨i₀, by simp⟩⟩, ?_⟩
    rintro ⟨i, hi⟩; apply Subtype.ext; simpa using hi
  -- Cardinality of the row-index type is `r`.
  have hcardRow :
      Fintype.card (∀ _p : {i : Fin k // i ∈ ({i₀} : Finset (Fin k))}, Fin (r : ℕ)) = (r : ℕ) := by
    rw [Fintype.card_pi, Fintype.prod_unique]; simp
  -- Upper bound: `M.rank ≤ card RowT = r`.
  have hub : flatRank (unitTensor F (k := k) r) {i₀} ≤ (r : ℕ) := by
    have h := (flattenMatrix (unitTensor F (k := k) r) {i₀}).rank_le_card_height
    rw [hcardRow] at h
    exact h
  -- Lower bound: an `r × r` identity submatrix of `Mᵀ`.
  let eRow : Fin (r : ℕ) ≃ (∀ p : {i : Fin k // i ∈ ({i₀} : Finset (Fin k))}, Fin (r : ℕ)) :=
    flatRowEquiv (k := k) i₀ r
  let g : Fin (r : ℕ) → (∀ q : {q : Fin k // q ∉ ({i₀} : Finset (Fin k))}, Fin (r : ℕ)) :=
    fun c => fun _ => c
  -- The submatrix `N` of `Mᵀ`: rows via `g` (columns of `M`), columns via `eRow`.
  have hNone : ((flattenMatrix (unitTensor F (k := k) r) {i₀}).transpose).submatrix g eRow = 1 := by
    funext c a
    change ((flattenMatrix (unitTensor F (k := k) r) {i₀}).transpose) (g c) (eRow a)
      = (1 : Matrix (Fin (r:ℕ)) (Fin (r:ℕ)) F) c a
    change flattenMatrix (unitTensor F (k := k) r) {i₀} (eRow a) (g c) = _
    rw [flattenMatrix]
    simp only [unitTensor]
    rw [Matrix.one_apply]
    have hidx_i₀ : (if h : i₀ ∈ ({i₀} : Finset (Fin k)) then (eRow a) ⟨i₀, h⟩ else g c ⟨i₀, h⟩)
        = a := by
      rw [dif_pos (by simp)]; exact flatRowEquiv_apply (k := k) i₀ r a _
    have hidx_j₀ : (if h : j₀ ∈ ({i₀} : Finset (Fin k)) then (eRow a) ⟨j₀, h⟩ else g c ⟨j₀, h⟩)
        = c := by
      rw [dif_neg (by simp [hj₀])]
    by_cases hca : c = a
    · subst hca
      rw [if_pos, if_pos rfl]
      intro p q
      have hval : ∀ x : Fin k,
          (if h : x ∈ ({i₀} : Finset (Fin k)) then (eRow c) ⟨x, h⟩ else g c ⟨x, h⟩) = c := by
        intro x
        by_cases hx : x ∈ ({i₀} : Finset (Fin k))
        · rw [dif_pos hx]; exact flatRowEquiv_apply (k := k) i₀ r c _
        · rw [dif_neg hx]
      rw [hval p, hval q]
    · rw [if_neg hca, if_neg]
      intro hall
      apply hca
      have := hall i₀ j₀
      rw [hidx_i₀, hidx_j₀] at this
      exact this.symm
  -- Conclude `r ≤ M.rank`.
  have hlb : (r : ℕ) ≤ flatRank (unitTensor F (k := k) r) {i₀} := by
    have h1 : (((flattenMatrix (unitTensor F (k := k) r) {i₀}).transpose).submatrix g eRow).rank
        ≤ ((flattenMatrix (unitTensor F (k := k) r) {i₀}).transpose).rank :=
      Matrix.rank_submatrix_le g eRow _
    rw [hNone, Matrix.rank_one, Fintype.card_fin] at h1
    rw [flatRank, ← Matrix.rank_transpose (flattenMatrix (unitTensor F (k := k) r) {i₀})]
    exact h1
  omega

omit [NeZero k] in
/-- **Nat-compatibility of `≤ₜ` on unit tensors** (`k ≥ 2`): `n ≤ m` iff
`unitTensor n ≤ₜ unitTensor m`. Forward is coordinate inclusion; reverse is
`flatRank`-monotonicity (`flatRank (unitTensor r) {i} = r`). -/
lemma unitTensor_restricts_iff_le (hk : 2 ≤ k) {n m : ℕ+} :
    Restricts (unitTensor F (k := k) n) (unitTensor F (k := k) m) ↔ (n : ℕ) ≤ (m : ℕ) := by
  constructor
  · intro h
    have i₀ : Fin k := ⟨0, by omega⟩
    have := h.flatRank_mono i₀
    rwa [flatRank_unitTensor (F := F) hk i₀ n, flatRank_unitTensor (F := F) hk i₀ m] at this
  · intro h; exact unitTensor_restricts_of_le h

/-- Nat-compatibility at the level of classes (`k ≥ 2`):
`n ≤ m ↔ relClass (n) (m)`. -/
lemma nat_compat_relClass (hk : 2 ≤ k) (n m : ℕ) :
    n ≤ m ↔ relClass ((n : TensorClass F k)) ((m : TensorClass F k)) := by
  classical
  rw [natCast_eq_unitClass, natCast_eq_unitClass]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- `n = 0`: LHS `0 ≤ m` true; RHS `relClass 0 (unitClass m)` true (zero restricts).
    subst hn
    simp only [Nat.zero_le, true_iff, unitClass_zero]
    -- `relClass 0 (unitClass m)`.
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp only [unitClass_zero]; exact Restricts.refl _
    · rw [unitClass, dif_pos hm, TensorClass.zero_def]
      exact zeroT_restricts _
  · rcases Nat.eq_zero_or_pos m with hm | hm
    · -- `m = 0`, `n ≥ 1`: LHS false; RHS `relClass (unitTensor n) 0` false.
      subst hm
      simp only [Nat.le_zero, unitClass_zero]
      constructor
      · intro h; omega
      · intro h
        rw [unitClass, dif_pos hn, TensorClass.zero_def] at h
        -- `Restricts (unitTensor n) zeroT` ⟹ `flatRank` of unit `= 0`, contradiction.
        exfalso
        have i₀ : Fin k := ⟨0, by omega⟩
        have hmono := h.flatRank_mono i₀
        rw [flatRank_unitTensor (F := F) hk i₀ ⟨n, hn⟩] at hmono
        have hz : flatRank (zeroT : KTensor F (fun _ => (1 : ℕ+))) {i₀} = 0 := by
          rw [flatRank]
          have : flattenMatrix (zeroT : KTensor F (fun _ => (1 : ℕ+))) {i₀} = 0 := by
            funext row col; rfl
          rw [this, Matrix.rank_zero]
        rw [hz] at hmono
        simp only [PNat.mk_coe] at hmono
        omega
    · -- both `≥ 1`: reduce to `unitTensor_restricts_iff_le`.
      rw [unitClass, dif_pos hn, unitClass, dif_pos hm]
      change _ ↔ Restricts (unitTensor F (k := k) ⟨n, hn⟩) (unitTensor F (k := k) ⟨m, hm⟩)
      rw [unitTensor_restricts_iff_le (F := F) hk]
      rfl

/-! ### Archimedean helpers. -/

/-- **Prod-dims restriction** (paper tex:534-536): every tensor `T : KTensor F d`
restricts to the rank-`(∏ dᵢ)` unit tensor, via the standard-basis decomposition.
Port of the construction in `SpectrumWellOrdered.Fspec_le_prod_dims_F`. -/
lemma restricts_unitTensor_prod_dims {d : Fin k → ℕ+} (T : KTensor F d)
    (N : ℕ) (hN : N = ∏ i, (d i : ℕ)) (hNpos : 0 < N) :
    Restricts T (unitTensor F (k := k) ⟨N, hNpos⟩) := by
  classical
  have hk : (0 : ℕ) < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hcard : Fintype.card (∀ i : Fin k, Fin (d i)) = N := by
    rw [Fintype.card_pi, hN]; simp
  let e : Fin N ≃ (∀ i : Fin k, Fin (d i)) :=
    (finCongr hcard).symm.trans (Fintype.equivFin (∀ i : Fin k, Fin (d i))).symm
  refine ⟨fun i => fun (j : Fin (d i)) (c : Fin N) =>
    if i = ⟨0, hk⟩ then (if j = (e c) i then T (e c) else 0)
                   else (if j = (e c) i then 1 else 0), ?_⟩
  intro jdx
  have hterm : ∀ c : Fin N,
      (∏ i, (if i = ⟨0, hk⟩ then (if jdx i = (e c) i then T (e c) else 0)
                            else (if jdx i = (e c) i then 1 else 0)))
        = (if jdx = e c then T (e c) else 0) := by
    intro c
    by_cases h : jdx = e c
    · rw [h, if_pos rfl]
      rw [show (∏ i, (if i = (⟨0, hk⟩ : Fin k)
                then (if (e c) i = (e c) i then T (e c) else 0)
                else (if (e c) i = (e c) i then 1 else 0)))
            = ∏ i, if i = (⟨0, hk⟩ : Fin k) then T (e c) else 1 from
          Finset.prod_congr rfl (fun i _ => by simp)]
      rw [Finset.prod_ite_eq' (Finset.univ) (⟨0, hk⟩ : Fin k) (fun _ => T (e c))]
      simp
    · rw [if_neg h]
      have hex : ∃ i₀ : Fin k, jdx i₀ ≠ (e c) i₀ := by
        by_contra hne; push_neg at hne; exact h (funext hne)
      obtain ⟨i₀, hi₀⟩ := hex
      apply Finset.prod_eq_zero (Finset.mem_univ i₀)
      by_cases hi : i₀ = ⟨0, hk⟩ <;> simp [hi, hi₀]
  have hT_eq : T jdx = ∑ c : Fin N, (if jdx = e c then T (e c) else 0) := by
    rw [Finset.sum_eq_single (e.symm jdx)]
    · rw [Equiv.apply_symm_apply, if_pos rfl]
    · intro c _ hc
      have : jdx ≠ e c := by intro heq; apply hc; rw [heq, Equiv.symm_apply_apply]
      rw [if_neg this]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  rw [hT_eq]
  refine Finset.sum_of_injOn (e := fun c : Fin N => (fun _ : Fin k => c)) ?_ ?_ ?_ ?_
  · intro a _ b _ hab
    have := congrFun hab ⟨0, hk⟩; simpa using this
  · intro c _; exact Finset.mem_univ _
  · intro idx _ hidx
    have hne : ¬ (∀ i j : Fin k, idx i = idx j) := by
      intro hconst; apply hidx
      refine ⟨idx ⟨0, hk⟩, by simp, ?_⟩
      funext i; exact (hconst ⟨0, hk⟩ i)
    have huz : unitTensor (F := F) (k := k) ⟨N, hNpos⟩ idx = 0 := by
      simp only [unitTensor]; rw [if_neg hne]
    rw [huz, mul_zero]
  · intro c _
    have hud : unitTensor (F := F) (k := k) ⟨N, hNpos⟩ (fun _ : Fin k => c) = 1 := by
      simp [unitTensor]
    simp only [hud, mul_one]
    exact (hterm c).symm

/-- A nonzero tensor has a nonzero entry. -/
lemma exists_ne_zero_of_mk_ne_zero {d : Fin k → ℕ+} (T : KTensor F d)
    (hT : TensorClass.mk ⟨d, T⟩ ≠ (0 : TensorClass F k)) :
    ∃ idx, T idx ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  apply hT
  rw [TensorClass.zero_def]
  apply TensorClass.mk_eq_of_equiv
  -- `T = 0` as a tensor, so `T ∼ₜ zeroT`.
  have hT0 : T = (0 : KTensor F d) := by funext idx; exact h idx
  change T ∼ₜ (zeroT : KTensor F (fun _ => (1 : ℕ+)))
  rw [hT0]
  exact (zeroT_equiv_zero (F := F) (d := d)).symm

/-- A nonzero tensor admits the rank-`1` unit as a restriction: pick a nonzero
entry `T idx₀ = α ≠ 0`, and use the leg "covector" `δ_{idx₀}` scaled by `α⁻¹`. -/
lemma unitTensor_one_restricts_of_ne_zero {d : Fin k → ℕ+} (T : KTensor F d)
    (hT : TensorClass.mk ⟨d, T⟩ ≠ (0 : TensorClass F k)) :
    Restricts (unitTensor F (k := k) 1) T := by
  classical
  have hk : (0 : ℕ) < k := Nat.pos_of_ne_zero (NeZero.ne k)
  obtain ⟨idx₀, hidx₀⟩ := exists_ne_zero_of_mk_ne_zero T hT
  -- Leg matrix on leg `i`: row `Fin 1`, col `Fin (d i)`; selects coordinate `idx₀ i`,
  -- with the inverse scalar `(T idx₀)⁻¹` placed on leg `0`.
  refine ⟨fun i => fun (_ : Fin (1 : ℕ+)) (c : Fin (d i)) =>
    if i = ⟨0, hk⟩ then (if c = idx₀ i then (T idx₀)⁻¹ else 0)
                   else (if c = idx₀ i then 1 else 0), ?_⟩
  intro jdx
  rw [Finset.sum_eq_single idx₀]
  · -- the coefficient at `idx₀` is `(T idx₀)⁻¹`, and `unitTensor 1 jdx = 1`.
    have hprod : (∏ i, (if i = (⟨0, hk⟩ : Fin k)
          then (if idx₀ i = idx₀ i then (T idx₀)⁻¹ else 0)
          else (if idx₀ i = idx₀ i then 1 else 0)))
        = (T idx₀)⁻¹ := by
      rw [show (∏ i, (if i = (⟨0, hk⟩ : Fin k)
            then (if idx₀ i = idx₀ i then (T idx₀)⁻¹ else 0)
            else (if idx₀ i = idx₀ i then 1 else 0)))
          = ∏ i, if i = (⟨0, hk⟩ : Fin k) then (T idx₀)⁻¹ else 1 from
        Finset.prod_congr rfl (fun i _ => by simp)]
      rw [Finset.prod_ite_eq' (Finset.univ) (⟨0, hk⟩ : Fin k) (fun _ => (T idx₀)⁻¹)]
      simp
    rw [hprod, unitTensor_one_eq]
    change (1 : F) = (T idx₀)⁻¹ * T idx₀
    rw [inv_mul_cancel₀ hidx₀]
  · intro col _ hcol
    have hex : ∃ i₀ : Fin k, col i₀ ≠ idx₀ i₀ := by
      by_contra hne; push_neg at hne; exact hcol (funext hne)
    obtain ⟨i₀, hi₀⟩ := hex
    apply mul_eq_zero_of_left
    apply Finset.prod_eq_zero (Finset.mem_univ i₀)
    by_cases hi : i₀ = ⟨0, hk⟩ <;> simp [hi, hi₀]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

/-! ### The `StrassenPreorder`. -/

/-- **Strassen preorder on `TensorClass F k`** (Strassen 1988), for `k ≥ 2`.
The relation is the restriction preorder `≤ₜ` lifted to classes; the eight fields
are reflexivity/transitivity of `≤ₜ`, the zero tensor as least element,
nat-compatibility (`flatRank` of unit tensors), additive/multiplicative
monotonicity (`directSum_congr`/`kron_congr`), and the Archimedean property
(every tensor restricts to a unit tensor; a nonzero tensor absorbs `⟨1⟩`). -/
noncomputable def tensorStrassenPreorder (hk : 2 ≤ k) :
    StrassenPreorder (TensorClass F k) where
  rel := relClass
  refl := by
    rintro ⟨a⟩; exact Restricts.refl a.2
  trans := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ hab hbc; exact Restricts.trans hab hbc
  zero_le := by
    rintro ⟨a⟩
    rw [TensorClass.zero_def]
    exact zeroT_restricts a.2
  nat_compat := nat_compat_relClass hk
  add_mono := by
    rintro ⟨a⟩ ⟨b⟩ ⟨s⟩ hab
    exact Restricts.directSum_congr hab (Restricts.refl s.2)
  mul_mono := by
    rintro ⟨a⟩ ⟨b⟩ ⟨s⟩ hab
    exact Restricts.kron_congr hab (Restricts.refl s.2)
  archimedean := by
    rintro ⟨a⟩ ⟨b⟩ hb
    classical
    -- `r := ∏ (da i)`; `a' ≤ₜ ⟨r⟩` and `⟨r⟩ ≤ₜ ⟨r⟩ ⊠ b'` (since `b ≠ 0`).
    set R : ℕ := ∏ i, (a.1 i : ℕ) with hR
    have hRpos : 0 < R := by rw [hR]; exact Finset.prod_pos (fun i _ => (a.1 i).pos)
    refine ⟨R, ?_⟩
    -- Compute the representative of `(R : TensorClass) * mk b`.
    rw [natCast_eq_unitClass, unitClass, dif_pos hRpos]
    -- `mk ⟨_, unitTensor ⟨R⟩⟩ * mk b = mk ⟨_, unitTensor ⟨R⟩ ⊠ b'⟩`.
    change relClass (TensorClass.mk a)
      (TensorClass.mk ⟨_, unitTensor F (k := k) ⟨R, hRpos⟩⟩ * TensorClass.mk b)
    rw [TensorClass.mk_mul]
    change Restricts a.2 (unitTensor F (k := k) ⟨R, hRpos⟩ ⊠ b.2)
    -- `a' ≤ₜ ⟨R⟩`.
    have h1 : Restricts a.2 (unitTensor F (k := k) ⟨R, hRpos⟩) :=
      restricts_unitTensor_prod_dims a.2 R hR hRpos
    -- `⟨R⟩ ∼ₜ ⟨R⟩ ⊠ ⟨1⟩ ≤ₜ ⟨R⟩ ⊠ b'`.
    have hb' : Restricts (unitTensor F (k := k) 1) b.2 :=
      unitTensor_one_restricts_of_ne_zero b.2 hb
    have h2 : Restricts (unitTensor F (k := k) ⟨R, hRpos⟩)
        (unitTensor F (k := k) ⟨R, hRpos⟩ ⊠ b.2) := by
      refine Restricts.trans (kron_one (unitTensor F (k := k) ⟨R, hRpos⟩)).2 ?_
      exact Restricts.kron_congr (Restricts.refl _) hb'
    exact Restricts.trans h1 h2

/-- The tensor restriction preorder satisfies the zero-aware strong-Archimedean
alternative used by the gapped-spectrum duality theorem. -/
theorem tensor_strong_archimedean (hk : 2 ≤ k) :
    ∀ a : TensorClass F k,
      (tensorStrassenPreorder (F := F) hk).rel a 0 ∨
        (tensorStrassenPreorder (F := F) hk).rel 1 a := by
  intro a
  refine Quotient.inductionOn a ?_
  rintro ⟨d, T⟩
  by_cases hzero : TensorClass.mk ⟨d, T⟩ = (0 : TensorClass F k)
  · left
    change (tensorStrassenPreorder (F := F) hk).rel (TensorClass.mk ⟨d, T⟩) 0
    rw [hzero]
    exact (tensorStrassenPreorder (F := F) hk).refl 0
  · right
    rw [← unitClass_one (F := F) (k := k)]
    change relClass (unitClass (F := F) (k := k) 1) (TensorClass.mk ⟨d, T⟩)
    rw [unitClass, dif_pos (by norm_num : (0 : ℕ) < 1)]
    exact unitTensor_one_restricts_of_ne_zero T hzero

end Semicontinuity
