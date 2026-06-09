/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.MaxRankBound
import AsymptoticTensorRankSemicontinuity.TensorSemiring
import AsymptoticTensorRankSemicontinuity.SpectrumDescend
import AsymptoticTensorRankSemicontinuity.TensorStrassenPreorder
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.SpectrumBridge
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.CrossingPairAnyField
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.PairUnitKron

/-!
# Unit-overhead lemma for Corollary 3.5

Source: **Semicontinuity paper** (Christandl–Hoeberechts–Nieuwboer–Vrana–Zuiddam),
proof of Corollary 3.5 (the field-invariance / border-subrank washout steps,
paper tex:976-996).

## Finite subrank subadditivity is false

Two consumers (`AsymptoticSubrank/FieldInvariance.lean`, `AsymptoticSubrank/BorderSubrank.lean`)
use the unit-overhead bound

  `subrank (⟨q⟩ ⊠ S) ≤ q · subrank S`.

This `(★)` is **FALSE**: `⟨q⟩ ⊠ S = ⊕^q S` (a `q`-fold direct sum), and the
subrank is *super*-additive under `⊕`, NOT sub-additive.  The
Derksen–Makam–Zuiddam counterexample exhibits tensors with
`Q(S), Q(T) ≤ √(3n−2)` yet `Q(S ⊕ T) ≥ n`, so no finite-subrank subadditivity
bound of the `(★)` shape can hold.

The valid unit-overhead lemma puts the **asymptotic** subrank on the right:

  `subrank (⟨q⟩ ⊠ S) ≤ q · asympSubrank S`.

It is proved at the *spectrum* level (Strassen 1988), NOT via any finite-subrank
subadditivity: every spectral point `φ` gives `subrank (⟨q⟩ ⊠ S) ≤ q · φ(S)`
(T1, duality-free), and the asymptotic-spectrum duality (completeness of the
asymptotic spectrum, Strassen 1988 Thm 3.10) collapses `q · inf_φ φ(S)` to
`q · asympSubrank S`.

## Main results

* `subrank_unitKron_le_spectralPoint` — the per-spectral-point bound.
* `asympSubrank_kronPowNat` — Kron-power law for `asympSubrank`. Note the
  exponent `n+1`: `kronPowNat T 0 = T`, so `kronPowNat T n`
  is `T^{⊠(n+1)}`, hence `asympSubrank (kronPowNat T n) = asympSubrank T ^ (n+1)`.
* `subrank_unitKron_le_mul_asympSubrank` — the unit-overhead lemma.
* `subrank_of_restricts_unit_overhead` — the form used downstream.
-/

namespace Semicontinuity

open AsymptoticSpectrumDuality

universe u

variable {F : Type u} [Field F] {k : ℕ}

/-- A spectral point sends the canonical zero tensor to `0`
    (re-proof of `SpectralPointExtension.SpectralPoint.toFun_zeroT`, kept local to
    avoid importing the heavy `SpectralPointExtension` chain). -/
private lemma SpectralPoint.toFun_zeroT' [NeZero k] (φ : SpectralPoint k F) :
    φ.toFun (zeroT (F := F) (k := k)) = 0 := by
  have hadd := φ.add (zeroT (F := F) (k := k)) (zeroT (F := F) (k := k))
  have hequiv : (zeroT (F := F) (k := k) ⊕ₜ zeroT (F := F) (k := k))
      ∼ₜ zeroT (F := F) (k := k) :=
    zero_directSum (dZ := fun _ => (1 : ℕ+)) (zeroT (F := F) (k := k))
  have hinv : φ.toFun (zeroT (F := F) (k := k) ⊕ₜ zeroT (F := F) (k := k))
      = φ.toFun (zeroT (F := F) (k := k)) :=
    le_antisymm (φ.mono _ _ hequiv.1) (φ.mono _ _ hequiv.2)
  rw [hinv] at hadd
  linarith

/-- Spectral points are nonnegative: `0 = φ(zeroT) ≤ φ(S)` since `zeroT ≤ₜ S`. -/
private lemma SpectralPoint.toFun_nonneg [NeZero k] (φ : SpectralPoint k F)
    {d : Fin k → ℕ+} (S : KTensor F d) : (0 : ℝ) ≤ φ.toFun S := by
  have hmono := φ.mono (zeroT : KTensor F (fun _ => (1 : ℕ+))) S (zeroT_restricts S)
  rwa [SpectralPoint.toFun_zeroT' φ] at hmono

/-! ## Boundedness of the subrank set (needed to extract `a ≤ subrank` in T4).

`r ≤ flatRank (⟨r⟩) {i₀} ≤ flatRank X {i₀}`, so the subrank set is bounded above.
The first inequality reads the `r × r` identity off two distinct legs `i₀ ≠ i₁`
(this is why `2 ≤ k` is needed; a local re-proof of the FieldInvariance private
`unitTensor_flatRank_singleton_ge`). -/

/-- `r ≤ flatRank (⟨r⟩) {i₀}`: the `{i₀}`-flattening of the rank-`r` unit tensor
    contains the `r × r` identity submatrix (read off two distinct legs). -/
private lemma unitTensor_flatRank_singleton_ge'
    (i₀ i₁ : Fin k) (hne : i₁ ≠ i₀) {r : ℕ} (hr : 0 < r) :
    r ≤ flatRank (unitTensor F (k := k) ⟨r, hr⟩) {i₀} := by
  classical
  set U : KTensor F (fun _ : Fin k => (⟨r, hr⟩ : ℕ+)) := unitTensor F (k := k) ⟨r, hr⟩
  have memi : i₀ ∈ ({i₀} : Finset (Fin k)) := Finset.mem_singleton_self i₀
  have memj : i₁ ∉ ({i₀} : Finset (Fin k)) := by rwa [Finset.mem_singleton]
  let eRow : Fin r ≃ ((x : {x // x ∈ ({i₀} : Finset (Fin k))}) → Fin r) :=
    { toFun := fun m _ => m
      invFun := fun row => row ⟨i₀, memi⟩
      left_inv := fun m => rfl
      right_inv := fun row => by
        funext x
        obtain ⟨x, hx⟩ := x
        have : x = i₀ := Finset.mem_singleton.mp hx
        subst this
        rfl }
  let cmap : Fin r → ((x : {x // x ∉ ({i₀} : Finset (Fin k))}) → Fin r) :=
    fun v _ => v
  have hsub : (flattenMatrix U {i₀}).submatrix eRow cmap = (1 : Matrix (Fin r) (Fin r) F) := by
    ext m v
    rw [Matrix.submatrix_apply, Matrix.one_apply]
    simp only [flattenMatrix, U, unitTensor]
    set g : Fin k → Fin r := fun x => if h : x ∈ ({i₀} : Finset (Fin k))
      then (eRow m ⟨x, h⟩ : Fin r) else (cmap v ⟨x, h⟩ : Fin r) with hg
    change (if ∀ i j : Fin k, g i = g j then (1 : F) else 0) = if m = v then 1 else 0
    have hmerge : ∀ a : Fin k, g a = if a ∈ ({i₀} : Finset (Fin k)) then m else v := by
      intro a
      simp only [hg]
      by_cases ha : a ∈ ({i₀} : Finset (Fin k))
      · rw [dif_pos ha, if_pos ha]; rfl
      · rw [dif_neg ha, if_neg ha]
    have hval_i0 : g i₀ = m := by rw [hmerge i₀, if_pos memi]
    have hval_i1 : g i₁ = v := by rw [hmerge i₁, if_neg memj]
    have hpred : (∀ i j : Fin k, g i = g j) ↔ m = v := by
      constructor
      · intro hall
        have h2 := hall i₀ i₁
        rw [hval_i0, hval_i1] at h2
        exact h2
      · intro hmv a b
        rw [hmerge a, hmerge b, hmv]
        split <;> split <;> rfl
    by_cases hmv : m = v
    · rw [if_pos (hpred.mpr hmv), if_pos hmv]
    · rw [if_neg (fun h => hmv (hpred.mp h)), if_neg hmv]
  have hsubr : ((flattenMatrix U {i₀}).submatrix eRow cmap).rank
      ≤ (flattenMatrix U {i₀}).rank := by
    rw [← Matrix.rank_transpose ((flattenMatrix U {i₀}).submatrix eRow cmap),
        ← Matrix.rank_transpose (flattenMatrix U {i₀}), Matrix.transpose_submatrix]
    exact Matrix.rank_submatrix_le _ eRow _
  rw [hsub, Matrix.rank_one, Fintype.card_fin] at hsubr
  exact hsubr

/-- The subrank set `{r | 0 < r ∧ ⟨r⟩ ≤ₜ X}` is bounded above (by `flatRank X {i₀}`
    for two distinct legs `i₀ ≠ i₁`, available when `2 ≤ k`). -/
lemma subrank_set_bddAbove' (i₀ i₁ : Fin k) (hne : i₁ ≠ i₀)
    {d : Fin k → ℕ+} (X : KTensor F d) :
    BddAbove { r : ℕ | ∃ hr : 0 < r, Restricts (unitTensor F (k := k) ⟨r, hr⟩) X } := by
  refine ⟨flatRank X {i₀}, ?_⟩
  rintro r ⟨hr, hres⟩
  calc r ≤ flatRank (unitTensor F (k := k) ⟨r, hr⟩) {i₀} :=
        unitTensor_flatRank_singleton_ge' i₀ i₁ hne hr
    _ ≤ flatRank X {i₀} := hres.flatRank_le {i₀}

/-! ## T1 — per-spectral-point unit-overhead bound (duality-free). -/

/-- **T1 — per-spectral-point unit-overhead bound** (Strassen 1988; paper
    tex:976-996).

For any spectral point `φ : SpectralPoint k F`, any overhead `q : ℕ+`, and any
`k`-tensor `S`,

  `subrank (⟨q⟩ ⊠ S) ≤ q · φ(S)`     (as reals).

Proof (duality-free).  Every member `a` of the subrank set of `⟨q⟩ ⊠ S` is a
positive `a` with `⟨a⟩ ≤ₜ ⟨q⟩ ⊠ S`.  Applying `φ` and using its
`normalize`/`mult`/`mono` axioms,

  `a = φ(⟨a⟩) ≤ φ(⟨q⟩ ⊠ S) = φ(⟨q⟩) · φ(S) = q · φ(S)`.

So `q · φ(S)` is a real upper bound for the (ℕ-valued) subrank set; since every
member is `≤ q · φ(S)`, the `Nat.sSup` is `≤ q · φ(S)` after the `ℕ → ℝ` cast. -/
theorem subrank_unitKron_le_spectralPoint [NeZero k]
    (φ : SpectralPoint k F) (q : ℕ+) {d : Fin k → ℕ+} (S : KTensor F d) :
    (subrank (unitTensor F (k := k) q ⊠ S) : ℝ) ≤ (q : ℝ) * φ.toFun S := by
  classical
  -- Each member `a` of the subrank set satisfies `(a : ℝ) ≤ q · φ(S)`.
  have hmem : ∀ a ∈ { r : ℕ | ∃ hr : 0 < r,
      Restricts (unitTensor F (k := k) ⟨r, hr⟩) (unitTensor F (k := k) q ⊠ S) },
      (a : ℝ) ≤ (q : ℝ) * φ.toFun S := by
    rintro a ⟨ha, hres⟩
    -- `a = φ(⟨a⟩)`.
    have h1 : φ.toFun (unitTensor F (k := k) ⟨a, ha⟩) = (a : ℝ) := by
      rw [φ.normalize ⟨a, ha⟩]; simp
    -- `φ(⟨a⟩) ≤ φ(⟨q⟩ ⊠ S)` by monotonicity.
    have h2 : φ.toFun (unitTensor F (k := k) ⟨a, ha⟩)
        ≤ φ.toFun (unitTensor F (k := k) q ⊠ S) :=
      φ.mono _ _ hres
    -- `φ(⟨q⟩ ⊠ S) = φ(⟨q⟩) · φ(S) = q · φ(S)`.
    have h3 : φ.toFun (unitTensor F (k := k) q ⊠ S) = (q : ℝ) * φ.toFun S := by
      rw [φ.mult, φ.normalize q]
    rw [h1] at h2
    rw [h3] at h2
    exact h2
  -- `q · φ(S)` is a nonnegative real bound (`φ ≥ 0`, `q > 0`).
  have hqφ_nonneg : (0 : ℝ) ≤ (q : ℝ) * φ.toFun S := by
    have : (0 : ℝ) ≤ φ.toFun S := SpectralPoint.toFun_nonneg φ S
    positivity
  -- The ℕ-valued subrank set is bounded by `⌊q · φ(S)⌋₊`, so `subrank ≤ ⌊q·φ(S)⌋₊`.
  have hbound : subrank (unitTensor F (k := k) q ⊠ S) ≤ ⌊(q : ℝ) * φ.toFun S⌋₊ := by
    apply csSup_le'
    intro a ha
    rw [Nat.le_floor_iff hqφ_nonneg]
    exact hmem a ha
  calc (subrank (unitTensor F (k := k) q ⊠ S) : ℝ)
      ≤ (⌊(q : ℝ) * φ.toFun S⌋₊ : ℝ) := by exact_mod_cast hbound
    _ ≤ (q : ℝ) * φ.toFun S := Nat.floor_le hqφ_nonneg

/-! ## Kron-power law for `asympSubrank`.

Note the exponent: `kronPowNat T 0 = T` (the base copy), so
`kronPowNat T n = T^{⊠(n+1)}` (`n+1` factors) and the power law reads

  `asympSubrank (kronPowNat T n) = asympSubrank T ^ (n+1)`.

(At `n = 0` both sides are `asympSubrank T`.) -/

/-- **Kron-power law for the asymptotic subrank** (Fekete; paper tex:974).

`asympSubrank (kronPowNat T n) = asympSubrank T ^ (n+1)` — note the `n+1`
exponent (see the section docstring).  This is the multiplicativity of `Q̃`
under Kronecker powers (`Q̃(T^{⊠m}) = Q̃(T)^m`, Fekete).

The concrete `asympSubrank` (`MaxRankBound.lean`, tex:974; root index
`1/(n+1)` matching the `(n+1)`-fold power) is the standard `Q̃`, and
the proof uses the concrete↔abstract bridge:
* `SpectrumBridge.asympSubrank_eq_abstract`: `asympSubrank S = pF.asympSubrank (mk S)`;
* `SpectrumBridge.mkPow`: `mk (kronPowNat T n) = (mk T)^(n+1)`;
* `SpectrumBridge.asympSubrank_pow_abstract`: the abstract Fekete power law
  `pF.asympSubrank (a^m) = pF.asympSubrank a ^ m` for `1 ≤_P a`, `m ≥ 1`.

HYPOTHESES.  Needs `2 ≤ k` (for the bridge's two-distinct-legs `BddAbove`) and the
genuine Fekete precondition `mk ⟨d,T⟩ ≠ 0` (equivalently `1 ≤_P T`): the power law
fundamentally requires `1 ≤_P a`, mirroring the abstract `asympSubrank_pow_abstract`
hypothesis.  These hypotheses match the later use in T4. -/
theorem asympSubrank_kronPowNat [NeZero k] (hk : 2 ≤ k) {d : Fin k → ℕ+}
    (T : KTensor F d) (hT : TensorClass.mk ⟨d, T⟩ ≠ (0 : TensorClass F k)) (n : ℕ) :
    asympSubrank (kronPowNat T n) = asympSubrank T ^ (n + 1) := by
  classical
  set pF := tensorStrassenPreorder (F := F) hk with hpF
  set a : TensorClass F k := TensorClass.mk ⟨d, T⟩ with ha
  -- `1 ≤_P a` for nonzero `T`.
  have h1a : pF.rel 1 a := by
    rw [ha, hpF, TensorClass.one_def]
    exact unitTensor_one_restricts_of_ne_zero T hT
  -- Bridge `asympSubrank (kronPowNat T n) = pF.asympSubrank (a^(n+1))`.
  have hLHS : asympSubrank (kronPowNat T n)
      = pF.asympSubrank (a ^ (n + 1)) := by
    rw [asympSubrank_eq_abstract hk (kronPowNat T n), ← hpF]
    congr 1
    rw [← mkPow T n]
  -- Abstract power law `pF.asympSubrank (a^(n+1)) = pF.asympSubrank a ^ (n+1)`.
  have hpow : pF.asympSubrank (a ^ (n + 1)) = pF.asympSubrank a ^ (n + 1) :=
    asympSubrank_pow_abstract pF h1a (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  -- Bridge back: `pF.asympSubrank a = asympSubrank T`.
  have hRHS : pF.asympSubrank a = asympSubrank T := by
    rw [ha, ← asympSubrank_eq_abstract hk T]
  rw [hLHS, hpow, hRHS]

/-! ## T3 — the CORRECT unit-overhead lemma. -/

/-- **T3 — the correct unit-overhead lemma** (Strassen 1988; paper tex:976-996).

  `subrank (⟨q⟩ ⊠ S) ≤ q · asympSubrank S`     (as reals).

This is the corrected `(★)`: the RHS is the **asymptotic** subrank, NOT the
finite subrank.  The finite-RHS form `subrank (⟨q⟩ ⊠ S) ≤ q · subrank S` is FALSE
(`⟨q⟩ ⊠ S = ⊕^q S` and subrank is super-additive under `⊕`; Derksen–Makam–Zuiddam
counterexample — see the module docstring).

Proof idea.  T1 gives `subrank (⟨q⟩ ⊠ S) ≤ q · φ(S)` for
*every* concrete spectral point `φ`, hence
`subrank (⟨q⟩ ⊠ S) / q ≤ ⨅_φ φ(S)` (`le_ciInf`).  The KTensor asymptotic-spectrum
duality is supplied by `AsymptoticSubrank/SpectrumBridge.lean`'s
`iInf_concrete_le_asympSubrank`: `(⨅_(concrete φ) φ(S)) ≤ asympSubrank S`.  Multiply
by `q`.

The bridge (`SpectrumBridge.lean`) instantiates Strassen-1988 duality at KTensor:
* `subrank_eq_abstract`: `subrank S = (tensorStrassenPreorder hk).subrank (mk ⟨d,S⟩)`.
* `asympSubrank_eq_abstract`:
  `(tensorStrassenPreorder hk).asympSubrank (mk S) = asympSubrank S` for the
  concrete `asympSubrank` of `MaxRankBound.lean` tex:974.  The directional `≤` half
  (`abstract_asympSubrank_le_concrete`) is what is consumed here.
* **duality** `iInf_concrete_le_abstract_asympSubrank`: via the abstract
  `asympSubrank_eq_iInf_spectrum` (`SpectrumDuality.lean:332`), `Nonempty
  (AsymptoticSpectrum _)` from `tensorClass_nontrivial`, and translating each
  abstract spectral point back to a concrete one with `ofAbstractSpectralPoint`.

GAPPEDNESS HYPOTHESIS (`hgap`).  The abstract duality `asympSubrank_eq_iInf_spectrum`
genuinely requires `IsGapped` (the `inf ≤ asympSubrank` direction can fail without it
— that is the entire point of gappedness in Strassen's framework).  The remaining,
honestly-documented gap is the *non-gapped nonzero* case: a nonzero `S` with `S ≁ₜ ⟨1⟩`
and `subrank (S^{⊠k}) = 1` for all `k` (so `asympSubrank S = 1`), for which closing
`subrank (⟨q⟩ ⊠ S) ≤ q` elementarily amounts to the open "subrank-1-stable ⟹ unit"
question.  Rather than add a spurious hypothesis silently or a custom axiom, `hgap`
makes the genuine precondition explicit; every gapped (in particular every strictly
gapped, and every `∼ₜ`-`⟨0⟩`/`⟨1⟩`) `S` is covered proved.  `hgap` was
`[NeZero k]` before; the bridge requires `2 ≤ k` (which T4 already supplies). -/
theorem subrank_unitKron_le_mul_asympSubrank [NeZero k] (hk : 2 ≤ k)
    (q : ℕ+) {d : Fin k → ℕ+} (S : KTensor F d)
    (hgap : (tensorStrassenPreorder (F := F) hk).IsGapped (TensorClass.mk ⟨d, S⟩)) :
    (subrank (unitTensor F (k := k) q ⊠ S) : ℝ) ≤ (q : ℝ) * asympSubrank S := by
  classical
  -- The concrete spectral-point family is nonempty (so `⨅` is a genuine `ciInf`).
  haveI : Nontrivial (TensorClass F k) := tensorClass_nontrivial hk
  haveI hne : Nonempty (AsymptoticSpectrum (tensorStrassenPreorder (F := F) hk)) :=
    AsymptoticSpectrum.nonempty _
  haveI : Nonempty (SpectralPoint k F) :=
    ⟨ofAbstractSpectralPoint (K := F) hk hne.some⟩
  -- Every concrete `φ(S) ≥ 0`, so `⨅ φ φ(S)` is bounded below.
  have hbdd : BddBelow (Set.range (fun φ : SpectralPoint k F => φ.toFun S)) := by
    refine ⟨0, ?_⟩
    rintro y ⟨φ, rfl⟩
    exact SpectralPoint.toFun_nonneg φ S
  -- T1 over every concrete `φ`, recast as `(subrank … : ℝ) / q ≤ φ(S)`.
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.pos
  have hdiv_le : ∀ φ : SpectralPoint k F,
      (subrank (unitTensor F (k := k) q ⊠ S) : ℝ) / (q : ℝ) ≤ φ.toFun S := by
    intro φ
    rw [div_le_iff₀ hqpos, mul_comm]
    exact subrank_unitKron_le_spectralPoint φ q S
  -- Hence `subrank/q ≤ ⨅ φ φ(S) ≤ asympSubrank S`, i.e. `subrank ≤ q · asympSubrank S`.
  have hinf : (subrank (unitTensor F (k := k) q ⊠ S) : ℝ) / (q : ℝ)
      ≤ ⨅ φ : SpectralPoint k F, φ.toFun S :=
    le_ciInf hdiv_le
  have hbridge : (⨅ φ : SpectralPoint k F, φ.toFun S) ≤ asympSubrank S :=
    iInf_concrete_le_asympSubrank hk S hgap
  rw [div_le_iff₀ hqpos] at hinf
  calc (subrank (unitTensor F (k := k) q ⊠ S) : ℝ)
      ≤ (⨅ φ : SpectralPoint k F, φ.toFun S) * (q : ℝ) := hinf
    _ = (q : ℝ) * (⨅ φ : SpectralPoint k F, φ.toFun S) := by ring
    _ ≤ (q : ℝ) * asympSubrank S := by
        apply mul_le_mul_of_nonneg_left hbridge (le_of_lt hqpos)

/-! ## T4 — the washout-ready consumer form. -/

/-- **T4 — washout-ready unit-overhead bound** (paper tex:976-996).

If `⟨a⟩ ≤ₜ ⟨q⟩ ⊠ kronPowNat T n`, then `(a : ℝ) ≤ q · asympSubrank (kronPowNat T n)`.

This is T3 specialized to `S = kronPowNat T n`, prepended with `a ≤ subrank(…)`
(a witness restriction puts `a` in the subrank set).  It is the form the Cor 3.5
consumers (`FieldInvariance.lean`, `BorderSubrank.lean`) call after their
`M → ∞` Fekete washout has produced a single restriction
`⟨a⟩ ≤ ⟨q⟩ ⊠ kronPowNat T n`.

The RHS is left as `asympSubrank (kronPowNat T n)` (NOT rewritten to
`asympSubrank T ^ (n+1)` via T2) to keep this consumer form independent of T2's
nonzero/`2 ≤ k` hypotheses.  Consumers wanting the explicit power form may
post-compose with `asympSubrank_kronPowNat`. -/
theorem subrank_of_restricts_unit_overhead [NeZero k] (hk : 2 ≤ k)
    (a q : ℕ+) {d : Fin k → ℕ+} (T : KTensor F d) (n : ℕ)
    (hgap : (tensorStrassenPreorder (F := F) hk).IsGapped
      (TensorClass.mk ⟨_, kronPowNat T n⟩))
    (h : Restricts (unitTensor F (k := k) a) (unitTensor F (k := k) q ⊠ kronPowNat T n)) :
    (a : ℝ) ≤ (q : ℝ) * asympSubrank (kronPowNat T n) := by
  classical
  -- Two distinct legs `0 ≠ 1` (from `2 ≤ k`) for the `BddAbove` of the subrank set.
  have h0 : (0 : ℕ) < k := by omega
  have h1 : (1 : ℕ) < k := by omega
  set i₀ : Fin k := ⟨0, h0⟩
  set i₁ : Fin k := ⟨1, h1⟩
  have hne : i₁ ≠ i₀ := by
    simp only [i₀, i₁, Ne, Fin.mk.injEq]; omega
  -- `a` is a positive witness in the subrank set of `⟨q⟩ ⊠ kronPowNat T n`.
  have hmem : (a : ℕ) ∈ { r : ℕ | ∃ hr : 0 < r,
      Restricts (unitTensor F (k := k) ⟨r, hr⟩)
        (unitTensor F (k := k) q ⊠ kronPowNat T n) } := by
    refine ⟨a.pos, ?_⟩
    -- `⟨(a : ℕ), a.pos⟩ = a` as `ℕ+`.
    simpa using h
  -- Hence `a ≤ subrank (⟨q⟩ ⊠ kronPowNat T n)`.
  have ha_le : (a : ℕ) ≤ subrank (unitTensor F (k := k) q ⊠ kronPowNat T n) :=
    le_csSup (subrank_set_bddAbove' i₀ i₁ hne _) hmem
  -- Combine with T3.
  calc (a : ℝ)
      ≤ (subrank (unitTensor F (k := k) q ⊠ kronPowNat T n) : ℝ) := by exact_mod_cast ha_le
    _ ≤ (q : ℝ) * asympSubrank (kronPowNat T n) :=
        subrank_unitKron_le_mul_asympSubrank hk q (kronPowNat T n) hgap

/-! ## Lemma A (survey `th:examples-gapped`, tex:2286-2297) — the flattening
gappedness criterion over an infinite field.

The survey proof (tex:2296-2297): "for tensors … either there is a flattening
rank of one, or `T² ≥_P 2`. Namely, … if every flattening rank is at least two,
then `T ≥_P 𝕄_{2,1,1}` and `T ≥_P 𝕄_{1,2,1}`, and so
`T² ≥ 𝕄_{2,1,1} 𝕄_{1,2,1} = 𝕄_{2,2,1} ≥_P 2`."

We formalize the contrapositive of the "subrank-1-stable ⟹ unit" statement via
Theorem 3.2 (`subrankPair_prod_ge_flatRank`).  Over an **infinite** field the
cardinality hypothesis `(flatRank S I : Cardinal) < #F` of Theorem 3.2 is
automatic (`flatRank S I < ℵ₀ ≤ #F`), exactly the regime of Cor 3.5 (GOR field
`ℚ`/`ℝ`/`ℂ` + algebraic extensions). -/

/-- For `2 ≤ k`, `subrank S ≤ flatRank S {i₀}` (any leg `i₀` admitting a distinct
    `i₁ ≠ i₀`): the `subrank` `sSup`-set is bounded member-wise by `flatRank S {i₀}`
    (`subrank_set_bddAbove'`). -/
lemma subrank_le_flatRank_singleton {d : Fin k → ℕ+}
    (i₀ i₁ : Fin k) (hne : i₁ ≠ i₀) (S : KTensor F d) :
    subrank S ≤ flatRank S {i₀} := by
  classical
  unfold subrank
  refine csSup_le' ?_
  rintro r ⟨hr, hres⟩
  calc r ≤ flatRank (unitTensor F (k := k) ⟨r, hr⟩) {i₀} :=
        unitTensor_flatRank_singleton_ge' i₀ i₁ hne hr
    _ ≤ flatRank S {i₀} := hres.flatRank_le {i₀}

/-- If an `r × r` submatrix of `M` equals the identity, then `r ≤ M.rank`.  Stated
    over an **abstract** matrix `M` (with abstract index types) so that the rank
    bound `Matrix.rank_submatrix_le` never whnf-unfolds a heavy concrete flattening
    matrix at the call site. -/
private lemma rank_ge_of_submatrix_eq_one {R : Type*} [CommRing R] [Nontrivial R]
    {ι κ : Type*} [Fintype κ] {r : ℕ} (M : Matrix ι κ R)
    (f : Fin r → ι) (e : Fin r → κ) (hM : M.submatrix f e = (1 : Matrix (Fin r) (Fin r) R)) :
    r ≤ M.rank := by
  -- `rank` ≤-bound for an arbitrary (non-`Equiv`) row/col selection, via `eRank`
  -- (Mathlib's `rank_submatrix_le` requires the column reindex to be an `Equiv`,
  -- which fails for `|Scut| ≥ 2`; the `eRank` lemma is the general-function form).
  have hsubr : (M.submatrix f e).rank ≤ M.rank := by
    have hle : (M.submatrix f e).eRank ≤ M.eRank := Matrix.eRank_submatrix_le M f e
    have hfin : M.eRank ≠ ⊤ :=
      ne_top_of_le_ne_top (ENat.coe_ne_top (Fintype.card κ))
        (by rw [← ENat.card_eq_coe_fintype_card]; exact Matrix.eRank_le_card_width M)
    simpa only [Matrix.eRank_toNat_eq_rank] using ENat.toNat_le_toNat hle hfin
  rwa [hM, Matrix.rank_one, Fintype.card_fin] at hsubr

/-- **General-cut unit flattening lower bound**: for any *bipartition* cut `S`
    (some `i₀ ∈ S`, some `i₁ ∈ Sᶜ`), `r ≤ flatRank (⟨r⟩) S`.  The `S`-flattening of the
    rank-`r` GHZ unit contains the `r × r` identity submatrix: rows set every leg in
    `S` to a common value `m`, columns set every leg outside `S` to a common value
    `v`, and the unit entry is `1` iff `m = v` (all legs agree).  This is the
    bipartition generalization of `unitTensor_flatRank_singleton_ge'`. -/
lemma unitTensor_flatRank_cut_ge
    (Scut : Finset (Fin k)) {i₀ i₁ : Fin k} (hi₀ : i₀ ∈ Scut) (hi₁ : i₁ ∉ Scut)
    {r : ℕ} (hr : 0 < r) :
    r ≤ flatRank (unitTensor F (k := k) ⟨r, hr⟩) Scut := by
  classical
  set U : KTensor F (fun _ : Fin k => (⟨r, hr⟩ : ℕ+)) := unitTensor F (k := k) ⟨r, hr⟩
  -- Row map: value `m` to every leg in `Scut`.  Col map: value `v` to every leg ∉ `Scut`.
  -- (Plain constant-embeddings, NOT `Equiv`s — for `|Scut| ≥ 2` they are not
  -- surjective; `Matrix.rank_submatrix_le` accepts any index function.)
  let eRow : Fin r → ((x : {x // x ∈ Scut}) → Fin r) := fun m _ => m
  let cmap : Fin r → ((x : {x // x ∉ Scut}) → Fin r) := fun v _ => v
  have hsub : (flattenMatrix U Scut).submatrix eRow cmap = (1 : Matrix (Fin r) (Fin r) F) := by
    ext m v
    rw [Matrix.submatrix_apply, Matrix.one_apply]
    simp only [flattenMatrix, U, unitTensor]
    set g : Fin k → Fin r := fun x => if h : x ∈ Scut
      then (eRow m ⟨x, h⟩ : Fin r) else (cmap v ⟨x, h⟩ : Fin r) with hg
    change (if ∀ a b : Fin k, g a = g b then (1 : F) else 0) = if m = v then 1 else 0
    have hmerge : ∀ a : Fin k, g a = if a ∈ Scut then m else v := by
      intro a; simp only [hg]
      by_cases ha : a ∈ Scut
      · rw [dif_pos ha, if_pos ha]
      · rw [dif_neg ha, if_neg ha]
    have hval_i0 : g i₀ = m := by rw [hmerge i₀, if_pos hi₀]
    have hval_i1 : g i₁ = v := by rw [hmerge i₁, if_neg hi₁]
    have hpred : (∀ a b : Fin k, g a = g b) ↔ m = v := by
      constructor
      · intro hall; have h2 := hall i₀ i₁; rwa [hval_i0, hval_i1] at h2
      · intro hmv a b; rw [hmerge a, hmerge b]; split <;> split <;> simp_all
    by_cases hmv : m = v
    · rw [if_pos (hpred.mpr hmv), if_pos hmv]
    · rw [if_neg (fun h => hmv (hpred.mp h)), if_neg hmv]
  -- `r ≤ (flattenMatrix U Scut).rank = flatRank U Scut` via the abstract-matrix helper
  -- (avoids whnf-unfolding the unit tensor inside `rank_submatrix_le`).
  exact rank_ge_of_submatrix_eq_one (flattenMatrix U Scut) eRow cmap hsub

/-- **`subrank ≤ flatRank` along any bipartition cut**: `subrank T ≤ flatRank T Scut`
    for a cut with `i₀ ∈ Scut`, `i₁ ∉ Scut` — the `subrank` `sSup`-set is bounded
    member-wise via `unitTensor_flatRank_cut_ge` + restriction monotonicity.  This is
    the bipartition generalization of `subrank_le_flatRank_singleton`. -/
lemma subrank_le_flatRank_cut {d : Fin k → ℕ+}
    (Scut : Finset (Fin k)) {i₀ i₁ : Fin k} (hi₀ : i₀ ∈ Scut) (hi₁ : i₁ ∉ Scut)
    (T : KTensor F d) :
    subrank T ≤ flatRank T Scut := by
  classical
  unfold subrank
  refine csSup_le' ?_
  rintro r ⟨hr, hres⟩
  calc r ≤ flatRank (unitTensor F (k := k) ⟨r, hr⟩) Scut :=
        unitTensor_flatRank_cut_ge Scut hi₀ hi₁ hr
    _ ≤ flatRank T Scut := hres.flatRank_le Scut

/-- Over an **infinite** field the Theorem 3.2 cardinality hypothesis is automatic:
    `(flatRank S I : Cardinal) < #F`, since `flatRank S I < ℵ₀ ≤ #F`. -/
lemma flatRank_lt_card_of_infinite [Infinite F] {d : Fin k → ℕ+}
    (S : KTensor F d) (I : Finset (Fin k)) :
    ((flatRank S I : ℕ) : Cardinal) < Cardinal.mk F :=
  (Cardinal.natCast_lt_aleph0).trans_le (Cardinal.aleph0_le_mk F)

/-- If the singleton flattening at `i` has rank at least two, then the
    field-general crossing-pair extraction gives a rank-2 pair-unit restriction
    on some pair incident with `i`. -/
private lemma exists_subrankPair_ge_two_of_flatRank_singleton_ge_two
    (hk : 2 ≤ k) {d : Fin k → ℕ+} (S : KTensor F d) (i : Fin k)
    (h2i : 2 ≤ flatRank S {i}) :
    ∃ j : Fin k, i ≠ j ∧ 2 ≤ subrankPair S i j := by
  classical
  have hsingleton_ne_univ : ({i} : Finset (Fin k)) ≠ Finset.univ := by
    intro h
    have hcard : k = 1 := by
      calc
        k = (Finset.univ : Finset (Fin k)).card := by simp
        _ = ({i} : Finset (Fin k)).card := by rw [← h]
        _ = 1 := by simp
    omega
  obtain ⟨i', hi', j, _hj, hij, hpair⟩ :=
    exists_crossing_pair_of_flatRank_cut_ge_two_anyField hk S ({i} : Finset (Fin k))
      ⟨i, Finset.mem_singleton_self i⟩ hsingleton_ne_univ h2i
  rw [Finset.mem_singleton] at hi'
  subst i'
  exact ⟨j, hij, hpair⟩

/-- A rank-`≥ 2` pair-subrank gives a concrete rank-2 pair-unit restriction. -/
private lemma unitPairTensor_two_restricts_of_subrankPair_ge_two {d : Fin k → ℕ+}
    (S : KTensor F d) (i j : Fin k) (hij : i ≠ j)
    (hij2 : 2 ≤ subrankPair S i j) :
    Restricts (unitPairTensor (F := F) (⟨2, two_pos⟩ : ℕ+) i j hij) S := by
  have hpos : 0 < subrankPair S i j := by omega
  have hle : ((⟨2, two_pos⟩ : ℕ+) : ℕ)
      ≤ ((⟨subrankPair S i j, hpos⟩ : ℕ+) : ℕ) := hij2
  exact (unitPairTensor_restricts_of_le (F := F) i j hij hle).trans
    (subrankPair_unitPair_restricts S i j hij hpos)

/-! ## The TRUE all-bipartition Lemma A via leg-by-leg GHZ extension.

A singleton-hypothesis form using a per-leg pair-unit fold is FALSE: a pair-unit
`⟨2⟩_{i, jfun i} ≤ₜ S` on every leg only
forces index agreement within each connected component of the partner graph, NOT
the global GHZ equality `⟨2⟩` demands (counterexample `k=4`, `S = ⟨2⟩_{0,1} ⊠
⟨2⟩_{2,3}`).

The survey (`th:examples-gapped`, tex:2286-2297) says "every flattening rank" —
meaning every bipartition `∅ ≠ I ⊊ [k]`, NOT just singletons.  We formalize the
TRUE statement via a leg-by-leg GHZ-extension induction on a *partial* GHZ tensor:
starting from a base pair `⟨2⟩_{i₀,j₀}` we merge one fresh leg at a time, each
merge supplied by Theorem 3.2 applied to the *current cut* `S` (which has
`flatRank ≥ 2` by hypothesis since `S ≠ univ`).  The fresh leg `j` is the partner
the cut-extraction hands us — so connectivity is automatic and the counterexample
cannot recur (the hypothesis `i ∈ S` for the merge is what makes it sound). -/

/-- **Partial GHZ format**: `2` on legs in `S`, `1` elsewhere. -/
def partialUnitFormat {k : ℕ} (S : Finset (Fin k)) : Fin k → ℕ+ :=
  fun i => if i ∈ S then (2 : ℕ+) else 1

/-- **Partial GHZ tensor** `partialUnitTensor S` (survey tex:2286-2297): the entry
    at `idx` is `1` iff all coordinates at legs in `S` agree (as naturals), else
    `0`.  Legs outside `S` are `Fin 1`-valued so contribute no constraint.

    At `S = univ` this is the full rank-2 unit `⟨2⟩` (up to the format rewrite
    `if i ∈ univ then 2 else 1 = 2`); at `S = {i,j}` it is the pair-unit
    `⟨2⟩_{i,j}`. -/
noncomputable def partialUnitTensor {k : ℕ} (S : Finset (Fin k)) :
    KTensor F (partialUnitFormat S) :=
  fun idx => if ∀ i ∈ S, ∀ j ∈ S, (idx i).val = (idx j).val then 1 else 0

/-- `partialUnitTensor {i,j}` is the pair-unit `⟨2⟩_{i,j}` (same format, same
    values: "both leg-`i` and leg-`j` coords agree" = "the `{i,j}` block agrees"). -/
lemma partialUnitFormat_pair {k : ℕ} (i j : Fin k) (_hij : i ≠ j) :
    partialUnitFormat ({i, j} : Finset (Fin k)) = naturalPairFormat (2 : ℕ+) i j := by
  funext ℓ
  simp only [partialUnitFormat, naturalPairFormat, Finset.mem_insert, Finset.mem_singleton]

/-- `partialUnitTensor {i,j}` equals the pair-unit `⟨2⟩_{i,j}` after the format
    rewrite (`partialUnitFormat_pair`). -/
lemma partialUnitTensor_pair {k : ℕ} (i j : Fin k) (hij : i ≠ j) :
    (partialUnitFormat_pair i j hij) ▸ (partialUnitTensor (F := F) ({i, j} : Finset (Fin k)))
      = unitPairTensor (F := F) (2 : ℕ+) i j hij := by
  classical
  have key : ∀ (d' : Fin k → ℕ+) (hd : partialUnitFormat ({i, j} : Finset (Fin k)) = d'),
      hd ▸ (partialUnitTensor (F := F) ({i, j} : Finset (Fin k)))
        = fun idx => (partialUnitTensor (F := F) ({i, j} : Finset (Fin k)))
            (fun ℓ => (congrFun hd ℓ).symm ▸ idx ℓ) := by
    intro d' hd; subst hd; rfl
  rw [key (naturalPairFormat (2 : ℕ+) i j) (partialUnitFormat_pair i j hij)]
  funext idx
  simp only [partialUnitTensor, unitPairTensor]
  have hval : ∀ (ℓ : Fin k),
      (((congrFun (partialUnitFormat_pair i j hij) ℓ).symm ▸ idx ℓ : _)).val
        = (idx ℓ).val := by
    intro ℓ
    rw [eqRec_eq_cast, ← Fin.cast_eq_cast (congrArg (fun m : ℕ+ => (m : ℕ))
      (congrFun (partialUnitFormat_pair i j hij) ℓ).symm), Fin.val_cast]
  -- LHS predicate: ∀ a ∈ {i,j}, ∀ b ∈ {i,j}, coords agree; reduces to coord i = coord j.
  have hmem_i : i ∈ ({i, j} : Finset (Fin k)) := by simp
  have hmem_j : j ∈ ({i, j} : Finset (Fin k)) := by simp
  have hpred : (∀ a ∈ ({i, j} : Finset (Fin k)), ∀ b ∈ ({i, j} : Finset (Fin k)),
        (((congrFun (partialUnitFormat_pair i j hij) a).symm ▸ idx a : _)).val
          = (((congrFun (partialUnitFormat_pair i j hij) b).symm ▸ idx b : _)).val)
      ↔ (idx i).val = (idx j).val := by
    constructor
    · intro h; have := h i hmem_i j hmem_j; rwa [hval i, hval j] at this
    · intro h a ha b hb
      rw [hval a, hval b]
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all
  by_cases h : (idx i).val = (idx j).val
  · rw [if_pos (hpred.mpr h), if_pos h]
  · rw [if_neg (fun hc => h (hpred.mp hc)), if_neg h]

/-- `partialUnitTensor univ` is the full rank-2 unit `⟨2⟩` (same format after the
    rewrite `if i ∈ univ then 2 else 1 = 2`, same values). -/
lemma partialUnitFormat_univ {k : ℕ} :
    partialUnitFormat (Finset.univ : Finset (Fin k)) = (fun _ => (2 : ℕ+)) := by
  funext ℓ; simp [partialUnitFormat]

lemma partialUnitTensor_univ {k : ℕ} :
    (partialUnitFormat_univ (k := k)) ▸ (partialUnitTensor (F := F) (Finset.univ : Finset (Fin k)))
      = unitTensor F (k := k) (2 : ℕ+) := by
  classical
  have key : ∀ (d' : Fin k → ℕ+) (hd : partialUnitFormat (Finset.univ : Finset (Fin k)) = d'),
      hd ▸ (partialUnitTensor (F := F) (Finset.univ : Finset (Fin k)))
        = fun idx => (partialUnitTensor (F := F) (Finset.univ : Finset (Fin k)))
            (fun ℓ => (congrFun hd ℓ).symm ▸ idx ℓ) := by
    intro d' hd; subst hd; rfl
  rw [key (fun _ => (2 : ℕ+)) (partialUnitFormat_univ (k := k))]
  funext idx
  simp only [partialUnitTensor, unitTensor]
  have hval : ∀ (ℓ : Fin k),
      (((congrFun (partialUnitFormat_univ (k := k)) ℓ).symm ▸ idx ℓ : _)).val = (idx ℓ).val := by
    intro ℓ
    rw [eqRec_eq_cast, ← Fin.cast_eq_cast (congrArg (fun m : ℕ+ => (m : ℕ))
      (congrFun (partialUnitFormat_univ (k := k)) ℓ).symm), Fin.val_cast]
  have hpred : (∀ a ∈ (Finset.univ : Finset (Fin k)), ∀ b ∈ (Finset.univ : Finset (Fin k)),
        (((congrFun (partialUnitFormat_univ (k := k)) a).symm ▸ idx a : _)).val
          = (((congrFun (partialUnitFormat_univ (k := k)) b).symm ▸ idx b : _)).val)
      ↔ (∀ a b : Fin k, idx a = idx b) := by
    constructor
    · intro h a b
      have := h a (Finset.mem_univ a) b (Finset.mem_univ b)
      rw [hval a, hval b] at this; exact Fin.ext this
    · intro h a _ b _; rw [hval a, hval b, h a b]
  by_cases h : ∀ a b : Fin k, idx a = idx b
  · rw [if_pos (hpred.mpr h), if_pos h]
  · rw [if_neg (fun hc => h (hpred.mp hc)), if_neg h]

/-- **GHZ extension step** (survey tex:2286-2297, the crux).

Given a leg `i ∈ S`, a fresh leg `j ∉ S` with `i ≠ j`, the partial GHZ tensor on
`insert j S` restricts (after a format rewrite) the Kronecker product of the
partial GHZ tensor on `S` with the pair-unit `⟨2⟩_{i,j}`:

  `partialUnitTensor (insert j S) ≤ₜ partialUnitTensor S ⊠ ⟨2⟩_{i,j}`.

Restriction matrices (`Restricts` direction `LHS ≤ₜ RHS`): on leg `i`, the
diagonal merge `Fin 2 → Fin (2·2)` selecting `(a, a)` (both the `S`-coord and the
pair-coord equal the merged coord `a`); on leg `j`, project the pair-coord
`Fin 2 → Fin (1·2)`; on legs in `S \ {i}`, identity `Fin 2 → Fin (2·1)`; on legs
outside, trivial `Fin 1 → Fin 1`.

The contraction collapses (`Finset.sum_eq_single`) to a single RHS index, whose
value is `[S-block agrees] · [coord i = coord j]`; with `i ∈ S` this is exactly
`[insert j S block agrees]`.  The `i ∈ S` hypothesis is load-bearing: it forces
the pair leg `j` to be tied (through leg `i`) to the whole `S`-block, so the
disconnected-partner-graph counterexample cannot recur. -/
theorem ghz_extend {k : ℕ} {S : Finset (Fin k)} {i j : Fin k}
    (hiS : i ∈ S) (hjS : j ∉ S) (hij : i ≠ j) :
    Restricts
      (partialUnitTensor (F := F) (insert j S))
      ((partialUnitTensor (F := F) S) ⊠ (unitPairTensor (F := F) (2 : ℕ+) i j hij)) := by
  classical
  -- Format dimension facts.  `dL ℓ = 2 ↔ ℓ ∈ insert j S`; `dS ℓ = 2 ↔ ℓ ∈ S`;
  -- `dP ℓ = 2 ↔ ℓ = i ∨ ℓ = j`.  Throughout we work with `.val`s in `ℕ`.
  have hdimL : ∀ ℓ, ((partialUnitFormat (insert j S) ℓ : ℕ+) : ℕ)
      = if ℓ ∈ insert j S then 2 else 1 := by
    intro ℓ; simp only [partialUnitFormat]; split <;> rfl
  have hdimS : ∀ ℓ, ((partialUnitFormat S ℓ : ℕ+) : ℕ) = if ℓ ∈ S then 2 else 1 := by
    intro ℓ; simp only [partialUnitFormat]; split <;> rfl
  have hdimP : ∀ ℓ, ((naturalPairFormat (2 : ℕ+) i j ℓ : ℕ+) : ℕ)
      = if ℓ = i ∨ ℓ = j then 2 else 1 := by
    intro ℓ; simp only [naturalPairFormat]; split <;> rfl
  -- Clamp the merged coordinate `a : Fin (dL ℓ)` to each factor dimension.
  -- `clampVal ℓ a (cond)` = `a.val` if `cond` (factor is 2-dim), else `0`.
  -- The clamped value is `< (factor dim)` in both cases.
  -- Leg-wise restriction matrices.  Entry is `1` iff `b` decodes to the clamped
  -- `(a, a)` on the two factors, else `0`.
  refine ⟨fun ℓ (a : Fin ((partialUnitFormat (insert j S) ℓ : ℕ+) : ℕ))
      (b : Fin ((partialUnitFormat S ℓ * naturalPairFormat (2 : ℕ+) i j ℓ : ℕ+) : ℕ)) =>
    if (kronDecodeL (d₁ := partialUnitFormat S ℓ) (d₂ := naturalPairFormat (2 : ℕ+) i j ℓ) b).val
          = (if ℓ ∈ S then a.val else 0)
        ∧ (kronDecodeR (d₁ := partialUnitFormat S ℓ) (d₂ := naturalPairFormat (2 : ℕ+) i j ℓ) b).val
          = (if ℓ = i ∨ ℓ = j then a.val else 0)
      then (1 : F) else 0, ?_⟩
  intro jdx
  -- Each leg's merged coord `jdx ℓ` is `< 2` whenever the relevant factor is 2-dim.
  have hjlt : ∀ ℓ, (jdx ℓ).val < (if ℓ ∈ insert j S then 2 else 1) := by
    intro ℓ; rw [← hdimL ℓ]; exact (jdx ℓ).isLt
  -- The unique contributing RHS index `idxJ`: on leg `ℓ`, encode `(clampS, clampP)`.
  -- We give its decoded-value characterization and build it via `kronDecodeEquiv.symm`.
  set clampS : ∀ ℓ, Fin ((partialUnitFormat S ℓ : ℕ+) : ℕ) := fun ℓ =>
    ⟨if ℓ ∈ S then (jdx ℓ).val else 0, by
      rw [hdimS ℓ]
      by_cases hℓ : ℓ ∈ S
      · rw [if_pos hℓ, if_pos hℓ]
        have hmem : ℓ ∈ insert j S := Finset.mem_insert_of_mem hℓ
        have hlt := hjlt ℓ; rw [if_pos hmem] at hlt; exact hlt
      · rw [if_neg hℓ, if_neg hℓ]; norm_num⟩ with hclampS
  set clampP : ∀ ℓ, Fin ((naturalPairFormat (2 : ℕ+) i j ℓ : ℕ+) : ℕ) := fun ℓ =>
    ⟨if ℓ = i ∨ ℓ = j then (jdx ℓ).val else 0, by
      rw [hdimP ℓ]
      by_cases hℓ : ℓ = i ∨ ℓ = j
      · rw [if_pos hℓ, if_pos hℓ]
        have hmem : ℓ ∈ insert j S := by
          rcases hℓ with rfl | rfl
          · exact Finset.mem_insert_of_mem hiS
          · exact Finset.mem_insert_self _ _
        have hlt := hjlt ℓ; rw [if_pos hmem] at hlt; exact hlt
      · rw [if_neg hℓ, if_neg hℓ]; norm_num⟩ with hclampP
  set idxJ : ∀ ℓ, Fin ((partialUnitFormat S ℓ * naturalPairFormat (2 : ℕ+) i j ℓ : ℕ+) : ℕ) :=
    fun ℓ => (kronDecodeEquiv (d₁ := partialUnitFormat S ℓ)
      (d₂ := naturalPairFormat (2 : ℕ+) i j ℓ)).symm (clampS ℓ, clampP ℓ) with hidxJ
  -- Decode facts for `idxJ`.
  have hdecL : ∀ ℓ, kronDecodeL (idxJ ℓ) = clampS ℓ := by
    intro ℓ
    have : kronDecodeEquiv (idxJ ℓ) = (clampS ℓ, clampP ℓ) := by
      rw [hidxJ]; exact Equiv.apply_symm_apply _ _
    rw [kronDecodeEquiv_apply] at this
    exact (Prod.ext_iff.mp this).1
  have hdecR : ∀ ℓ, kronDecodeR (idxJ ℓ) = clampP ℓ := by
    intro ℓ
    have : kronDecodeEquiv (idxJ ℓ) = (clampS ℓ, clampP ℓ) := by
      rw [hidxJ]; exact Equiv.apply_symm_apply _ _
    rw [kronDecodeEquiv_apply] at this
    exact (Prod.ext_iff.mp this).2
  -- Collapse the sum to the single term `idxJ`.
  rw [Finset.sum_eq_single idxJ]
  · -- Main term: product = 1, RHS value = LHS predicate.
    have hprod_one : (∏ ℓ, (if (kronDecodeL (idxJ ℓ)).val = (if ℓ ∈ S then (jdx ℓ).val else 0)
          ∧ (kronDecodeR (idxJ ℓ)).val = (if ℓ = i ∨ ℓ = j then (jdx ℓ).val else 0)
        then (1 : F) else 0)) = 1 := by
      apply Finset.prod_eq_one
      intro ℓ _
      rw [hdecL ℓ, hdecR ℓ]
      simp only [hclampS, hclampP, and_self, if_true]
    rw [hprod_one, one_mul]
    -- RHS tensor value at `idxJ`.
    change partialUnitTensor (insert j S) jdx
      = (partialUnitTensor S ⊠ unitPairTensor (2 : ℕ+) i j hij) idxJ
    rw [show (partialUnitTensor S ⊠ unitPairTensor (2 : ℕ+) i j hij) idxJ
        = partialUnitTensor S (kronLeftIndex idxJ)
          * unitPairTensor (2 : ℕ+) i j hij (kronRightIndex idxJ) from rfl]
    -- `kronLeftIndex idxJ = clampS`, `kronRightIndex idxJ = clampP` (value-wise).
    have hLI : ∀ ℓ, kronLeftIndex idxJ ℓ = clampS ℓ := by
      intro ℓ; rw [← kronDecodeL_eq_kronLeftIndex]; exact hdecL ℓ
    have hRI : ∀ ℓ, kronRightIndex idxJ ℓ = clampP ℓ := by
      intro ℓ; rw [← kronDecodeR_eq_kronRightIndex]; exact hdecR ℓ
    rw [show partialUnitTensor S (kronLeftIndex idxJ) = partialUnitTensor S clampS from by
        congr 1; funext ℓ; exact hLI ℓ,
      show unitPairTensor (2 : ℕ+) i j hij (kronRightIndex idxJ)
          = unitPairTensor (2 : ℕ+) i j hij clampP from by congr 1; funext ℓ; exact hRI ℓ]
    -- Evaluate both factors and the LHS.
    simp only [partialUnitTensor, unitPairTensor]
    -- Reduce the three predicates to facts about `jdx`-values.
    have hclampS_val : ∀ ℓ ∈ S, (clampS ℓ).val = (jdx ℓ).val := by
      intro ℓ hℓ; simp only [hclampS, if_pos hℓ]
    have hclampP_i : (clampP i).val = (jdx i).val := by
      simp only [hclampP]; simp
    have hclampP_j : (clampP j).val = (jdx j).val := by
      simp only [hclampP]; simp
    -- LHS predicate ⟺ S-block agrees ∧ coord i = coord j.
    by_cases hAll : ∀ a ∈ insert j S, ∀ b ∈ insert j S, (jdx a).val = (jdx b).val
    · rw [if_pos hAll]
      -- Both RHS factors are `1`.
      have hSagree : ∀ a ∈ S, ∀ b ∈ S, (clampS a).val = (clampS b).val := by
        intro a ha b hb
        rw [hclampS_val a ha, hclampS_val b hb]
        exact hAll a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb)
      have hPagree : (clampP i).val = (clampP j).val := by
        rw [hclampP_i, hclampP_j]
        exact hAll i (Finset.mem_insert_of_mem hiS) j (Finset.mem_insert_self _ _)
      rw [if_pos hSagree, if_pos hPagree, mul_one]
    · rw [if_neg hAll]
      -- At least one factor is `0`.  Push the negation: ∃ crossing disagreement.
      push_neg at hAll
      obtain ⟨a, ha, b, hb, hab⟩ := hAll
      -- Each of `a, b ∈ insert j S = S ∪ {j}`.  Show the product is 0 by cases.
      by_cases hSagree : ∀ x ∈ S, ∀ y ∈ S, (clampS x).val = (clampS y).val
      · -- S-block agrees, so the disagreement involves `j`; force coord i ≠ coord j.
        rw [if_pos hSagree]
        by_cases hPagree : (clampP i).val = (clampP j).val
        · -- coord i = coord j AND S-block agrees ⟹ insert j S block agrees (contra).
          exfalso
          rw [hclampP_i, hclampP_j] at hPagree
          have hStab : ∀ x ∈ S, ∀ y ∈ S, (jdx x).val = (jdx y).val := by
            intro x hx y hy
            have := hSagree x hx y hy
            rwa [hclampS_val x hx, hclampS_val y hy] at this
          -- coord of any S-element equals coord i (via S agreement), equals coord j.
          have hSj : ∀ x ∈ S, (jdx x).val = (jdx j).val := by
            intro x hx; rw [hStab x hx i hiS, hPagree]
          have hins : ∀ x ∈ insert j S, (jdx x).val = (jdx j).val := by
            intro x hx
            rw [Finset.mem_insert] at hx
            rcases hx with rfl | hx
            · rfl
            · exact hSj x hx
          exact hab ((hins a ha).trans (hins b hb).symm)
        · rw [if_neg hPagree, mul_zero]
      · rw [if_neg hSagree, zero_mul]
  · -- Off-term: any `idx ≠ idxJ` gives product = 0.
    intro idx _ hidx
    apply mul_eq_zero_of_left
    -- Some leg `ℓ` has `idx ℓ ≠ idxJ ℓ`, i.e. its decode ≠ (clampS, clampP), so the
    -- matrix entry is `0`.
    rw [Finset.prod_eq_zero_iff]
    by_contra hne
    push_neg at hne
    apply hidx
    funext ℓ
    have hℓ := hne ℓ (Finset.mem_univ ℓ)
    -- `hℓ`: the leg-`ℓ` matrix entry `≠ 0`, so the `if`-condition holds.
    by_cases hcond : (kronDecodeL (idx ℓ)).val = (if ℓ ∈ S then (jdx ℓ).val else 0)
        ∧ (kronDecodeR (idx ℓ)).val = (if ℓ = i ∨ ℓ = j then (jdx ℓ).val else 0)
    · -- Then `idx ℓ` decodes to `(clampS ℓ, clampP ℓ)`, hence `= idxJ ℓ`.
      have hdL' : kronDecodeL (idx ℓ) = clampS ℓ := by
        apply Fin.ext; rw [hcond.1, hclampS]
      have hdR' : kronDecodeR (idx ℓ) = clampP ℓ := by
        apply Fin.ext; rw [hcond.2, hclampP]
      have heq : kronDecodeEquiv (idx ℓ) = (clampS ℓ, clampP ℓ) := by
        rw [kronDecodeEquiv_apply, hdL', hdR']
      change idx ℓ = idxJ ℓ
      rw [hidxJ]
      change idx ℓ = kronDecodeEquiv.symm (clampS ℓ, clampP ℓ)
      rw [← heq, Equiv.symm_apply_apply]
    · exact absurd (if_neg hcond) hℓ
  · -- `idxJ ∈ univ` always, so this branch is vacuous.
    intro h; exact absurd (Finset.mem_univ _) h

set_option linter.unusedVariables false in
/-- **Per-cut Theorem 3.2 extraction** (survey tex:2286-2297).  If a *bipartition*
    cut `S` (nonempty, `≠ univ`) has flattening rank `≥ 2`, then some crossing pair
    `i ∈ S`, `j ∉ S` has `2 ≤ subrankPair T i j`.

    Proof is delegated to the field-general extraction in
    `CrossingPairAnyField`. -/
theorem exists_crossing_pair_of_flatRank_cut_ge_two
    (hk : 2 ≤ k) {d : Fin k → ℕ+} (T : KTensor F d) (S : Finset (Fin k))
    (hS : S.Nonempty) (hS' : S ≠ Finset.univ) (h2 : 2 ≤ flatRank T S) :
    ∃ i ∈ S, ∃ j ∉ S, ∃ hij : i ≠ j, 2 ≤ subrankPair T i j := by
  exact exists_crossing_pair_of_flatRank_cut_ge_two_anyField hk T S hS hS' h2

/-- **GHZ-extension `Restricts`-corollary**: feed `ghz_extend` a pair-unit
    `⟨2⟩_{i,j} ≤ₜ T` and a Kronecker-power restriction of the current partial unit,
    to extend by one leg.  `partialUnitTensor (insert j S) ≤ₜ
    partialUnitTensor S ⊠ ⟨2⟩_{i,j} ≤ₜ kronPowNat T m ⊠ T = kronPowNat T (m+1)`. -/
theorem partialUnit_extend_restricts {d : Fin k → ℕ+} (T : KTensor F d)
    {S : Finset (Fin k)} {i j : Fin k} (hiS : i ∈ S) (hjS : j ∉ S) (hij : i ≠ j)
    (hpair : Restricts (unitPairTensor (F := F) (2 : ℕ+) i j hij) T)
    {m : ℕ} (hpartial : Restricts (partialUnitTensor (F := F) S) (kronPowNat T m)) :
    Restricts (partialUnitTensor (F := F) (insert j S)) (kronPowNat T (m + 1)) := by
  have hkron : Restricts
      ((partialUnitTensor (F := F) S) ⊠ (unitPairTensor (F := F) (2 : ℕ+) i j hij))
      (kronPowNat T m ⊠ T) := Restricts.kron_congr hpartial hpair
  have hstep : (kronPowNat T m ⊠ T) = kronPowNat T (m + 1) := rfl
  exact (ghz_extend hiS hjS hij).trans (hstep ▸ hkron)

/-- **Lemma A (corrected, TRUE all-bipartition form)** (survey tex:2286-2297,
    `\label{th:examples-gapped}`).

If EVERY bipartition cut `S` (nonempty, `≠ univ`) has flattening rank `≥ 2`, then
some Kronecker power of `T` restricts the rank-2 unit `⟨2⟩`.

PROOF (survey tex:2296-2297, the leg-by-leg GHZ-extension realization).  Strong
induction growing the partial GHZ tensor one fresh leg at a time.  We first build a
*base pair* from the cut `{i₀}` (`flatRank ≥ 2` ⟹ crossing pair `i₀, j₀` with
`subrankPair ≥ 2` ⟹ `⟨2⟩_{i₀,j₀} ≤ₜ T`, i.e. `partialUnitTensor {i₀,j₀} ≤ₜ T =
kronPowNat T 0`).  Then, while the current set `S` is `≠ univ`, the cut `S` itself
has `flatRank ≥ 2` (hypothesis), yielding a crossing pair `i ∈ S`, `j ∉ S` with
`subrankPair ≥ 2`; `partialUnit_extend_restricts` (= `ghz_extend` + Kronecker
monotonicity) grows the restriction to `insert j S`.  The induction measure
`(univ \ S).card` strictly decreases.  At `univ` the partial unit is `⟨2⟩`
(`partialUnitTensor_univ`).

Unlike the invalid singleton-fold form, the fresh leg `j` is the partner the
cut-extraction hands us (so connectivity is automatic); the `ghz_extend` step
needs `i ∈ S`, which is what bars the disconnected-partner-graph counterexample. -/
theorem exists_unitTwo_restricts_of_all_flatRank_cut_ge_two
    (hk : 2 ≤ k) {d : Fin k → ℕ+} (T : KTensor F d)
    (hall : ∀ S : Finset (Fin k), S.Nonempty → S ≠ Finset.univ → 2 ≤ flatRank T S) :
    ∃ n : ℕ, Restricts (unitTensor F (k := k) (2 : ℕ+)) (kronPowNat T n) := by
  classical
  -- Two distinct legs from `2 ≤ k`.
  have h0 : (0 : ℕ) < k := by omega
  have h1 : (1 : ℕ) < k := by omega
  set i₀ : Fin k := ⟨0, h0⟩ with hi₀
  -- Base pair from the cut `{i₀}` (nonempty, `≠ univ` since `k ≥ 2`).
  have hi₀_ne_univ : ({i₀} : Finset (Fin k)) ≠ Finset.univ := by
    intro hcontra
    have hmem : (⟨1, h1⟩ : Fin k) ∈ ({i₀} : Finset (Fin k)) := by
      rw [hcontra]; exact Finset.mem_univ _
    rw [Finset.mem_singleton] at hmem
    exact absurd hmem (by simp [hi₀, Fin.ext_iff])
  obtain ⟨i, hi_mem, j, hj_mem, hij, hpair_ge⟩ :=
    exists_crossing_pair_of_flatRank_cut_ge_two hk T ({i₀} : Finset (Fin k))
      ⟨i₀, Finset.mem_singleton_self i₀⟩ hi₀_ne_univ
      (hall ({i₀} : Finset (Fin k)) ⟨i₀, Finset.mem_singleton_self i₀⟩ hi₀_ne_univ)
  rw [Finset.mem_singleton] at hi_mem; subst hi_mem
  -- `⟨2⟩_{i₀,j} ≤ₜ T`, hence `partialUnitTensor {i₀, j} ≤ₜ T = kronPowNat T 0`.
  have hpair0 : Restricts (unitPairTensor (F := F) (2 : ℕ+) i₀ j hij) T :=
    unitPairTensor_two_restricts_of_subrankPair_ge_two T i₀ j hij hpair_ge
  have hbase : Restricts (partialUnitTensor (F := F) ({i₀, j} : Finset (Fin k)))
      (kronPowNat T 0) := by
    have hcast := partialUnitTensor_pair (F := F) i₀ j hij
    have : Restricts ((partialUnitFormat_pair i₀ j hij) ▸
        (partialUnitTensor (F := F) ({i₀, j} : Finset (Fin k)))) T := by
      rw [hcast]; exact hpair0
    have h := (Restricts.format_cast_iff (partialUnitFormat_pair i₀ j hij)).mpr this
    simpa [kronPowNat] using h
  -- Grow: strong induction on `(univ \ S).card`, accumulating a partial-unit ≤ kronPow.
  -- `grow n` : for any `S` with the partial-unit restriction and `(univ\S).card = n`,
  -- some Kronecker power restricts `⟨2⟩`.
  suffices grow : ∀ n : ℕ, ∀ (S : Finset (Fin k)) (m : ℕ),
      S.Nonempty → (Finset.univ \ S).card = n →
      Restricts (partialUnitTensor (F := F) S) (kronPowNat T m) →
      ∃ N : ℕ, Restricts (unitTensor F (k := k) (2 : ℕ+)) (kronPowNat T N) by
    exact grow ((Finset.univ \ ({i₀, j} : Finset (Fin k))).card)
      ({i₀, j} : Finset (Fin k)) 0 ⟨i₀, by simp⟩ rfl hbase
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro S m hSne hcard hpartial
    by_cases hSuniv : S = Finset.univ
    · -- Reached univ: partial unit is the full `⟨2⟩`.
      subst hSuniv
      refine ⟨m, ?_⟩
      have h := (Restricts.format_cast_iff (partialUnitFormat_univ (k := k))).mp hpartial
      rwa [partialUnitTensor_univ (F := F) (k := k)] at h
    · -- `S ≠ univ`: extend by one fresh leg via the cut `S`.
      obtain ⟨i, hi_mem, j', hj'_mem, hij', hpair_ge'⟩ :=
        exists_crossing_pair_of_flatRank_cut_ge_two hk T S hSne hSuniv
          (hall S hSne hSuniv)
      have hpair' : Restricts (unitPairTensor (F := F) (2 : ℕ+) i j' hij') T :=
        unitPairTensor_two_restricts_of_subrankPair_ge_two T i j' hij' hpair_ge'
      have hnext : Restricts (partialUnitTensor (F := F) (insert j' S))
          (kronPowNat T (m + 1)) :=
        partialUnit_extend_restricts T hi_mem hj'_mem hij' hpair' hpartial
      -- The measure strictly decreases.
      have hj'_notin : j' ∉ S := hj'_mem
      have hcard_lt : (Finset.univ \ insert j' S).card < n := by
        rw [← hcard]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset (Finset.sdiff_subset_sdiff (Finset.Subset.refl _)
          (Finset.subset_insert j' S))]
        exact ⟨j', Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj'_notin⟩,
          fun hmem => (Finset.mem_sdiff.mp hmem).2 (Finset.mem_insert_self j' S)⟩
      exact IH _ hcard_lt (insert j' S) (m + 1) ⟨j', Finset.mem_insert_self j' S⟩ rfl hnext

/-- **Contrapositive of Lemma A** (survey tex:2286-2297).  If `T` is
    "subrank-1-stable" — every Kronecker power has `subrank ≤ 1` — then some
    *bipartition* cut `S` (nonempty, `≠ univ`) has flattening rank `≤ 1`.

    Proof: contrapose.  If every cut `S` has `flatRank T S ≥ 2`, Lemma A
    (`exists_unitTwo_restricts_of_all_flatRank_cut_ge_two`) gives `n` with
    `⟨2⟩ ≤ₜ kronPowNat T n`, hence `2 ≤ subrank (kronPowNat T n)`, contradicting
    `subrank (kronPowNat T n) ≤ 1`. -/
theorem exists_flatRank_cut_le_one_of_subrank_stable
    (hk : 2 ≤ k) {d : Fin k → ℕ+} (T : KTensor F d)
    (hstable : ∀ n : ℕ, subrank (kronPowNat T n) ≤ 1) :
    ∃ S : Finset (Fin k), S.Nonempty ∧ S ≠ Finset.univ ∧ flatRank T S ≤ 1 := by
  classical
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ S, S.Nonempty → S ≠ univ → 2 ≤ flatRank T S`.
  have hall : ∀ S : Finset (Fin k), S.Nonempty → S ≠ Finset.univ → 2 ≤ flatRank T S := by
    intro S hS hS'
    have := hcon S hS hS'
    omega
  obtain ⟨n, hres⟩ := exists_unitTwo_restricts_of_all_flatRank_cut_ge_two hk T hall
  -- Two distinct legs from `2 ≤ k` for the subrank-set `BddAbove`.
  have h0 : (0 : ℕ) < k := by omega
  have h1 : (1 : ℕ) < k := by omega
  set i₀ : Fin k := ⟨0, h0⟩
  set i₁ : Fin k := ⟨1, h1⟩
  have hne : i₁ ≠ i₀ := by simp only [i₀, i₁, Ne, Fin.mk.injEq]; omega
  have hmem : (2 : ℕ) ∈ { r : ℕ | ∃ hr : 0 < r,
      Restricts (unitTensor F (k := k) ⟨r, hr⟩) (kronPowNat T n) } :=
    ⟨two_pos, hres⟩
  have h2le : (2 : ℕ) ≤ subrank (kronPowNat T n) :=
    le_csSup (subrank_set_bddAbove' i₀ i₁ hne _) hmem
  have := hstable n
  omega

end Semicontinuity
