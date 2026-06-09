/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.MaxRankBound
import AsymptoticTensorRankSemicontinuity.FieldExtension
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.UnitOverhead
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Border degeneration → asymptotic subrank bridge for `KTensor` (Strassen 1991)

This file defines the **border (degeneration) subrank** `borderSubrank T` of a
`KTensor` and states the load-bearing analytic bridge

  `(borderSubrank T : ℝ) ≤ asympSubrank T`   (`borderSubrank_le_asympSubrank`),

which is the achievability half of Corollary 3.5's Vrana–Christandl step: a
border degeneration `⟨s⟩ ⪰ T` upgrades, asymptotically, to an honest restriction
bound `Q̃(T) ≥ s`.

## Source

**Strassen, "Degeneration and complexity of bilinear maps: some asymptotic
spectra", J. reine angew. Math. 413 (1991)**.

The relevant passage (tex:44-95) recalls degeneration `≦` (a map `f` is a
degeneration of `g` when `f ∈ closure(G·g)`) and the asymptotic preorder `≲`
defined on tensor classes via tensor powers (tex:64-69):

> `a ≲ b :⟺ aᴺ ≦ b^{N+o(N)}`,

which (tex:88-92) is equivalent to `aᴺ ≦ bᴺ · 2^{o(N)}`.  The *standard fact*
formalized here is that a (border) degeneration of `⟨s⟩` into `T` implies the
asymptotic restriction bound `Q̃(T) ≥ s`: a degree-`N` degeneration, raised to
the `n`-th Kronecker power, yields an *exact* restriction
`⟨s^n / poly(N,n)⟩ ≤ₜ T^{⊠n}`, whose `n`-th root tends to `s` as `n → ∞` (the
polynomial overhead `poly(N,n)` washes out under the `1/n` exponent).

## Encoding

`borderSubrank` ports the `Polynomial.coeff`-based degeneration encoding of
`TensorK.borderSubrankK`
(`the border-subrank amplification argument`),
retyped to the `KTensor`/`Restricts` substrate of `MaxRankBound`.  A degree-`N`
*border restriction* of `⟨s⟩` into `T` is a polynomial family
`A : ∀ i, Fin s → Fin (d i) → F[X]` with

* **vanishing** below degree `N`:
  `(∑_g (∏_i A i (ρ i) (g i)) · C (T g)).coeff n = 0` for all `n < N`, and
* **identity** at degree `N`:
  `(∑_g (∏_i A i (ρ i) (g i)) · C (T g)).coeff N = unitTensor F s ρ`,

for every leg-index tuple `ρ : ∀ i, Fin s`.  At `N = 0` (no vanishing
conditions) the constant-coefficient identity is *exactly* the `Restricts`
condition `⟨s⟩ ≤ₜ T` (the matrices `A i (ρ i) (g i)` become the leg matrices of
a restriction), so `subrank T ≤ borderSubrank T`.

## Main results

* `borderSubrank` — the border/degeneration subrank on `KTensor`.
* `subrank_le_borderSubrank` — an exact restriction is a degree-`0` degeneration,
  so `subrank T ≤ borderSubrank T`.
* `borderRestricts_amplify` — **(a) `n`-th-power amplification of a border
  degeneration**, the CORRECT GENERAL-`k` overhead `(N·n+1)^{k−1}` following
  Bürgisser §15.4 (15.7)+(15.8) (Strassen 1987 Prop 5.10).  A degree-`N` border
  restriction `⟨s⟩ ⪰ T` amplifies, via the two Bürgisser steps below, to the EXACT
  restriction

    `⟨s^n⟩ ≤ₜ ⟨(N·n+1)^{k−1}⟩ ⊠ T^{⊠n}`.

  The overhead is `(N·n+1)^{k−1}` with `q = N·n+1` — for a `k`-tensor the degree-`D`
  coefficient is the `k`-fold convolution `∑_{c₁+…+c_k=D, cᵢ≥0} ∏ᵢ Aᵢ.coeff cᵢ`, whose
  `(D+k−1 choose k−1)` compositions must all share ONE overhead index along the
  `⟨Q⟩` unit diagonal, so `Q ≥ (D+k−1 choose k−1)`; the clean valid bound is
  `Q = (D+1)^{k−1}` (inject `(c₁,…,c_k) ↦ (c₁,…,c_{k−1}) ∈ {0..D}^{k−1}`).  The
  special cases are `k=2 → (N·n+1)¹` (linear anti-diagonal), `k=3 → (N·n+1)²`
  (Bürgisser's bilinear `q²`), `k≥4 → (N·n+1)^{k−1}` (the FALSE `(N·n+1)²` was too
  small).  It is the composition of two individually-correct, individually-cited
  Bürgisser lemmas:
  - `borderRestricts_kronPow` (step 1, Bürgisser (15.8) iterated): the n-fold
    Kronecker degeneration `⟨s⟩ ⊴_{N+1} T ⟹ ⟨sⁿ⟩ ⊴_{nN+1} T^{⊠n}`.  proved
    (induction on `n` via `borderRestricts_kron_step` + `kron_contraction_factor` +
    `Polynomial.coeff_mul`);
  - `borderRestricts_exactify` (step 2, Bürgisser (15.7) general-`k`): `⟨m⟩ ⊴_q ψ ⟹
    Restricts ⟨m⟩ (⟨q^{k−1}⟩ ⊠ ψ)` via the `k[ε]/(εᵠ)` structural tensor
    (diagonal overhead collapse + guarded coefficient convolution).
  `borderRestricts_amplify` composes the `Polynomial.coeff` Cauchy-product
  bookkeeping of step 1 with step 2's `k[ε]/(εᵠ)` structural-tensor packing.
* `tendsto_overhead_rpow` / `washout_le` — **(c) the washout**: `((N·n+1)^e)^{1/n} → 1`
  and the resulting `s ≤ Q` from `s^n ≤ (N·n+1)^e·Q^n` (here `e = k−1`)
  (`((N·n+1)^e)^{1/n} = ((N·n+1)^{1/n})^e → 1^e` via `x ↦ x^e` continuity).
* `isGapped_pow` — gappedness is closed under powers.
* `borderSubrank_le_asympSubrank` — **the Strassen-1991 bridge**, the gapped /
  non-gapped case split of `FieldInvariance.asympSubrank_baseChange`.  The gapped
  branch uses amplification +
  T4 (`subrank_of_restricts_unit_overhead`) + T2 (`asympSubrank_kronPowNat`) +
  washout.  The non-gapped branch over arbitrary fields uses the
  corrected all-bipartition Lemma A (`exists_flatRank_cut_le_one_of_subrank_stable`)
  + the general-cut `borderRestricts_le_flatRank` (survey:2286-2297), the same way
  as `FieldInvariance.asympSubrank_baseChange`.

The declarations use steps (a) `borderRestricts_kronPow` (Bürgisser (15.8)
iterated, the n-fold Cauchy product) and (b) `borderRestricts_exactify`
(Bürgisser (15.7) general-`k`, the `k[ε]/(εᵠ)` structural-tensor
`q^{k−1}`-exactification).  None is the invalid `(★)`
`subrank (⟨q⟩ ⊠ S) ≤ q·subrank S` nor the invalid linear `⟨N·n+1⟩`
(k≥3) / bilinear `⟨(N·n+1)²⟩` (k≥4) overhead; the unit overhead is
handled at the spectral level by T4 (`asympSubrank` on the RHS), and
`borderRestricts_amplify` is a proved composition of (a)+(b).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Finset BigOperators Polynomial Filter

namespace Semicontinuity

universe u

variable {F : Type u} [Field F] {k : ℕ}

/-- The rank of a flattening does not increase after scalar extension.  Local copy
    of the standard column-span argument, kept here to avoid importing downstream
    Corollary-35 field-invariance material. -/
private theorem flatRank_baseChange_le' {K : Type u} [Field K] [Algebra F K]
    {d : Fin k → ℕ+} (T : KTensor F d) (I : Finset (Fin k)) :
    flatRank (T.baseChange (K := K)) I ≤ flatRank T I := by
  classical
  let M := flattenMatrix T I
  have hMatrix : (M.map (algebraMap F K)).rank ≤ M.rank := by
    rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
    obtain ⟨b, _hb_mem, hb_span, _hb_li⟩ :=
      Submodule.exists_fun_fin_finrank_span_eq F (Set.range M.col)
    have hle :
        Submodule.span K (Set.range (M.map (algebraMap F K)).col) ≤
          Submodule.span K (Set.range fun i =>
            (algebraMap F K) ∘ b i) := by
      rw [Submodule.span_le]
      rintro _ ⟨col, rfl⟩
      have hcol_mem : M.col col ∈ Submodule.span F (Set.range b) := by
        rw [hb_span]
        exact Submodule.subset_span ⟨col, rfl⟩
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hcol_mem
      refine (Submodule.mem_span_range_iff_exists_fun K).mpr
        ⟨fun i => algebraMap F K (c i), ?_⟩
      ext row
      have hc_row : (∑ i, c i * b i row) = M row col := by
        simpa [Matrix.col_apply, Finset.sum_apply, smul_eq_mul] using congr_fun hc row
      calc
        (∑ x, algebraMap F K (c x) • ((algebraMap F K) ∘ b x)) row
            = ∑ x, algebraMap F K (c x) * algebraMap F K (b x row) := by
                simp [Function.comp_apply, Algebra.smul_def]
        _ = ∑ x, algebraMap F K (c x * b x row) := by
                simp [map_mul]
        _ = algebraMap F K (∑ x, c x * b x row) :=
            (map_sum (algebraMap F K) _ _).symm
        _ = algebraMap F K (M row col) := by rw [hc_row]
        _ = M.map (algebraMap F K) row col := rfl
    exact (Submodule.finrank_mono hle).trans <| by
      calc Module.finrank K (Submodule.span K (Set.range fun i =>
            (algebraMap F K) ∘ b i))
          ≤ #(Finset.univ.image
              (fun i : Fin (Module.finrank F (Submodule.span F (Set.range M.col))) =>
                (algebraMap F K) ∘ b i)) := by
            simpa using finrank_span_le_card (R := K)
              (Set.range fun i : Fin (Module.finrank F
                (Submodule.span F (Set.range M.col))) => (algebraMap F K) ∘ b i)
        _ ≤ Fintype.card (Fin (Module.finrank F (Submodule.span F (Set.range M.col)))) :=
            Finset.card_image_le
        _ = Module.finrank F (Submodule.span F (Set.range M.col)) := Fintype.card_fin _
  have hflatten :
      flattenMatrix (T.baseChange (K := K)) I = (flattenMatrix T I).map (algebraMap F K) := by
    ext row col
    simp only [flattenMatrix, KTensor.baseChange, Matrix.map_apply]
  rw [flatRank, flatRank, hflatten]
  exact hMatrix

/-! ## The border (degeneration) subrank on `KTensor`. -/

/-- The polynomial-degeneration predicate: `⟨s⟩ ⪰ T` by a degree-`N` border
    restriction.  This is the `KTensor`/`Restricts`-retyped form of the body of
    `TensorK.borderSubrankK`
    (`IteratedMaMu/BorderSubrankK.lean`): a polynomial family
    `A : ∀ i, Fin s → Fin (d i) → F[X]` whose contraction against `T`

    * vanishes below degree `N` (the `ε`-orders of a border restriction), and
    * realizes the unit tensor `⟨s⟩` at degree `N`,

    for every leg tuple `ρ : ∀ i, Fin s`.  Here `unitTensor F (k := k) ⟨s, hs⟩ ρ`
    is the identity `k`-tensor entry `(= 1` iff all `ρ i` agree, else `0)`,
    matching `identityK` in the `TensorK` encoding.

    Source: Strassen 1991 tex:44-50 (degeneration `≦`), realized through the
    `Polynomial.coeff` `ε`-degeneration of `borderSubrankK`. -/
def BorderRestricts {d : Fin k → ℕ+} (s : ℕ) (hs : 0 < s) (T : KTensor F d) : Prop :=
  ∃ (N : ℕ) (A : ∀ i : Fin k, Fin s → Fin (d i) → Polynomial F),
    (∀ ρ : ∀ i : Fin k, Fin s, ∀ n : ℕ, n < N →
      (∑ g : ∀ i : Fin k, Fin (d i),
        (∏ i, A i (ρ i) (g i)) * Polynomial.C (T g)).coeff n = 0) ∧
    (∀ ρ : ∀ i : Fin k, Fin s,
      (∑ g : ∀ i : Fin k, Fin (d i),
        (∏ i, A i (ρ i) (g i)) * Polynomial.C (T g)).coeff N
        = unitTensor F (k := k) ⟨s, hs⟩
            (fun i => (Fin.cast (by rfl) (ρ i) : Fin ((⟨s, hs⟩ : ℕ+) : ℕ))))

/-- The explicit degree-`N` border-restriction witness predicate on a fixed
    polynomial family `A`: the body of `BorderRestricts` with the degree `N` and the
    family `A` exposed (not existentially bound).  This is the shape that composes
    across the two Bürgisser steps (step 1 produces it at degree `N·n`, step 2
    consumes it at that exact degree to read off the `q = N·n+1` overhead `⟨q²⟩`).

    `BorderRestricts s hs T ↔ ∃ N A, BorderRestrictsWitness s hs T N A`. -/
def BorderRestrictsWitness {d : Fin k → ℕ+} (s : ℕ) (hs : 0 < s) (T : KTensor F d)
    (N : ℕ) (A : ∀ i : Fin k, Fin s → Fin (d i) → Polynomial F) : Prop :=
  (∀ ρ : ∀ i : Fin k, Fin s, ∀ n : ℕ, n < N →
    (∑ g : ∀ i : Fin k, Fin (d i),
      (∏ i, A i (ρ i) (g i)) * Polynomial.C (T g)).coeff n = 0) ∧
  (∀ ρ : ∀ i : Fin k, Fin s,
    (∑ g : ∀ i : Fin k, Fin (d i),
      (∏ i, A i (ρ i) (g i)) * Polynomial.C (T g)).coeff N
      = unitTensor F (k := k) ⟨s, hs⟩
          (fun i => (Fin.cast (by rfl) (ρ i) : Fin ((⟨s, hs⟩ : ℕ+) : ℕ))))

/-- **Border (degeneration) subrank** `Q̲(T)` of a `KTensor` (Strassen 1991,
    tex:44-95).  The supremum of `s` such that a degree-`N` polynomial family
    *degenerates* the unit tensor `⟨s⟩` into `T` (`BorderRestricts`).  Ports
    `TensorK.borderSubrankK`
    (`IteratedMaMu/BorderSubrankK.lean`) to the `KTensor`/`Restricts` substrate.

    Since every exact restriction is a degree-`0` degeneration, `subrank T ≤
    borderSubrank T`; the Strassen-1991 amplification gives the asymptotic
    converse-direction bound `borderSubrank T ≤ Q̃(T)` (`asympSubrank`),
    formalized as `borderSubrank_le_asympSubrank`. -/
noncomputable def borderSubrank {d : Fin k → ℕ+} (T : KTensor F d) : ℕ :=
  sSup { s : ℕ | ∃ hs : 0 < s, BorderRestricts s hs T }

/-! ## Easy direction: an exact restriction is a degree-`0` degeneration. -/

/-- A `Restricts (⟨s⟩) T` exact restriction *is* a degree-`0` border
    restriction: take `A i (ρ i) (g i) := C (M i (ρ i) (g i))` for the leg
    matrices `M` of the restriction.  Then the contraction
    `∑_g (∏_i C (M i (ρ i) (g i))) · C (T g)` is a *constant* polynomial whose
    (unique, degree-`0`) coefficient is exactly the restriction value
    `∑_g (∏_i M i (ρ i) (g i)) · T g = ⟨s⟩ ρ`.  No vanishing conditions are
    required at `N = 0`. -/
theorem borderRestricts_of_restricts {d : Fin k → ℕ+} {s : ℕ} (hs : 0 < s)
    {T : KTensor F d}
    (h : Restricts (unitTensor F (k := k) ⟨s, hs⟩) T) :
    BorderRestricts s hs T := by
  classical
  obtain ⟨M, hM⟩ := h
  -- `A i a b := C (M i a' b)` where `a' : Fin s` is reindexed into `Fin (⟨s,hs⟩ : ℕ+)`.
  refine ⟨0, fun i a b => Polynomial.C (M i (Fin.cast (by rfl) a) b), ?_, ?_⟩
  · -- No `n < 0`.
    intro ρ n hn
    exact absurd hn (Nat.not_lt_zero n)
  · -- Degree-`0` coefficient = restriction value = `⟨s⟩ ρ`.
    intro ρ
    -- Each summand is a constant polynomial; pull `coeff 0` inside the sum.
    rw [Polynomial.finset_sum_coeff]
    -- `(∏_i C (M ...)) * C (T g)` is a product of constants `= C (...)`, so
    -- `coeff 0` is the product of the matrix entries times `T g`.
    have hcoeff : ∀ g : ∀ i : Fin k, Fin (d i),
        ((∏ i, Polynomial.C (M i (Fin.cast (by rfl) (ρ i)) (g i)))
            * Polynomial.C (T g)).coeff 0
          = (∏ i, M i (Fin.cast (by rfl) (ρ i)) (g i)) * T g := by
      intro g
      rw [← map_prod (Polynomial.C (R := F)), ← map_mul, Polynomial.coeff_C_zero]
    simp_rw [hcoeff]
    -- This is the restriction value of `⟨s⟩` at the reindexed `ρ`.
    have := hM (fun i => Fin.cast (by rfl) (ρ i))
    rw [this]

/-- Abstract-matrix submatrix-rank bound for **arbitrary** (non-`Equiv`) row/col
    selections, via `eRank` — Mathlib's `rank_submatrix_le` needs the column reindex
    to be an `Equiv`, which fails for `|Scut| ≥ 2`.  Stated over an abstract matrix so
    it never whnf-unfolds the heavy concrete flattening matrix at the call site. -/
private lemma rank_ge_of_submatrix_le_aux {K' : Type*} [CommRing K'] [Nontrivial K']
    {ι κ : Type*} [Fintype κ] {s : ℕ} (M : Matrix ι κ K') (f : Fin s → ι) (e : Fin s → κ) :
    (M.submatrix f e).rank ≤ M.rank := by
  have hle : (M.submatrix f e).eRank ≤ M.eRank := Matrix.eRank_submatrix_le M f e
  have hfin : M.eRank ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top (Fintype.card κ))
      (by rw [← ENat.card_eq_coe_fintype_card]; exact Matrix.eRank_le_card_width M)
  simpa only [Matrix.eRank_toNat_eq_rank] using ENat.toNat_le_toNat hle hfin

/-- A degree-`N` border restriction `⟨s⟩ ⪰ T` forces `s ≤ flatRank T Scut` for any
    *bipartition* cut `Scut` (with `i₀ ∈ Scut`, `i₁ ∉ Scut`): over the fraction
    field `Frac(F[X])`, the polynomial contraction is an exact restriction of a
    tensor whose `Scut`-flattening has an `s × s` submatrix with determinant
    divisible by `X^(N*s)` and nonzero leading coefficient. -/
theorem borderRestricts_le_flatRank {d : Fin k → ℕ+} {s : ℕ} (hs : 0 < s)
    {T : KTensor F d} (Scut : Finset (Fin k)) {i₀ i₁ : Fin k}
    (hi₀ : i₀ ∈ Scut) (hi₁ : i₁ ∉ Scut)
    (hres : BorderRestricts s hs T) :
    s ≤ flatRank T Scut := by
  classical
  obtain ⟨N, A, hvan, hid⟩ := hres
  let K := FractionRing (Polynomial F)
  let φ : Polynomial F →+* K := algebraMap (Polynomial F) K
  let dS : Fin k → ℕ+ := fun _ => ⟨s, hs⟩
  let S : KTensor K dS := fun ρ =>
    φ ((∑ g : ∀ i : Fin k, Fin (d i),
      (∏ i, A i (Fin.cast (by rfl) (ρ i)) (g i)) * Polynomial.C (T g)))
  let B : ∀ i : Fin k, Matrix (Fin (dS i)) (Fin (d i)) K :=
    fun i a b => φ (A i (Fin.cast (by rfl) a) b)
  have hST : Restricts S (T.baseChange (K := K)) := by
    refine ⟨B, ?_⟩
    intro ρ
    simp only [S, B, KTensor.baseChange]
    change φ (∑ g : ∀ i : Fin k, Fin (d i),
        (∏ i, A i (Fin.cast (by rfl) (ρ i)) (g i)) * Polynomial.C (T g))
      = ∑ idx : (∀ i : Fin k, Fin (d i)),
          (∏ i, φ (A i (Fin.cast (by rfl) (ρ i)) (idx i))) * φ (Polynomial.C (T idx))
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro g _
    rw [map_mul, map_prod]
  -- Rows set every in-cut leg to a common value `m`; cols every out-cut leg to `v`.
  -- (For `|Scut| ≥ 2` these constant-embeddings are NOT surjective, so `eRow` is a
  -- plain injective function, not an `Equiv`; `Matrix.rank_submatrix_le` accepts any
  -- index function, so the `s × s` constant-block still bounds the flattening rank.)
  let eRow : Fin s → ((x : {x // x ∈ Scut}) → Fin (dS x.val)) :=
    fun m x => Fin.cast (by rfl) m
  let cCol : Fin s → ((x : {x // x ∉ Scut}) → Fin (dS x.val)) :=
    fun v x => Fin.cast (by rfl) v
  let ρmv : Fin s → Fin s → (∀ i : Fin k, Fin s) :=
    fun m v i => if i ∈ Scut then m else v
  let P : Matrix (Fin s) (Fin s) (Polynomial F) := Matrix.of fun m v =>
    ∑ g : ∀ i : Fin k, Fin (d i),
      (∏ i, A i (ρmv m v i) (g i)) * Polynomial.C (T g)
  have hsub : (flattenMatrix S Scut).submatrix eRow cCol = P.map φ := by
    apply Matrix.ext
    intro m v
    simp only [Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply, flattenMatrix,
      S, P, cCol]
    -- With the constant-embeddings `eRow`/`cCol` and `ρmv i = if i ∈ Scut then m else v`,
    -- the `dite` over `i ∈ Scut` matches `ρmv` definitionally, so `congr 1` closes the goal.
    congr 1
  have hP_vanish : ∀ m v n, n < N → (P m v).coeff n = 0 := by
    intro m v n hn
    exact hvan (ρmv m v) n hn
  have hP_ident : ∀ m v, (P m v).coeff N = if m = v then 1 else 0 := by
    intro m v
    have h := hid (ρmv m v)
    simp only [P, Matrix.of_apply]
    rw [h]
    simp only [unitTensor]
    have hpred : (∀ i j : Fin k,
        Fin.cast (by rfl) (ρmv m v i) = Fin.cast (by rfl) (ρmv m v j)) ↔ m = v := by
      constructor
      · intro hall
        have h01 := hall i₀ i₁
        simp only [ρmv, if_pos hi₀, if_neg hi₁, Fin.cast_eq_self] at h01
        exact h01
      · intro hmv a b
        subst hmv
        simp only [ρmv]
        split <;> split <;> rfl
    by_cases hmv : m = v
    · rw [if_pos (hpred.mpr hmv), if_pos hmv]
    · rw [if_neg (fun h => hmv (hpred.mp h)), if_neg hmv]
  have hdvd : ∀ m v, Polynomial.X ^ N ∣ P m v := by
    intro m v
    rw [Polynomial.X_pow_dvd_iff]
    exact hP_vanish m v
  choose Q hPQ using hdvd
  let Qmat : Matrix (Fin s) (Fin s) (Polynomial F) := Matrix.of Q
  have hQ_coeff0 : ∀ m v, (Q m v).coeff 0 = if m = v then 1 else 0 := by
    intro m v
    have h := hP_ident m v
    rw [hPQ m v, Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self] at h
    exact h
  have hdetQ_ne : Qmat.det ≠ 0 := by
    intro hzero
    have h0 : Polynomial.constantCoeff Qmat.det = 0 := by rw [hzero]; simp
    rw [RingHom.map_det] at h0
    have hone : Polynomial.constantCoeff.mapMatrix Qmat = 1 := by
      apply Matrix.ext
      intro m v
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply,
        Qmat, Matrix.of_apply, Polynomial.constantCoeff_apply, hQ_coeff0]
    rw [hone, Matrix.det_one] at h0
    exact one_ne_zero h0
  have hdetP_ne : P.det ≠ 0 := by
    have hP_smul : P = (Polynomial.X : Polynomial F) ^ N • Qmat := by
      apply Matrix.ext
      intro m v
      simp only [Matrix.smul_apply, smul_eq_mul, Qmat, Matrix.of_apply, hPQ m v]
    rw [hP_smul, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ Polynomial.X_ne_zero)) hdetQ_ne
  have hdetPK_ne : (P.map φ).det ≠ 0 := by
    change (φ.mapMatrix P).det ≠ 0
    rw [← RingHom.map_det, Ne, ← map_zero φ]
    exact (IsFractionRing.injective (Polynomial F) K).ne hdetP_ne
  have hsub_rank : s ≤ flatRank S Scut := by
    have hfull : (P.map φ).rank = s := by
      rw [Matrix.rank_of_isUnit (P.map φ)
          ((P.map φ).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdetPK_ne)),
        Fintype.card_fin]
    -- `(submatrix eRow cCol).rank ≤ (flattenMatrix S Scut).rank` via an abstract-matrix
    -- helper so `rank_submatrix_le` does not whnf-unfold the heavy fraction-field tensor.
    have hle : ((flattenMatrix S Scut).submatrix eRow cCol).rank
        ≤ (flattenMatrix S Scut).rank :=
      rank_ge_of_submatrix_le_aux (flattenMatrix S Scut) eRow cCol
    rw [hsub, hfull] at hle
    exact hle
  calc
    s ≤ flatRank S Scut := hsub_rank
    _ ≤ flatRank (T.baseChange (K := K)) Scut := hST.flatRank_le Scut
    _ ≤ flatRank T Scut := flatRank_baseChange_le' T Scut

/-- **Easy direction** (Strassen 1991): the exact subrank is a lower bound for
    the border subrank, `subrank T ≤ borderSubrank T`, since every exact
    restriction `⟨s⟩ ≤ₜ T` is a degree-`0` degeneration
    (`borderRestricts_of_restricts`).  Requires the `borderSubrank` set to be
    nonempty / membership-monotone: we transport each witness of the `subrank`
    set into the `borderSubrank` set and use `csSup` monotonicity once the latter
    is bounded above.

    NOTE: stated over `k ≥ 2` (two distinct legs `i₀ ≠ i₁`), the regime of
    Cor 3.5, so that both subrank sets are bounded above (`BddAbove`) via the
    flattening witness, exactly as in `FieldInvariance.subrank_set_bddAbove`. -/
theorem subrank_le_borderSubrank {d : Fin k → ℕ+} (T : KTensor F d)
    (hbdd : BddAbove { s : ℕ | ∃ hs : 0 < s, BorderRestricts s hs T }) :
    subrank T ≤ borderSubrank T := by
  classical
  unfold subrank borderSubrank
  apply csSup_le_csSup' hbdd
  -- Subset: each exact-restriction witness gives a degree-0 degeneration.
  rintro s ⟨hs, hres⟩
  exact ⟨hs, borderRestricts_of_restricts hs hres⟩

/-! ## Gappedness propagates to Kronecker powers (abstract). -/

open AsymptoticSpectrumDuality

/-- **Gappedness is closed under powers** (Strassen-1988 framework).  If a class
    `a` is gapped (`IsGapped a`), then so is every positive power `a^n` (`n ≥ 1`).

    Each `IsGapped` disjunct propagates:
    * disjunct (i) `∃ m>0, 2 ≤_P a^m`: then `2 ≤_P 2^n ≤_P (a^m)^n = (a^n)^m`
      (`natCast_mono` on `2 ≤ 2^n`, then `pow_mono`), so `∃ m>0, 2 ≤_P (a^n)^m`;
    * disjunct (ii) `a ≤_P 0`: then `a^n = a·a^{n-1} ≤_P 0·a^{n-1} = 0`
      (`mul_mono`);
    * disjunct (iii) `∃ φ, φ(a) = 1`: then `φ(a^n) = φ(a)^n = 1` (`eval_pow`). -/
private lemma isGapped_pow {S : Type*} [CommSemiring S] {p : StrassenPreorder S}
    {a : S} (ha : p.IsGapped a) {n : ℕ} (hn : 1 ≤ n) : p.IsGapped (a ^ n) := by
  rcases ha with ⟨m, hm, h2⟩ | h0 | ⟨φ₀, hφ₀⟩
  · -- disjunct (i)
    refine Or.inl ⟨m, hm, ?_⟩
    -- `2 ≤_P 2^n`
    have hle2 : p.rel (2 : S) ((2 : S) ^ n) := by
      have hnat : (2 : ℕ) ≤ (2 : ℕ) ^ n := Nat.le_self_pow (by omega) 2
      have := p.natCast_mono hnat
      simpa using this
    -- `2^n ≤_P (a^m)^n`
    have hpn : p.rel ((2 : S) ^ n) ((a ^ m) ^ n) := p.pow_mono n h2
    -- `(a^m)^n = (a^n)^m`
    have hcomm : (a ^ m) ^ n = (a ^ n) ^ m := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [hcomm] at hpn
    exact p.trans _ _ _ hle2 hpn
  · -- disjunct (ii): `a ≤_P 0`
    refine Or.inr (Or.inl ?_)
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    have := p.mul_mono a 0 (a ^ j) h0
    rw [zero_mul] at this
    rw [pow_succ, mul_comm]
    simpa [mul_comm] using this
  · -- disjunct (iii): `∃ φ₀, φ₀(a) = 1` ⟹ `φ₀(a^n) = φ₀(a)^n = 1`
    exact Or.inr (Or.inr ⟨φ₀, by
      rw [AsymptoticSpectrum.eval_pow, hφ₀, one_pow]⟩)

/-! ## The Strassen-1991 bridge: border degeneration ⇒ asymptotic subrank. -/

/-- The per-leg Kronecker index equivalence on full tuples:
    `(∀ i, Fin (dS i * dT i)) ≃ (∀ i, Fin (dS i)) × (∀ i, Fin (dT i))`,
    leg `i` split by `finProdFinEquiv.symm` into `(kronLeftIndex, kronRightIndex)`.
    This is the bijection underlying the Kronecker-product contraction
    factorization (Bürgisser (15.8), the `⊗` of two border restrictions). -/
def kronIndexEquiv {d₁ d₂ : Fin k → ℕ+} :
    (∀ i : Fin k, Fin ((d₁ i * d₂ i : ℕ+) : ℕ)) ≃
      (∀ i : Fin k, Fin (d₁ i)) × (∀ i : Fin k, Fin (d₂ i)) where
  toFun g := (fun i => kronLeftIndex (dS := d₁) (dT := d₂) g i,
              fun i => kronRightIndex (dS := d₁) (dT := d₂) g i)
  invFun p := fun i =>
    (finProdFinEquiv (by simpa [PNat.mul_coe] using (p.1 i, p.2 i))
      : Fin ((d₁ i * d₂ i : ℕ+) : ℕ))
  left_inv g := by
    funext i
    simp only [kronLeftIndex, kronRightIndex]
    -- `finProdFinEquiv (finProdFinEquiv.symm x).1, .2 = x`, up to the `PNat.mul_coe` cast.
    refine Fin.ext ?_
    have := Equiv.apply_symm_apply finProdFinEquiv
      (by simpa [PNat.mul_coe] using g i : Fin (((d₁ i : ℕ) * (d₂ i : ℕ))))
    simpa [PNat.mul_coe] using congrArg Fin.val this
  right_inv p := by
    refine Prod.ext ?_ ?_ <;> funext i <;>
      simp only [kronLeftIndex, kronRightIndex]
    · have := congrArg Prod.fst (Equiv.symm_apply_apply finProdFinEquiv (p.1 i, p.2 i))
      simp only [finProdFinEquiv_symm_apply] at this; exact this
    · have := congrArg Prod.snd (Equiv.symm_apply_apply finProdFinEquiv (p.1 i, p.2 i))
      simp only [finProdFinEquiv_symm_apply] at this; exact this

/-- **Contraction factorization for a Kronecker-product witness** (Bürgisser (15.8)).
    If `B i ρ g := A₁ i ρ₁ᵢ (kronLeftIndex g i) · A₂ i ρ₂ᵢ (kronRightIndex g i)` is the
    Kronecker-product polynomial family (built from the families `A₁, A₂` of two border
    restrictions, with the label `ρ` split into `(ρ₁, ρ₂)` and the leg `g` split into
    `(g₁, g₂)`), then the contraction of `B` against `T₁ ⊠ T₂` *factors* as the product
    of the two individual contractions:

      `∑_g (∏_i B i ρᵢ gᵢ)·C((T₁⊠T₂) g) = P_{A₁}(ρ₁) · P_{A₂}(ρ₂)`.

    This is the polynomial identity that turns the `q₁+q₂−1` order addition of (15.8) into
    a `Polynomial.coeff` Cauchy product (`coeff_mul`). -/
theorem kron_contraction_factor {d₁ d₂ : Fin k → ℕ+}
    {s₁ s₂ : ℕ} (T₁ : KTensor F d₁) (T₂ : KTensor F d₂)
    (A₁ : ∀ i : Fin k, Fin s₁ → Fin (d₁ i) → Polynomial F)
    (A₂ : ∀ i : Fin k, Fin s₂ → Fin (d₂ i) → Polynomial F)
    (ρ₁ : ∀ i : Fin k, Fin s₁) (ρ₂ : ∀ i : Fin k, Fin s₂) :
    (∑ g : ∀ i : Fin k, Fin ((d₁ i * d₂ i : ℕ+) : ℕ),
        (∏ i, A₁ i (ρ₁ i) (kronLeftIndex (dS := d₁) (dT := d₂) g i)
              * A₂ i (ρ₂ i) (kronRightIndex (dS := d₁) (dT := d₂) g i))
          * Polynomial.C ((T₁ ⊠ T₂) g))
      = (∑ g₁ : ∀ i : Fin k, Fin (d₁ i),
            (∏ i, A₁ i (ρ₁ i) (g₁ i)) * Polynomial.C (T₁ g₁))
        * (∑ g₂ : ∀ i : Fin k, Fin (d₂ i),
            (∏ i, A₂ i (ρ₂ i) (g₂ i)) * Polynomial.C (T₂ g₂)) := by
  classical
  -- Reindex the `g`-sum by the Kronecker equiv into a double sum over `(g₁, g₂)`.
  rw [← (kronIndexEquiv (d₁ := d₁) (d₂ := d₂)).symm.sum_comp
        (fun g => (∏ i, A₁ i (ρ₁ i) (kronLeftIndex (dS := d₁) (dT := d₂) g i)
              * A₂ i (ρ₂ i) (kronRightIndex (dS := d₁) (dT := d₂) g i))
          * Polynomial.C ((T₁ ⊠ T₂) g))]
  rw [Finset.sum_mul_sum]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun g₁ _ => Finset.sum_congr rfl (fun g₂ _ => ?_))
  -- Compute the summand under the equiv: `kronLeftIndex (e.symm (g₁,g₂)) = g₁`, etc.
  simp only [kronIndexEquiv, Equiv.coe_fn_symm_mk]
  have hL : ∀ i : Fin k,
      kronLeftIndex (dS := d₁) (dT := d₂)
        (fun i => (finProdFinEquiv (by simpa [PNat.mul_coe] using (g₁ i, g₂ i))
          : Fin ((d₁ i * d₂ i : ℕ+) : ℕ))) i = g₁ i := by
    intro i
    simp only [kronLeftIndex]
    have := congrArg Prod.fst (Equiv.symm_apply_apply finProdFinEquiv (g₁ i, g₂ i))
    simp only [finProdFinEquiv_symm_apply] at this; exact this
  have hR : ∀ i : Fin k,
      kronRightIndex (dS := d₁) (dT := d₂)
        (fun i => (finProdFinEquiv (by simpa [PNat.mul_coe] using (g₁ i, g₂ i))
          : Fin ((d₁ i * d₂ i : ℕ+) : ℕ))) i = g₂ i := by
    intro i
    simp only [kronRightIndex]
    have := congrArg Prod.snd (Equiv.symm_apply_apply finProdFinEquiv (g₁ i, g₂ i))
    simp only [finProdFinEquiv_symm_apply] at this; exact this
  simp only [hL, hR]
  -- `(T₁⊠T₂) (e.symm (g₁,g₂)) = T₁ g₁ · T₂ g₂`.
  have hT : (T₁ ⊠ T₂)
      (fun i => (finProdFinEquiv (by simpa [PNat.mul_coe] using (g₁ i, g₂ i))
        : Fin ((d₁ i * d₂ i : ℕ+) : ℕ))) = T₁ g₁ * T₂ g₂ := by
    simp only [kroneckerTensor]
    congr 1
    · congr 1; funext i; exact hL i
    · congr 1; funext i; exact hR i
  rw [hT, map_mul, Finset.prod_mul_distrib]
  ring

/-- **Single Kronecker step** (Bürgisser (15.8), `t₁⊴_{q₁}⟨r₁⟩, t₂⊴_{q₂}⟨r₂⟩ ⟹
    t₁⊗t₂ ⊴_{q₁+q₂−1} ⟨r₁r₂⟩`, `burgisserbook.tex:11598-11600`).  Two border-restriction
    witnesses — degree `N₁` for `⟨s₁⟩ ⪰ T₁` and degree `N₂` for `⟨s₂⟩ ⪰ T₂` — combine
    into a degree-`(N₁+N₂)` witness for `⟨s₁·s₂⟩ ⪰ T₁ ⊠ T₂`.

    The witness `B i ρ g := A₁ i (ρ.divNat i) (kronLeftIndex g i) ·
    A₂ i (ρ.modNat i) (kronRightIndex g i)` makes the contraction factor
    (`kron_contraction_factor`) as `P_{A₁}(ρ₁)·P_{A₂}(ρ₂)`, whence `coeff_mul` (the
    Cauchy product) gives the `q₁+q₂−1` order addition: vanishing below `N₁+N₂` (each
    convolution term has one factor below its threshold) and `⟨s₁⟩·⟨s₂⟩ = ⟨s₁s₂⟩` at
    `N₁+N₂` (injectivity of `finProdFinEquiv.symm`). -/
theorem borderRestricts_kron_step {d₁ d₂ : Fin k → ℕ+}
    {s₁ s₂ : ℕ} (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    {T₁ : KTensor F d₁} {T₂ : KTensor F d₂} (N₁ N₂ : ℕ)
    (A₁ : ∀ i : Fin k, Fin s₁ → Fin (d₁ i) → Polynomial F)
    (A₂ : ∀ i : Fin k, Fin s₂ → Fin (d₂ i) → Polynomial F)
    (hA₁ : BorderRestrictsWitness s₁ hs₁ T₁ N₁ A₁)
    (hA₂ : BorderRestrictsWitness s₂ hs₂ T₂ N₂ A₂) :
    ∃ B, BorderRestrictsWitness (s₁ * s₂) (Nat.mul_pos hs₁ hs₂) (T₁ ⊠ T₂) (N₁ + N₂) B := by
  classical
  obtain ⟨hA₁van, hA₁id⟩ := hA₁
  obtain ⟨hA₂van, hA₂id⟩ := hA₂
  -- Per-leg label split `σ₁ ρ i := (finProdFinEquiv.symm (ρ i)).1`, `σ₂` the `.2`.
  set σ₁ : (∀ i : Fin k, Fin (s₁ * s₂)) → ∀ i : Fin k, Fin s₁ :=
    fun ρ i => (finProdFinEquiv.symm (ρ i)).1 with hσ₁
  set σ₂ : (∀ i : Fin k, Fin (s₁ * s₂)) → ∀ i : Fin k, Fin s₂ :=
    fun ρ i => (finProdFinEquiv.symm (ρ i)).2 with hσ₂
  -- Witness `B`: split the label `a : Fin (s₁·s₂)` per leg by `finProdFinEquiv.symm`,
  -- and the Kronecker leg `g` by `kronLeft/RightIndex`.
  set B : ∀ i : Fin k, Fin (s₁ * s₂) → Fin ((d₁ i * d₂ i : ℕ+) : ℕ) → Polynomial F :=
    fun i a g =>
      A₁ i (finProdFinEquiv.symm a).1
        (finProdFinEquiv.symm (by simpa [PNat.mul_coe] using g)).1
      * A₂ i (finProdFinEquiv.symm a).2
        (finProdFinEquiv.symm (by simpa [PNat.mul_coe] using g)).2 with hB
  -- The contraction of `B` at full label `ρ` factors as `P_{A₁}(σ₁ ρ) · P_{A₂}(σ₂ ρ)`.
  have contraction_factor_at : ∀ ρ : ∀ i : Fin k, Fin (s₁ * s₂),
      (∑ g : ∀ i : Fin k, Fin ((d₁ i * d₂ i : ℕ+) : ℕ),
        (∏ i, B i (ρ i) (g i)) * Polynomial.C ((T₁ ⊠ T₂) g))
        = (∑ g₁ : ∀ i : Fin k, Fin (d₁ i),
            (∏ i, A₁ i (σ₁ ρ i) (g₁ i)) * Polynomial.C (T₁ g₁))
          * (∑ g₂ : ∀ i : Fin k, Fin (d₂ i),
            (∏ i, A₂ i (σ₂ ρ i) (g₂ i)) * Polynomial.C (T₂ g₂)) := by
    intro ρ
    rw [← kron_contraction_factor T₁ T₂ A₁ A₂ (σ₁ ρ) (σ₂ ρ)]; rfl
  -- `⟨s₁⟩(σ₁ ρ) · ⟨s₂⟩(σ₂ ρ) = ⟨s₁·s₂⟩(ρ)` (injectivity of `finProdFinEquiv.symm`).
  have unitTensor_split_mul : ∀ ρ : ∀ i : Fin k, Fin (s₁ * s₂),
      unitTensor F (k := k) ⟨s₁, hs₁⟩ (fun i => Fin.cast (by rfl) (σ₁ ρ i))
      * unitTensor F (k := k) ⟨s₂, hs₂⟩ (fun i => Fin.cast (by rfl) (σ₂ ρ i))
        = unitTensor F (k := k) ⟨s₁ * s₂, Nat.mul_pos hs₁ hs₂⟩
            (fun i => Fin.cast (by rfl) (ρ i)) := by
    intro ρ
    simp only [unitTensor, hσ₁, hσ₂]
    -- The casts are identities; the `⟨s₁·s₂⟩`-condition `∀ i j, ρ i = ρ j` is equivalent
    -- to the conjunction of the two split conditions, since `finProdFinEquiv.symm` is
    -- injective (`ρ i = ρ j ↔ (divNat, modNat) agree`).
    have hiff : (∀ i j : Fin k, (Fin.cast (by rfl) (ρ i) : Fin (s₁ * s₂))
          = Fin.cast (by rfl) (ρ j))
        ↔ ((∀ i j : Fin k, (Fin.cast (by rfl) (finProdFinEquiv.symm (ρ i)).1 : Fin s₁)
              = Fin.cast (by rfl) (finProdFinEquiv.symm (ρ j)).1)
          ∧ (∀ i j : Fin k, (Fin.cast (by rfl) (finProdFinEquiv.symm (ρ i)).2 : Fin s₂)
              = Fin.cast (by rfl) (finProdFinEquiv.symm (ρ j)).2)) := by
      simp only [Fin.cast_eq_self]
      constructor
      · intro h
        refine ⟨fun i j => ?_, fun i j => ?_⟩
        · rw [h i j]
        · rw [h i j]
      · rintro ⟨h1, h2⟩ i j
        have : finProdFinEquiv.symm (ρ i) = finProdFinEquiv.symm (ρ j) :=
          Prod.ext (h1 i j) (h2 i j)
        exact finProdFinEquiv.symm.injective this
    by_cases hall : (∀ i j : Fin k, (Fin.cast (by rfl) (ρ i) : Fin (s₁ * s₂))
          = Fin.cast (by rfl) (ρ j))
    · obtain ⟨h1, h2⟩ := hiff.mp hall
      rw [if_pos h1, if_pos h2, if_pos hall, mul_one]
    · rw [if_neg hall]
      rw [hiff] at hall
      by_cases h1 : (∀ i j : Fin k, (Fin.cast (by rfl) (finProdFinEquiv.symm (ρ i)).1 : Fin s₁)
              = Fin.cast (by rfl) (finProdFinEquiv.symm (ρ j)).1)
      · have h2 : ¬ (∀ i j : Fin k, (Fin.cast (by rfl) (finProdFinEquiv.symm (ρ i)).2 : Fin s₂)
              = Fin.cast (by rfl) (finProdFinEquiv.symm (ρ j)).2) := fun h2 => hall ⟨h1, h2⟩
        rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
  refine ⟨B, ?_, ?_⟩
  · -- VANISHING below `N₁ + N₂`.
    intro ρ n hn
    rw [contraction_factor_at ρ, Polynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_antidiagonal] at hp
    -- `p.1 + p.2 = n < N₁ + N₂`, so `p.1 < N₁` or `p.2 < N₂`.
    rcases lt_or_ge p.1 N₁ with h1 | h1
    · rw [hA₁van _ _ h1, zero_mul]
    · have h2 : p.2 < N₂ := by omega
      rw [hA₂van _ _ h2, mul_zero]
  · -- IDENTITY at `N₁ + N₂`.
    intro ρ
    rw [contraction_factor_at ρ, Polynomial.coeff_mul]
    -- Only the term `(N₁, N₂)` survives: `p.1 < N₁ ⟹` left factor `0`;
    -- `p.1 > N₁ ⟹ p.2 < N₂ ⟹` right factor `0`.
    rw [Finset.sum_eq_single (⟨N₁, N₂⟩ : ℕ × ℕ)]
    · rw [hA₁id, hA₂id]
      -- `⟨s₁⟩ ρ₁ · ⟨s₂⟩ ρ₂ = ⟨s₁s₂⟩ ρ`.
      exact unitTensor_split_mul ρ
    · intro p hp hne
      rw [Finset.mem_antidiagonal] at hp
      rcases lt_or_ge p.1 N₁ with h1 | h1
      · rw [hA₁van _ _ h1, zero_mul]
      · have hp1 : N₁ < p.1 := by
          rcases lt_or_eq_of_le h1 with h | h
          · exact h
          · refine absurd (?_ : p = (⟨N₁, N₂⟩ : ℕ × ℕ)) hne
            rw [Prod.ext_iff]; exact ⟨h.symm, by omega⟩
        have h2 : p.2 < N₂ := by omega
        rw [hA₂van _ _ h2, mul_zero]
    · intro h
      exact absurd (Finset.mem_antidiagonal.mpr (rfl : N₁ + N₂ = N₁ + N₂)) h

/-- **Reindexing a border-restriction witness along a rank equality** `s = s'` and a
    degree equality `N = N'`.  Reindexing the label leg `Fin s → Fin s'` by the
    `Fin.cast` of `s = s'` transports the witness; the `⟨s⟩` unit-tensor RHS reindexes to
    `⟨s'⟩`.  Bookkeeping glue for the `borderRestricts_kronPow` induction (where the
    Kronecker recursion produces `s^(m+1)·s` / `N·(m+1)+N` that must be rewritten to
    `s^(m+2)` / `N·(m+2)`). -/
theorem borderRestrictsWitness_reindex {d : Fin k → ℕ+} {s s' : ℕ}
    (hs : 0 < s) (hs' : 0 < s') {T : KTensor F d} {N N' : ℕ}
    (A : ∀ i : Fin k, Fin s → Fin (d i) → Polynomial F)
    (hss : s = s') (hNN : N = N')
    (hA : BorderRestrictsWitness s hs T N A) :
    BorderRestrictsWitness s' hs' T N'
      (fun i a g => A i (Fin.cast hss.symm a) g) := by
  subst hss; subst hNN
  obtain ⟨hvan, hid⟩ := hA
  refine ⟨?_, ?_⟩
  · intro ρ l hl
    have := hvan (fun i => Fin.cast rfl (ρ i)) l hl
    simpa using this
  · intro ρ
    have := hid (fun i => Fin.cast rfl (ρ i))
    simpa using this

/-- **Step 1 — `n`-fold Kronecker degeneration** (Bürgisser §15.4, (15.8) iterated;
    `burgisserbook.tex:11598-11600` and Lemma (15.24)(3), `tex:11952`).

    Bürgisser (15.8):
    `t₁ ⊴_{q₁} ⟨r₁⟩, t₂ ⊴_{q₂} ⟨r₂⟩ ⟹ t₁⊗t₂ ⊴_{q₁+q₂−1} ⟨r₁r₂⟩`.
    Iterating `n` times the single degeneration `⟨s⟩ ⊴_{N+1} T` (a degree-`N` border
    restriction has order `q = N+1`, the lowest realized `ε`-order being `q−1 = N`):
    the orders add as `q₁+…+qₙ−(n−1) = n(N+1)−(n−1) = nN+1`, and the ranks multiply
    `r₁⋯rₙ = sⁿ`.  Hence

      `⟨s⟩ ⊴_{N+1} T ⟹ ⟨sⁿ⟩ ⊴_{nN+1} T^{⊠n}`,

    i.e. a degree-`N·n` border restriction of `⟨sⁿ⟩` into `T^{⊠n}`
    (`kronPowNat T (n-1) = T^{⊠n}`).  In the `Polynomial.coeff` framework this is the
    n-fold Cauchy product: the product family `∏_{j<n} A_j` over the Kronecker legs
    has its sub-`(N·n)` `ε`-coefficients vanish and its degree-`N·n` coefficient
    realize `⟨sⁿ⟩`, the full convolution `∑_{c₁+…+cₙ=N·n} ∏ᵢ (Aᵢ).coeff cᵢ`.

    Proof: by induction on `n`, iterating the single Kronecker step
    `borderRestricts_kron_step` (Bürgisser (15.8), `T₂ = T`) along the `kroneckerTensor`
    recursion `kronPowNat T m ⊠ T = kronPowNat T (m+1)`.  Each step factors the contraction
    polynomial (`kron_contraction_factor`) and applies `Polynomial.coeff_mul` (the Cauchy
    product) to get the `q₁+q₂−1` order addition and `⟨s₁⟩·⟨s₂⟩ = ⟨s₁s₂⟩` (injectivity of
    `finProdFinEquiv.symm`).  No false `(★)`, no extra hypotheses. -/
theorem borderRestricts_kronPow {d : Fin k → ℕ+} {s : ℕ} (hs : 0 < s)
    {T : KTensor F d} (N : ℕ)
    (A : ∀ i : Fin k, Fin s → Fin (d i) → Polynomial F)
    (hA : BorderRestrictsWitness s hs T N A)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ B, BorderRestrictsWitness (s ^ n) (pow_pos hs n) (kronPowNat T (n - 1)) (N * n) B := by
  classical
  -- Induct on `m = n - 1` (so `n = m + 1`), avoiding `n - 1` subtraction in the recursion.
  -- The step uses `borderRestricts_kron_step` with `T₂ = T`, since
  -- `kronPowNat T m ⊠ T = kronPowNat T (m+1)` (the `kroneckerTensor` recursion).
  suffices h : ∀ m : ℕ, ∃ B, BorderRestrictsWitness (s ^ (m + 1)) (pow_pos hs (m + 1))
      (kronPowNat T m) (N * (m + 1)) B by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simpa using h m
  intro m
  induction m with
  | zero =>
    -- Base: `kronPowNat T 0 = T` (defeq), reindex `A` along `s = s^1`, `N = N*1`.
    exact ⟨_, borderRestrictsWitness_reindex (F := F) (k := k) hs (pow_pos hs 1) A
      (by rw [pow_one]) (by rw [Nat.mul_one]) hA⟩
  | succ m ih =>
    -- Step: combine the `m`-fold witness with `A` (for `T`) via `borderRestricts_kron_step`,
    -- then reindex `s^(m+1)·s → s^(m+2)`, `N·(m+1)+N → N·(m+2)`.  The tensor identity
    -- `kronPowNat T m ⊠ T = kronPowNat T (m+1)` is definitional (`kroneckerTensor` recursion).
    obtain ⟨B, hB⟩ := ih
    obtain ⟨C, hC⟩ :=
      borderRestricts_kron_step (F := F) (k := k) (s₁ := s ^ (m + 1)) (s₂ := s)
        (pow_pos hs (m + 1)) hs (N * (m + 1)) N B A hB hA
    exact ⟨_, borderRestrictsWitness_reindex (F := F) (k := k)
      (Nat.mul_pos (pow_pos hs (m + 1)) hs) (pow_pos hs (m + 1 + 1)) C
      (pow_succ s (m + 1)).symm (by ring) hC⟩

/-- **Multi-coefficient convolution** (the `k`-fold Cauchy product).  The
    degree-`N` coefficient of a finite product of polynomials is the convolution
    over all ways to write `N` as an ordered sum of per-factor degrees:

      `(∏ i, p i).coeff N = ∑_{l ∈ finsuppAntidiag univ N} ∏ i, (p i).coeff (l i)`.

    Proved by pulling the product through the polynomial → power-series coercion
    (a ring hom, `Polynomial.coeToPowerSeries.ringHom`) and applying
    `PowerSeries.coeff_prod` (`Mathlib.RingTheory.PowerSeries.Basic`), then
    `Polynomial.coeff_coe` to read the coefficients back as polynomial
    coefficients. -/
private lemma coeff_prod_finsuppAntidiag {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Polynomial F) (N : ℕ) :
    (∏ i, p i).coeff N
      = ∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) N,
          ∏ i, (p i).coeff (l i) := by
  classical
  -- Pull `coeff N` along the polynomial → power series coercion (a ring hom).
  have hcoe : ((∏ i, p i : Polynomial F) : PowerSeries F)
      = ∏ i, ((p i : Polynomial F) : PowerSeries F) :=
    map_prod (Polynomial.coeToPowerSeries.ringHom (R := F)) p Finset.univ
  rw [← Polynomial.coeff_coe, hcoe, PowerSeries.coeff_prod]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Polynomial.coeff_coe]

private lemma unitTensor_diagonal_sum [NeZero k] {r : ℕ+} (f : (∀ i : Fin k, Fin r) → F) :
    (∑ qIdx : ∀ i : Fin k, Fin r,
        f qIdx * unitTensor F (k := k) r qIdx)
      = ∑ q : Fin r, f (fun _ : Fin k => q) := by
  classical
  simp only [unitTensor]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  refine (Finset.sum_bij
    (t := (Finset.univ : Finset (Fin r)))
    (f := f)
    (g := fun q : Fin r => f (fun _ : Fin k => q))
    (fun qIdx (_ : qIdx ∈ (Finset.univ.filter
        (fun qIdx : ∀ i : Fin k, Fin r => ∀ i j : Fin k, qIdx i = qIdx j))) =>
      if hk : Nonempty (Fin k) then qIdx (Classical.choice hk) else 0)
    ?_ ?_ ?_ ?_)
  · intro qIdx hqIdx
    simp
  · intro qIdx₁ hqIdx₁ qIdx₂ hqIdx₂ hq
    rw [Finset.mem_filter] at hqIdx₁ hqIdx₂
    obtain ⟨_, hdiag₁⟩ := hqIdx₁
    obtain ⟨_, hdiag₂⟩ := hqIdx₂
    funext i
    by_cases hk : Nonempty (Fin k)
    · calc
        qIdx₁ i = qIdx₁ (Classical.choice hk) := hdiag₁ i (Classical.choice hk)
        _ = qIdx₂ (Classical.choice hk) := by simpa [hk] using hq
        _ = qIdx₂ i := (hdiag₂ i (Classical.choice hk)).symm
    · exact False.elim (hk ⟨i⟩)
  · intro q _
    refine ⟨fun _ : Fin k => q, ?_, ?_⟩
    · simp
    · have hk : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp (NeZero.pos k)
      simp [hk]
  · intro qIdx hqIdx
    rw [Finset.mem_filter] at hqIdx
    obtain ⟨_, hdiag⟩ := hqIdx
    congr 1
    funext i
    by_cases hk : Nonempty (Fin k)
    · simpa [hk] using hdiag i (Classical.choice hk)
    · exact False.elim (hk ⟨i⟩)

private def exactifyPart (n N : ℕ) (c : Fin n → Fin (N + 1)) : Fin (n + 1) → ℕ :=
  Fin.lastCases (N - ∑ j : Fin n, (c j : ℕ)) (fun j : Fin n => (c j : ℕ))

private def exactifyCoef (n N : ℕ) (i : Fin (n + 1)) (c : Fin n → Fin (N + 1))
    (p : Polynomial F) : F :=
  Fin.lastCases
    (if (∑ j : Fin n, (c j : ℕ)) ≤ N then p.coeff (N - ∑ j : Fin n, (c j : ℕ)) else 0)
    (fun j : Fin n => p.coeff (c j : ℕ)) i

private lemma exactifyPart_castSucc (n N : ℕ) (c : Fin n → Fin (N + 1)) (j : Fin n) :
    exactifyPart n N c j.castSucc = (c j : ℕ) := by
  simp [exactifyPart]

private lemma exactifyPart_last (n N : ℕ) (c : Fin n → Fin (N + 1)) :
    exactifyPart n N c (Fin.last n) = N - ∑ j : Fin n, (c j : ℕ) := by
  simp [exactifyPart]

private lemma exactifyCoef_castSucc (n N : ℕ) (c : Fin n → Fin (N + 1))
    (p : Polynomial F) (j : Fin n) :
    exactifyCoef n N j.castSucc c p = p.coeff (c j : ℕ) := by
  simp [exactifyCoef]

private lemma exactifyCoef_last (n N : ℕ) (c : Fin n → Fin (N + 1)) (p : Polynomial F) :
    exactifyCoef n N (Fin.last n) c p =
      if (∑ j : Fin n, (c j : ℕ)) ≤ N then p.coeff (N - ∑ j : Fin n, (c j : ℕ)) else 0 := by
  simp [exactifyCoef]

set_option linter.flexible false in
private lemma exactifyCoef_sum_eq_coeff (n N : ℕ) (p : Fin (n + 1) → Polynomial F) :
    (∑ q : Fin ((N + 1) ^ n),
        ∏ i : Fin (n + 1),
          exactifyCoef n N i (finFunctionFinEquiv.symm q) (p i))
      = (∏ i : Fin (n + 1), p i).coeff N := by
  classical
  let e := finFunctionFinEquiv (m := N + 1) (n := n)
  let H : (Fin n → Fin (N + 1)) → F :=
    fun c => ∏ i : Fin (n + 1), exactifyCoef n N i c (p i)
  have hq : (∑ q : Fin ((N + 1) ^ n), H (e.symm q)) = ∑ c : Fin n → Fin (N + 1), H c := by
    simpa [e] using (e.symm.sum_comp H)
  rw [show (∑ q : Fin ((N + 1) ^ n),
        ∏ i : Fin (n + 1), exactifyCoef n N i (finFunctionFinEquiv.symm q) (p i))
        = ∑ q : Fin ((N + 1) ^ n), H (e.symm q) from rfl, hq]
  let valid : (Fin n → Fin (N + 1)) → Prop := fun c => (∑ j : Fin n, (c j : ℕ)) ≤ N
  have hinvalid_zero : ∀ c : Fin n → Fin (N + 1), ¬ valid c → H c = 0 := by
    intro c hc
    have hlast : exactifyCoef n N (Fin.last n) c (p (Fin.last n)) = 0 := by
      rw [exactifyCoef_last, if_neg hc]
    exact Finset.prod_eq_zero (Finset.mem_univ (Fin.last n)) hlast
  rw [show (∑ c : Fin n → Fin (N + 1), H c)
      = ∑ c ∈ (Finset.univ.filter valid : Finset (Fin n → Fin (N + 1))), H c by
        symm
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        intro c _
        by_cases hc : valid c
        · rw [if_pos hc]
        · rw [if_neg hc, hinvalid_zero c hc]]
  rw [coeff_prod_finsuppAntidiag (F := F) p N]
  -- Use `sum_bij` with the membership-dependent map, so the bound proof for `Fin (N+1)`
  -- can use the antidiagonal equation.
  refine (Finset.sum_bij
    (s := Finset.finsuppAntidiag (Finset.univ : Finset (Fin (n + 1))) N)
    (t := (Finset.univ.filter valid : Finset (Fin n → Fin (N + 1))))
    (f := fun l => ∏ i : Fin (n + 1), (p i).coeff (l i))
    (g := H)
    (fun l hl j => ⟨l j.castSucc, by
      have hsum := (Finset.mem_finsuppAntidiag.mp hl).1
      have hle : l j.castSucc ≤ N := by
        rw [← hsum]
        exact Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ j.castSucc)
      omega⟩)
    ?_ ?_ ?_ ?_).symm
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hsum := (Finset.mem_finsuppAntidiag.mp hl).1
    have hsplit : (∑ x : Fin (n + 1), l x)
        = (∑ j : Fin n, l j.castSucc) + l (Fin.last n) := by
      exact Fin.sum_univ_castSucc (fun x : Fin (n + 1) => l x)
    rw [hsplit] at hsum
    have : (∑ j : Fin n, l j.castSucc) ≤ N := by omega
    simpa using this
  · intro l₁ hl₁ l₂ hl₂ h
    apply Finsupp.ext
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact congrArg Fin.val (congrFun h j)
    · have hsum₁ := (Finset.mem_finsuppAntidiag.mp hl₁).1
      have hsum₂ := (Finset.mem_finsuppAntidiag.mp hl₂).1
      have hsplit₁ : (∑ x : Fin (n + 1), l₁ x)
          = (∑ j : Fin n, l₁ j.castSucc) + l₁ (Fin.last n) :=
        Fin.sum_univ_castSucc (fun x : Fin (n + 1) => l₁ x)
      have hsplit₂ : (∑ x : Fin (n + 1), l₂ x)
          = (∑ j : Fin n, l₂ j.castSucc) + l₂ (Fin.last n) :=
        Fin.sum_univ_castSucc (fun x : Fin (n + 1) => l₂ x)
      rw [hsplit₁] at hsum₁
      rw [hsplit₂] at hsum₂
      have hpref : (∑ j : Fin n, l₁ j.castSucc) = ∑ j : Fin n, l₂ j.castSucc := by
        refine Finset.sum_congr rfl ?_
        intro j _
        exact congrArg Fin.val (congrFun h j)
      omega
  · intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨_, hcvalid⟩ := hc
    let l : Fin (n + 1) →₀ ℕ :=
      Finsupp.onFinset Finset.univ
        (exactifyPart n N c)
        (by intro i _; simp)
    refine ⟨l, ?_, ?_⟩
    · rw [Finset.mem_finsuppAntidiag]
      constructor
      · dsimp [l]
        change (∑ x : Fin (n + 1), exactifyPart n N c x) = N
        rw [Fin.sum_univ_castSucc]
        simp [exactifyPart_castSucc, exactifyPart_last]
        rw [Nat.add_comm]
        exact Nat.sub_add_cancel hcvalid
      · exact fun x _ => Finset.mem_univ x
    · funext j
      dsimp [l]
      simp [exactifyPart_castSucc]
  · intro l hl
    dsimp [H]
    refine Finset.prod_congr rfl ?_
    intro i _
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp [exactifyCoef_castSucc]
    · have hsum := (Finset.mem_finsuppAntidiag.mp hl).1
      have hsplit : (∑ x : Fin (n + 1), l x)
          = (∑ j : Fin n, l j.castSucc) + l (Fin.last n) :=
        Fin.sum_univ_castSucc (fun x : Fin (n + 1) => l x)
      rw [hsplit] at hsum
      have hle : (∑ j : Fin n, l j.castSucc) ≤ N := by omega
      have hlast : l (Fin.last n) = N - ∑ j : Fin n, l j.castSucc := by omega
      simp [exactifyCoef_last, hle, hlast]

set_option linter.flexible false in
/-- **Step 2 — `q^{k−1}`-exactification** (Bürgisser §15.4, (15.7), GENERAL-`k` form;
    `burgisserbook.tex:11588-11594`).

    Bürgisser (15.7) states the BILINEAR (`k=3`) case: for a degree-`(q−1)` border
    restriction `t ⊴_q ⟨r⟩`, collecting the coefficient of `ε^{q−1}` realizes `t` as
    the full convolution `t = ∑_{ρ=1}^{r} ∑_{μ+ν+λ=q−1} u_ρ^{(μ)} ⊗ v_ρ^{(ν)} ⊗ w_ρ^{(λ)}`
    (`tex:11582-11588`), whence `t ⊴_q ⟨r⟩ ⟹ R(t) ≤ (q(q+1)/2)·r ≤ q²·r`
    (`tex:11590-11592`), `q²` being the structural rank of `k[ε]/(εᵠ)`.

    GENERAL `k`: the degree-`(q−1)` coefficient of the `k`-fold product
    `∏ᵢ Aᵢ(ε)` is the convolution `∑_{c₁+…+c_k=q−1, cᵢ≥0} ∏ᵢ Aᵢ.coeff cᵢ`, with
    `(q−1+k−1 choose k−1)` compositions.  The `⟨Q⟩` unit diagonal forces ONE shared
    overhead index across all `k` legs, so `Q` must encode every composition:
    `Q ≥ (q+k−2 choose k−1)`.  The clean valid bound is `Q = q^{k−1}`, via the
    injection `(c₁,…,c_k) ↦ (c₁,…,c_{k−1}) ∈ {0..q−1}^{k−1}` (`c_k := (q−1) − ∑`).
    Specializing: `k=2 → q¹` (linear anti-diagonal), `k=3 → q²` (Bürgisser's
    bilinear case), `k≥4 → q^{k−1}` (the bilinear `q²` is too SMALL).  As a
    `Restricts` statement, the overhead leg of size `q^{k−1}` carries this
    ε-convolution:

      `⟨m⟩ ⊴_q ψ ⟹ Restricts ⟨m⟩ (⟨q^{k−1}⟩ ⊠ ψ)`.

    Here a `BorderRestrictsWitness m hm ψ N A` packages a degree-`N` border
    restriction (its realized `ε`-order is `N = q−1`, so `q = N+1`); we instantiate at
    `q = N+1`, `m = s^n`, `ψ = T^{⊠n}`, overhead `⟨(N+1)^{k−1}⟩` (= `⟨q^{k−1}⟩`).

    Indexing the `Fin ((N+1)^{k−1})` overhead leg by
    `c̄ = (c₁,…,c_{k−1}) ∈ (Fin (N+1))^{k−1}` (`finFunctionFinEquiv`, card `(N+1)^{k−1}`),
    the restriction matrices read off `Bᵢ a ((c̄,b)) := (A i (cast a) b).coeff cᵢ`
    for `i<k−1`, and for the LAST leg `Bₖ a ((c̄,b)) := if (∑_{j<k−1} cⱼ) ≤ N then
    (A k (cast a) b).coeff (N − ∑_{j<k−1} cⱼ) else 0` (the `if … else 0` GUARD is
    load-bearing: ℕ-truncated subtraction would otherwise give `coeff 0` and inject
    spurious terms for the `c̄` whose first `k−1` parts already exceed `N`).  The
    `⟨(N+1)^{k−1}⟩`-diagonal forces a shared `c̄`, and the contraction reconstitutes
    `∑_{c₁+…+c_k=N} ∏ᵢ Aᵢ.coeff cᵢ · ψ_g = coeff_N P = ⟨m⟩`.  (The vanishing field of
    `hA` is UNUSED here — the identity reads `coeff_N` directly.)

    The coefficient bookkeeping uses the
    `k`-fold coefficient convolution is `PowerSeries.coeff_prod`
    (`Mathlib.RingTheory.PowerSeries.Basic:658`):
    `coeff d (∏ j, f j) = ∑ l ∈ finsuppAntidiag univ d, ∏ i, coeff (l i) (f i)`,
    pulled back along the polynomial→power-series coercion
    `change Polynomial.coeToPowerSeries.ringHom (∏ i, p i) = ∏ i, …; exact map_prod …`.
    The remaining bookkeeping is the bijection `finFunctionFinEquiv.symm` overhead
    index `↔ finsuppAntidiag univ N` (the diagonal collapse of `⟨Q⟩`), robust at
    `k=0,1`.  No false `(★)`, no extra hypotheses, overhead is the TRUE `(N+1)^{k−1}`. -/
theorem borderRestricts_exactify {d : Fin k → ℕ+} {m : ℕ} (hm : 0 < m)
    {ψ : KTensor F d} (N : ℕ)
    (A : ∀ i : Fin k, Fin m → Fin (d i) → Polynomial F)
    (hA : BorderRestrictsWitness m hm ψ N A) :
    Restricts
      (unitTensor F (k := k) ⟨m, hm⟩)
      (unitTensor F (k := k) ⟨(N + 1) ^ (k - 1), pow_pos (Nat.succ_pos _) (k - 1)⟩ ⊠ ψ) := by
  classical
  cases k with
  | zero =>
      refine ⟨fun i => Fin.elim0 i, ?_⟩
      intro jdx
      have hid := hA.2 jdx
      have hcoeff : (Polynomial.C (ψ (fun i : Fin 0 => Fin.elim0 i))).coeff N = (1 : F) := by
        simpa [unitTensor] using hid
      have hpsi : ψ (fun i : Fin 0 => Fin.elim0 i) = (1 : F) := by
        rw [Polynomial.coeff_C] at hcoeff
        by_cases hN : N = 0
        · simpa [hN] using hcoeff
        · rw [if_neg hN] at hcoeff
          exact False.elim (zero_ne_one hcoeff)
      simp [unitTensor, kroneckerTensor]
      exact hpsi.symm.trans (congrArg ψ (Subsingleton.elim _ _))
  | succ n =>
      let qPN : ℕ+ := ⟨(N + 1) ^ n, pow_pos (Nat.succ_pos _) n⟩
      let M : ∀ i : Fin (n + 1),
          Matrix (Fin ((⟨m, hm⟩ : ℕ+) : ℕ)) (Fin ((qPN * d i : ℕ+) : ℕ)) F :=
        fun i a idx =>
          let q : Fin qPN := (finProdFinEquiv.symm (by simpa [PNat.mul_coe] using idx)).1
          let b : Fin (d i) := (finProdFinEquiv.symm (by simpa [PNat.mul_coe] using idx)).2
          exactifyCoef n N i (finFunctionFinEquiv.symm q) (A i a b)
      refine ⟨M, ?_⟩
      intro jdx
      have hcoeff_contraction :
          (∑ g : ∀ i : Fin (n + 1), Fin (d i),
              ((∏ i : Fin (n + 1), A i (jdx i) (g i)) * Polynomial.C (ψ g))).coeff N
            = ∑ g : ∀ i : Fin (n + 1), Fin (d i),
                ((∏ i : Fin (n + 1), A i (jdx i) (g i)).coeff N) * ψ g := by
        rw [Polynomial.finset_sum_coeff]
        refine Finset.sum_congr rfl ?_
        intro g _
        rw [Polynomial.coeff_mul_C]
      have hid := hA.2 jdx
      rw [hcoeff_contraction] at hid
      rw [show unitTensor F (k := n + 1) ⟨m, hm⟩ jdx
          = ∑ g : ∀ i : Fin (n + 1), Fin (d i),
              ((∏ i : Fin (n + 1), A i (jdx i) (g i)).coeff N) * ψ g by
            simpa [Fin.cast_eq_self] using hid.symm]
      change (∑ g : ∀ i : Fin (n + 1), Fin (d i),
              ((∏ i : Fin (n + 1), A i (jdx i) (g i)).coeff N) * ψ g)
          = ∑ idx : ∀ i : Fin (n + 1), Fin ((qPN * d i : ℕ+) : ℕ),
              (∏ i : Fin (n + 1), M i (jdx i) (idx i)) *
                ((unitTensor F (k := n + 1) qPN ⊠ ψ) idx)
      -- Reindex the target contraction by the Kronecker index equivalence.
      rw [← (kronIndexEquiv (k := n + 1)
            (d₁ := fun _ : Fin (n + 1) => qPN) (d₂ := d)).symm.sum_comp
          (fun idx =>
            (∏ i : Fin (n + 1), M i (jdx i) (idx i)) *
              ((unitTensor F (k := n + 1) qPN ⊠ ψ) idx))]
      rw [Fintype.sum_prod_type]
      -- Compute the Kronecker projections of the recombined index.
      have hsum_pair :
          (∑ qIdx : ∀ i : Fin (n + 1), Fin qPN,
            ∑ gIdx : ∀ i : Fin (n + 1), Fin (d i),
              (∏ i : Fin (n + 1),
                  M i (jdx i)
                    (((kronIndexEquiv (k := n + 1)
                        (d₁ := fun _ : Fin (n + 1) => qPN) (d₂ := d)).symm
                        (qIdx, gIdx)) i)) *
                ((unitTensor F (k := n + 1) qPN ⊠ ψ)
                  ((kronIndexEquiv (k := n + 1)
                    (d₁ := fun _ : Fin (n + 1) => qPN) (d₂ := d)).symm
                    (qIdx, gIdx)))
            = ∑ qIdx : ∀ i : Fin (n + 1), Fin qPN,
                (∑ gIdx : ∀ i : Fin (n + 1), Fin (d i),
                  (∏ i : Fin (n + 1),
                    exactifyCoef n N i (finFunctionFinEquiv.symm (qIdx i))
                      (A i (jdx i) (gIdx i))) *
                    (unitTensor F (k := n + 1) qPN qIdx * ψ gIdx))) := by
        refine Finset.sum_congr rfl ?_
        intro qIdx _
        refine Finset.sum_congr rfl ?_
        intro gIdx _
        have hL : ∀ i : Fin (n + 1),
            kronLeftIndex (dS := fun _ : Fin (n + 1) => qPN) (dT := d)
              ((kronIndexEquiv (k := n + 1)
                (d₁ := fun _ : Fin (n + 1) => qPN) (d₂ := d)).symm (qIdx, gIdx)) i
              = qIdx i := by
          intro i
          have := congrArg Prod.fst
            (Equiv.symm_apply_apply finProdFinEquiv (qIdx i, gIdx i))
          simp only [finProdFinEquiv_symm_apply] at this
          exact this
        have hR : ∀ i : Fin (n + 1),
            kronRightIndex (dS := fun _ : Fin (n + 1) => qPN) (dT := d)
              ((kronIndexEquiv (k := n + 1)
                (d₁ := fun _ : Fin (n + 1) => qPN) (d₂ := d)).symm (qIdx, gIdx)) i
              = gIdx i := by
          intro i
          have := congrArg Prod.snd
            (Equiv.symm_apply_apply finProdFinEquiv (qIdx i, gIdx i))
          simp only [finProdFinEquiv_symm_apply] at this
          exact this
        have hT : (unitTensor F (k := n + 1) qPN ⊠ ψ)
              ((kronIndexEquiv (k := n + 1)
                (d₁ := fun _ : Fin (n + 1) => qPN) (d₂ := d)).symm (qIdx, gIdx))
            = unitTensor F (k := n + 1) qPN qIdx * ψ gIdx := by
          simp only [kroneckerTensor]
          rw [show kronLeftIndex
                ((kronIndexEquiv (k := n + 1)
                  (d₁ := fun _ : Fin (n + 1) => qPN) (d₂ := d)).symm (qIdx, gIdx))
                = qIdx by
                  funext i
                  exact hL i,
              show kronRightIndex
                ((kronIndexEquiv (k := n + 1)
                  (d₁ := fun _ : Fin (n + 1) => qPN) (d₂ := d)).symm (qIdx, gIdx))
                = gIdx by
                  funext i
                  exact hR i]
        rw [hT]
        congr 1
        refine Finset.prod_congr rfl ?_
        intro i _
        change
          exactifyCoef n N i
              (finFunctionFinEquiv.symm
                (kronLeftIndex (dS := fun _ : Fin (n + 1) => qPN) (dT := d)
                  ((kronIndexEquiv (k := n + 1)
                    (d₁ := fun _ : Fin (n + 1) => qPN) (d₂ := d)).symm
                    (qIdx, gIdx)) i))
              (A i (jdx i)
                (kronRightIndex (dS := fun _ : Fin (n + 1) => qPN) (dT := d)
                  ((kronIndexEquiv (k := n + 1)
                    (d₁ := fun _ : Fin (n + 1) => qPN) (d₂ := d)).symm
                    (qIdx, gIdx)) i))
            = exactifyCoef n N i (finFunctionFinEquiv.symm (qIdx i))
                (A i (jdx i) (gIdx i))
        rw [hL i, hR i]
      rw [hsum_pair]
      -- Collapse the unit-overhead diagonal and rebuild the coefficient of the product.
      rw [show
          (∑ qIdx : ∀ i : Fin (n + 1), Fin qPN,
            ∑ gIdx : ∀ i : Fin (n + 1), Fin (d i),
              (∏ i : Fin (n + 1),
                exactifyCoef n N i (finFunctionFinEquiv.symm (qIdx i))
                  (A i (jdx i) (gIdx i))) *
                (unitTensor F (k := n + 1) qPN qIdx * ψ gIdx))
          = ∑ qIdx : ∀ i : Fin (n + 1), Fin qPN,
              ((∑ gIdx : ∀ i : Fin (n + 1), Fin (d i),
                ((∏ i : Fin (n + 1),
                  exactifyCoef n N i (finFunctionFinEquiv.symm (qIdx i))
                    (A i (jdx i) (gIdx i))) * ψ gIdx))
                * unitTensor F (k := n + 1) qPN qIdx) by
            refine Finset.sum_congr rfl ?_
            intro qIdx _
            trans ∑ gIdx : ∀ i : Fin (n + 1), Fin (d i),
                ((∏ i : Fin (n + 1),
                  exactifyCoef n N i (finFunctionFinEquiv.symm (qIdx i))
                    (A i (jdx i) (gIdx i))) * ψ gIdx) *
                  unitTensor F (k := n + 1) qPN qIdx
            · refine Finset.sum_congr rfl ?_
              intro gIdx _
              ring
            · exact (Finset.sum_mul
                (s := (Finset.univ : Finset (∀ i : Fin (n + 1), Fin (d i))))
                (f := fun gIdx =>
                  ((∏ i : Fin (n + 1),
                    exactifyCoef n N i (finFunctionFinEquiv.symm (qIdx i))
                      (A i (jdx i) (gIdx i))) * ψ gIdx))
                (a := unitTensor F (k := n + 1) qPN qIdx)).symm]
      rw [unitTensor_diagonal_sum (F := F)
        (k := n + 1)
        (f := fun qIdx : (∀ i : Fin (n + 1), Fin qPN) =>
          ∑ gIdx : ∀ i : Fin (n + 1), Fin (d i),
            ((∏ i : Fin (n + 1),
              exactifyCoef n N i (finFunctionFinEquiv.symm (qIdx i))
                (A i (jdx i) (gIdx i))) * ψ gIdx))]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro gIdx _
      rw [← Finset.sum_mul]
      rw [show
          (∑ q : Fin qPN,
            ∏ i : Fin (n + 1),
              exactifyCoef n N i (finFunctionFinEquiv.symm q)
                (A i (jdx i) (gIdx i)))
          = (∏ i : Fin (n + 1), A i (jdx i) (gIdx i)).coeff N by
            simpa [qPN] using
              exactifyCoef_sum_eq_coeff (F := F) n N
                (fun i : Fin (n + 1) => A i (jdx i) (gIdx i))]

/-- **(a) `n`-th-power amplification of a border degeneration** — the CORRECT `q²`
    overhead, following Bürgisser §15.4 (15.7)+(15.8) and Strassen 1987 Prop 5.10.

    SOURCE (exact):
    * **Bürgisser §15.4 (15.8)** (`burgisserbook.tex:11598-11600`, Lemma (15.24)(3)
      `tex:11952`): `t₁ ⊴_{q₁} ⟨r₁⟩, t₂ ⊴_{q₂} ⟨r₂⟩ ⟹ t₁⊗t₂ ⊴_{q₁+q₂−1} ⟨r₁r₂⟩`.
    * **Bürgisser §15.4 (15.7)** (`burgisserbook.tex:11590-11592`):
      `t ⊴_q ⟨r⟩ ⟹ R(t) ≤ (q(q+1)/2)·r ≤ q²·r` over ANY field (`≤ (2q−1)r` if `k`
      infinite, `tex:11594`).  The `q²` is the structural rank of `k[ε]/(εᵠ)`.
    * **Strassen 1987, Proposition 5.10**
      (Strassen 1987, §6):
      the same amplification `aᴺ ≤ r·N²·bᴺ`, with the QUADRATIC `N²` overhead — cf.
      **Strassen 1988, Thm 3.1** (`strassen1988.tex:727`): "`aᴺ ≤ bᴺ·rN²`".

    From a degree-`N` border restriction `⟨s⟩ ⪰ T` (`BorderRestricts s hs T`):
    1. (step 1, `borderRestricts_kronPow`, Bürgisser (15.8)-iterated) the `n`-fold
       Kronecker power gives the degree-`N·n` border restriction
       `⟨sⁿ⟩ ⊴_{nN+1} T^{⊠n}`;
    2. (step 2, `borderRestricts_exactify`, Bürgisser (15.7) general-`k`) the
       `q^{k−1}`-exactification at `q = N·n+1` turns it into the EXACT restriction

         `⟨sⁿ⟩ ≤ₜ ⟨(N·n+1)^{k−1}⟩ ⊠ T^{⊠n}`,

       i.e. `Restricts (unitTensor ⟨sⁿ⟩) (unitTensor ⟨(N·n+1)^{k−1}⟩ ⊠ kronPowNat T (n-1))`.

    The overhead `(N·n+1)^{k−1}` is the general-`k` form of Bürgisser's `q²` (the `q²`
    is the `k=3` bilinear case; for `k≥4` it is too small).  The degree-`D` coefficient
    of the `k`-fold product is the convolution `∑_{c₁+…+c_k=D, cᵢ≥0} ∏ᵢ aᵢ.coeff cᵢ`,
    `(D+k−1 choose k−1)` compositions, all forced through ONE shared `⟨Q⟩` overhead
    index, so `Q = (D+1)^{k−1}` (the injection `(c₁,…,c_k) ↦ (c₁,…,c_{k−1})`).  Both
    overheads are POLYNOMIAL in `n` and wash out under the `1/n` root
    (`((N·n+1)^{k−1})^{1/n} = ((N·n+1)^{1/n})^{k−1} → 1`, see `washout_le`).

    This theorem composes of the two cited Bürgisser step lemmas
    `borderRestricts_kronPow` (15.8) + `borderRestricts_exactify` (15.7); the heavy
    `Polynomial.coeff` Cauchy-product bookkeeping is contained in those two
    individually cited step lemmas. -/
theorem borderRestricts_amplify {d : Fin k → ℕ+} {s : ℕ} (hs : 0 < s)
    {T : KTensor F d} (N : ℕ)
    (hA : ∃ (A : ∀ i : Fin k, Fin s → Fin (d i) → Polynomial F),
      (∀ ρ : ∀ i : Fin k, Fin s, ∀ n : ℕ, n < N →
        (∑ g : ∀ i : Fin k, Fin (d i),
          (∏ i, A i (ρ i) (g i)) * Polynomial.C (T g)).coeff n = 0) ∧
      (∀ ρ : ∀ i : Fin k, Fin s,
        (∑ g : ∀ i : Fin k, Fin (d i),
          (∏ i, A i (ρ i) (g i)) * Polynomial.C (T g)).coeff N
          = unitTensor F (k := k) ⟨s, hs⟩
              (fun i => (Fin.cast (by rfl) (ρ i) : Fin ((⟨s, hs⟩ : ℕ+) : ℕ)))))
    (n : ℕ) (hn : 1 ≤ n) :
    Restricts
      (unitTensor F (k := k) ⟨s ^ n, pow_pos hs n⟩)
      (unitTensor F (k := k) ⟨(N * n + 1) ^ (k - 1), pow_pos (Nat.succ_pos _) (k - 1)⟩
        ⊠ kronPowNat T (n - 1)) := by
  classical
  -- Unpack the degree-`N` border-restriction witness `A` of `⟨s⟩ ⪰ T`.
  obtain ⟨A, hAvan, hAid⟩ := hA
  have hAw : BorderRestrictsWitness s hs T N A := ⟨hAvan, hAid⟩
  -- Step 1 (Bürgisser (15.8) iterated): the n-fold Kronecker degeneration
  -- `⟨sⁿ⟩ ⊴_{nN+1} T^{⊠n}`, a degree-`N·n` border-restriction witness `B` of `⟨sⁿ⟩`
  -- into `kronPowNat T (n-1) = T^{⊠n}` (degree pinned exactly at `N·n`).
  obtain ⟨B, hBw⟩ :=
    borderRestricts_kronPow (F := F) (k := k) hs N A hAw n hn
  -- Step 2 (Bürgisser (15.7)): the `q²`-exactification at `q = (N·n)+1 = N·n+1`,
  -- producing the EXACT restriction with overhead `⟨(N·n+1)²⟩`.
  exact borderRestricts_exactify (F := F) (k := k) (m := s ^ n) (pow_pos hs n)
    (ψ := kronPowNat T (n - 1)) (N * n) B hBw

/-! ## (c) Washout: the polynomial overhead `(N·n+1)^{1/n} → 1`. -/

/-- The polynomial overhead washes out under the `1/n` exponent:
    `(N·n + 1)^{1/n} → 1` as `n → ∞`.

    `((N·n+1 : ℕ) : ℝ)^{1/n} = exp((1/n) · log(N·n+1))` and
    `(1/n) · log(N·n+1) → 0` (log grows slower than linearly, `log =o[atTop] id`),
    so the limit is `exp 0 = 1`. -/
private lemma tendsto_overhead_rpow (N : ℕ) :
    Filter.Tendsto (fun n : ℕ => ((N * n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / (n : ℝ)))
      Filter.atTop (nhds 1) := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · -- `N = 0`: the function is `1^{1/n} = 1`, constantly.
    subst hN0
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards with n
    simp
  · -- `N ≥ 1`: `(N·n+1)^{1/n} = exp((1/n)·log(N·n+1))` and `(1/n)·log(N·n+1) → 0`.
    -- `log(N·n+1)/n → 0`.
    have hlog : Filter.Tendsto
        (fun n : ℕ => Real.log ((N * n + 1 : ℕ) : ℝ) * ((1 : ℝ) / (n : ℝ)))
        Filter.atTop (nhds 0) := by
      -- `log` is little-o of `id`, so `log x / x → 0`; precompose with `x = N·n+1 → ∞`.
      have hdiv : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
        have := Real.isLittleO_log_id_atTop
        simpa [div_eq_mul_inv] using
          (Asymptotics.IsLittleO.tendsto_div_nhds_zero this)
      have hAt : Filter.Tendsto (fun n : ℕ => ((N * n + 1 : ℕ) : ℝ))
          Filter.atTop Filter.atTop := by
        apply Filter.tendsto_atTop_mono (fun n => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
        · have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNpos
          push_cast
          nlinarith [Nat.cast_nonneg (α := ℝ) n]
      have hcomp : Filter.Tendsto
          (fun n : ℕ => Real.log ((N * n + 1 : ℕ) : ℝ) / ((N * n + 1 : ℕ) : ℝ))
          Filter.atTop (nhds 0) := hdiv.comp hAt
      -- `log(N·n+1) * (1/n) = (log(N·n+1)/(N·n+1)) * ((N·n+1)/n)` and `(N·n+1)/n → N`.
      have hratio : Filter.Tendsto (fun n : ℕ => ((N * n + 1 : ℕ) : ℝ) / (n : ℝ))
          Filter.atTop (nhds (N : ℝ)) := by
        have heq : (fun n : ℕ => ((N * n + 1 : ℕ) : ℝ) / (n : ℝ))
            =ᶠ[Filter.atTop] (fun n : ℕ => (N : ℝ) + (1 : ℝ) / (n : ℝ)) := by
          filter_upwards [Filter.eventually_gt_atTop 0] with n hn
          have hn0 : (n : ℝ) ≠ 0 := by positivity
          push_cast
          field_simp
        rw [Filter.tendsto_congr' heq]
        have h1n : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) :=
          tendsto_one_div_atTop_nhds_zero_nat
        simpa using (tendsto_const_nhds.add h1n)
      have hmul := hcomp.mul hratio
      rw [zero_mul] at hmul
      refine hmul.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hden : ((N * n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp
    -- `(N·n+1)^{1/n} = exp((1/n)·log(N·n+1))`, continuous `exp`, limit `exp 0 = 1`.
    have hpos : ∀ n : ℕ, (0 : ℝ) < ((N * n + 1 : ℕ) : ℝ) := fun n => by positivity
    have hrw : (fun n : ℕ => ((N * n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / (n : ℝ)))
        =ᶠ[Filter.atTop]
        (fun n : ℕ => Real.exp (Real.log ((N * n + 1 : ℕ) : ℝ) * ((1 : ℝ) / (n : ℝ)))) := by
      filter_upwards with n
      rw [Real.rpow_def_of_pos (hpos n), mul_comm]
    rw [Filter.tendsto_congr' hrw]
    have := (Real.continuous_exp.tendsto 0).comp hlog
    simpa using this

/-- **(c) Washout bound** (Strassen 1991, tex:88-95).  If for every `n ≥ 1` the
    amplified bound `s^n ≤ (N·n+1) · Q^n` holds (with `0 ≤ Q`), then `s ≤ Q`.

    Take `n`-th roots: `s ≤ (N·n+1)^{1/n} · Q`, and `(N·n+1)^{1/n} → 1`
    (`tendsto_overhead_rpow`), so the RHS `→ Q`; since `s ≤` each term, `s ≤ Q`
    by `le_of_tendsto'`. -/
private lemma washout_le (s N e : ℕ) (Q : ℝ) (hQ : 0 ≤ Q)
    (hbound : ∀ n : ℕ, 1 ≤ n → (s : ℝ) ^ n ≤ (((N * n + 1) ^ e : ℕ) : ℝ) * Q ^ n) :
    (s : ℝ) ≤ Q := by
  -- The `e`-power overhead still washes out: `((N·n+1)^e)^{1/n} = ((N·n+1)^{1/n})^e → 1^e`
  -- via `x ↦ x^e` continuity composed with `tendsto_overhead_rpow`.
  have htend_sq : Filter.Tendsto
      (fun n : ℕ => (((N * n + 1) ^ e : ℕ) : ℝ) ^ ((1 : ℝ) / (n : ℝ)))
      Filter.atTop (nhds 1) := by
    -- `((N·n+1)^e)^{1/n} = ((N·n+1)^{1/n})^e`.
    have hrw : (fun n : ℕ => (((N * n + 1) ^ e : ℕ) : ℝ) ^ ((1 : ℝ) / (n : ℝ)))
        =ᶠ[Filter.atTop]
        (fun n : ℕ => (((N * n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / (n : ℝ))) ^ e) := by
      filter_upwards with n
      have hbase : (((N * n + 1) ^ e : ℕ) : ℝ) = ((N * n + 1 : ℕ) : ℝ) ^ (e : ℕ) := by
        push_cast; ring
      rw [hbase, ← Real.rpow_natCast (((N * n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / (n : ℝ))) e,
          ← Real.rpow_natCast ((N * n + 1 : ℕ) : ℝ) e,
          ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity),
          mul_comm ((1 : ℝ) / (n : ℝ)) ((e : ℕ) : ℝ)]
    rw [Filter.tendsto_congr' hrw]
    have := (tendsto_overhead_rpow N).pow e
    simpa using this
  -- The comparison sequence `c n = ((N·n+1)^e)^{1/n} · Q → Q`.
  have htend : Filter.Tendsto
      (fun n : ℕ => (((N * n + 1) ^ e : ℕ) : ℝ) ^ ((1 : ℝ) / (n : ℝ)) * Q)
      Filter.atTop (nhds Q) := by
    have := htend_sq.mul_const Q
    simpa using this
  -- `s ≤ c n` for `n ≥ 1`: raise the amplified bound to the `1/n` power.
  refine ge_of_tendsto htend ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hexp_nonneg : (0 : ℝ) ≤ (1 : ℝ) / (n : ℝ) := by positivity
  -- Raise `s^n ≤ (N·n+1)^e·Q^n` to the `1/n` power.
  have hb := hbound n hn
  have hmono := Real.rpow_le_rpow (by positivity) hb hexp_nonneg
  -- LHS: `(s^n)^{1/n} = s`.
  have hlhs : ((s : ℝ) ^ n) ^ ((1 : ℝ) / (n : ℝ)) = (s : ℝ) := by
    rw [← Real.rpow_natCast (s : ℝ) n, ← Real.rpow_mul (by positivity)]
    rw [mul_one_div, div_self (ne_of_gt hnpos), Real.rpow_one]
  -- RHS: `((N·n+1)^e·Q^n)^{1/n} = ((N·n+1)^e)^{1/n}·Q`.
  have hrhs : ((((N * n + 1) ^ e : ℕ) : ℝ) * Q ^ n) ^ ((1 : ℝ) / (n : ℝ))
      = (((N * n + 1) ^ e : ℕ) : ℝ) ^ ((1 : ℝ) / (n : ℝ)) * Q := by
    rw [Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast Q n, ← Real.rpow_mul hQ]
    rw [mul_one_div, div_self (ne_of_gt hnpos), Real.rpow_one]
  rw [hlhs, hrhs] at hmono
  exact hmono

/-- **Strassen 1991** (tex:44-95), the border-degeneration → asymptotic-subrank
    bridge.  For any `KTensor` `T` (over `k ≥ 2` legs, the Cor 3.5 regime),

      `(borderSubrank T : ℝ) ≤ asympSubrank T`.

    PROOF (Strassen/Bini amplification, tex:64-95).  Mirrors the gapped /
    non-gapped case split of `FieldInvariance.asympSubrank_baseChange`.  Let `s` be
    any value admitted by `borderSubrank` via a degree-`N` border restriction
    `⟨s⟩ ⪰ T` (`BorderRestricts s hs T`).  Raising the degeneration to its `n`-th
    Kronecker power (Bürgisser (15.8)) and `q^{k−1}`-exactifying (Bürgisser (15.7)
    general-`k`, `q = N·n+1`) yields the **exact** restriction
    `⟨s^n⟩ ≤ₜ ⟨(N·n+1)^{k−1}⟩ ⊠ T^{⊠n}` (`borderRestricts_amplify`, the
    general-`k` overhead per Bürgisser §15.4 / Strassen 1987 Prop 5.10's `r·N²`, of
    which `q²` is the `k=3` bilinear case).

    * **Gapped** `T`.  Since
      `mk ⟨_, kronPowNat T (n-1)⟩ = (mk ⟨d,T⟩)^n` (`mkPow`) and gappedness is
      closed under powers (`isGapped_pow`), the unit-overhead lemma
      `subrank_of_restricts_unit_overhead` (T4, whose RHS is `asympSubrank`) gives
      `s^n ≤ (N·n+1)^{k−1} · asympSubrank (T^{⊠n}) = (N·n+1)^{k−1} · asympSubrank T ^ n`
      (`asympSubrank_kronPowNat`, T2, needs `mk ⟨d,T⟩ ≠ 0`).  The washout
      `washout_le` (`((N·n+1)^{k−1})^{1/n} → 1`, `tendsto_overhead_rpow` `^(k−1)`) gives
      `s ≤ asympSubrank T`; `csSup` over `s` gives the claim.  The unit-overhead is
      handled at the *spectral* level (T4), NEVER via the FALSE
      `subrank (⟨q⟩ ⊠ S) ≤ q·subrank S`.

    * **Non-gapped** `T` (via the field-general Lemma A, survey:2286-2297).
      Non-gappedness gives subrank-1-stability; the corrected all-bipartition
      Lemma A contrapositive (`exists_flatRank_cut_le_one_of_subrank_stable`)
      forces some *bipartition* cut `Scut` with `flatRank T Scut ≤ 1`, and the
      general-cut `borderRestricts_le_flatRank` bounds the border restriction
      `s ≤ flatRank T Scut ≤ 1 ≤ asympSubrank T`.  (The old singleton form of this
      step was FALSE for the disconnected-partner counterexample; see
      `UnitOverhead.ghz_extend` for the load-bearing `i ∈ S` repair.)

    HYPOTHESIS `hk : 2 ≤ k`.  The Cor 3.5 regime (two distinct legs), required by
    T2/T4 and the spectral bridge, exactly as the sibling
    `FieldInvariance.asympSubrank_baseChange` carries `i₁ ≠ i₀`. -/
theorem borderSubrank_le_asympSubrank [NeZero k] (hk : 2 ≤ k)
    {d : Fin k → ℕ+} (T : KTensor F d) :
    (borderSubrank T : ℝ) ≤ asympSubrank T := by
  classical
  set pF := tensorStrassenPreorder (F := F) hk with hpF
  set aF : TensorClass F k := TensorClass.mk ⟨d, T⟩ with haF
  -- `asympSubrank T ≥ 0` (nonneg `sSup`).
  have hQnn : (0 : ℝ) ≤ asympSubrank T := asympSubrank_nonneg' hk T
  -- It suffices to bound every member `s` of the `borderSubrank` set by `asympSubrank T`.
  have hmem_le : ∀ s ∈ { s : ℕ | ∃ hs : 0 < s, BorderRestricts s hs T },
      (s : ℝ) ≤ asympSubrank T := by
    rintro s ⟨hs, hBR⟩
    obtain ⟨N, A, hvanish, hident⟩ := hBR
    -- Amplification hypothesis packaged for `borderRestricts_amplify`.
    have hAex : ∃ (A : ∀ i : Fin k, Fin s → Fin (d i) → Polynomial F),
        (∀ ρ : ∀ i : Fin k, Fin s, ∀ m : ℕ, m < N →
          (∑ g : ∀ i : Fin k, Fin (d i),
            (∏ i, A i (ρ i) (g i)) * Polynomial.C (T g)).coeff m = 0) ∧
        (∀ ρ : ∀ i : Fin k, Fin s,
          (∑ g : ∀ i : Fin k, Fin (d i),
            (∏ i, A i (ρ i) (g i)) * Polynomial.C (T g)).coeff N
            = unitTensor F (k := k) ⟨s, hs⟩
                (fun i => (Fin.cast (by rfl) (ρ i) : Fin ((⟨s, hs⟩ : ℕ+) : ℕ)))) :=
      ⟨A, hvanish, hident⟩
    by_cases hgapF : pF.IsGapped aF
    · -- GAPPED case.
      by_cases haF0 : aF = (0 : TensorClass F k)
      · -- `aF = 0` (`T ∼ₜ 0`): both `asympSubrank T` and every
        -- `asympSubrank (kronPowNat T (n-1))` vanish (their classes are `0 = aF^n`,
        -- and `pF.asympSubrank 0 = 0` by `asympSubrank_natCast 0`).  The washout
        -- with `Q = 0` then gives `s ≤ 0`.
        have hQ0 : asympSubrank T = 0 := by
          rw [asympSubrank_eq_abstract hk T, ← haF, haF0]
          have : (0 : TensorClass F k) = ((0 : ℕ) : TensorClass F k) := by simp
          rw [this, (tensorStrassenPreorder (F := F) hk).asympSubrank_natCast]
          simp
        rw [hQ0]
        refine washout_le s N (k - 1) (0 : ℝ) le_rfl ?_
        intro n hn
        -- amplification at exponent `n`.
        have hamp := borderRestricts_amplify (F := F) (k := k) hs N hAex n hn
        have hpow_eq : aF ^ n = TensorClass.mk ⟨_, kronPowNat T (n - 1)⟩ := by
          rw [haF, ← mkPow T (n - 1)]; congr 1; omega
        have hgp : pF.IsGapped (aF ^ n) := isGapped_pow hgapF hn
        have hgp' : (tensorStrassenPreorder (F := F) hk).IsGapped
            (TensorClass.mk ⟨_, kronPowNat T (n - 1)⟩) := by rwa [hpow_eq, hpF] at hgp
        have hT4 := subrank_of_restricts_unit_overhead (F := F) hk
          ⟨s ^ n, pow_pos hs n⟩ ⟨(N * n + 1) ^ (k - 1), pow_pos (Nat.succ_pos _) (k - 1)⟩ T (n - 1)
          hgp' hamp
        -- `asympSubrank (kronPowNat T (n-1)) = 0` since its class is `aF^n = 0`.
        have hclass0 : TensorClass.mk ⟨_, kronPowNat T (n - 1)⟩ = (0 : TensorClass F k) := by
          rw [← hpow_eq, haF0, zero_pow (by omega : n ≠ 0)]
        have hAS0 : asympSubrank (kronPowNat T (n - 1)) = 0 := by
          rw [asympSubrank_eq_abstract hk (kronPowNat T (n - 1)), hclass0, ← hpF]
          have h0 : (0 : TensorClass F k) = ((0 : ℕ) : TensorClass F k) := by simp
          rw [h0, pF.asympSubrank_natCast]; simp
        rw [hAS0, mul_zero] at hT4
        rw [zero_pow (by omega : n ≠ 0), mul_zero]
        -- `hT4 : ↑↑⟨s^n⟩ ≤ 0`; goal `↑s^n ≤ 0`.  Same value up to cast.
        have hcast : ((⟨s ^ n, pow_pos hs n⟩ : ℕ+) : ℝ) = (s : ℝ) ^ n := by push_cast; ring
        rw [← hcast]
        exact hT4
      · -- `aF ≠ 0`: the general argument.
        refine washout_le s N (k - 1) (asympSubrank T) hQnn ?_
        intro n hn
        -- (a) amplification at exponent `n`.
        have hamp := borderRestricts_amplify (F := F) (k := k) hs N hAex n hn
        -- gappedness of the power `aF^n = mk (kronPowNat T (n-1))`.
        have hpow_eq : aF ^ n = TensorClass.mk ⟨_, kronPowNat T (n - 1)⟩ := by
          rw [haF, ← mkPow T (n - 1)]; congr 1; omega
        have hgp : pF.IsGapped (aF ^ n) := isGapped_pow hgapF hn
        have hgp' : (tensorStrassenPreorder (F := F) hk).IsGapped
            (TensorClass.mk ⟨_, kronPowNat T (n - 1)⟩) := by
          rwa [hpow_eq, hpF] at hgp
        -- (b) T4: `s^n ≤ (N·n+1)² · asympSubrank (kronPowNat T (n-1))`.
        have hT4 := subrank_of_restricts_unit_overhead (F := F) hk
          ⟨s ^ n, pow_pos hs n⟩ ⟨(N * n + 1) ^ (k - 1), pow_pos (Nat.succ_pos _) (k - 1)⟩ T (n - 1)
          hgp' hamp
        -- T2: `asympSubrank (kronPowNat T (n-1)) = asympSubrank T ^ n`.
        have hT2 : asympSubrank (kronPowNat T (n - 1)) = asympSubrank T ^ n := by
          rw [asympSubrank_kronPowNat hk T (by rwa [haF] at haF0)]
          congr 1; omega
        -- Assemble the per-`n` bound.  `hT4 : ↑↑⟨s^n⟩ ≤ ↑↑⟨(N·n+1)²⟩ · asympSubrank(…)`.
        rw [hT2] at hT4
        have hcast_s : ((⟨s ^ n, pow_pos hs n⟩ : ℕ+) : ℝ) = (s : ℝ) ^ n := by push_cast; ring
        have hcast_q : ((⟨(N * n + 1) ^ (k - 1), pow_pos (Nat.succ_pos _) (k - 1)⟩ : ℕ+) : ℝ)
            = (((N * n + 1) ^ (k - 1) : ℕ) : ℝ) := by push_cast; ring
        rw [← hcast_s, ← hcast_q]
        exact hT4
    · -- Non-gapped case (via the field-general Lemma A + border-flatRank,
      -- survey tex:2286-2297).  Non-gappedness ⟹ subrank-1-stable ⟹ some
      -- bipartition cut `Scut` with `flatRank T Scut ≤ 1`; `borderRestricts_le_flatRank`
      -- then bounds the border restriction `s ≤ flatRank T Scut ≤ 1 ≤ asympSubrank T`.
      have hno_strict : ∀ m : ℕ, 0 < m → ¬ pF.rel (2 : TensorClass F k) (aF ^ m) := by
        intro m hm h2; exact hgapF (Or.inl ⟨m, hm, h2⟩)
      have hnot_zero : ¬ pF.rel aF (0 : TensorClass F k) := fun h0 => hgapF (Or.inr (Or.inl h0))
      -- (1) subrank-1-stability over `F`.
      have hstable : ∀ n : ℕ, subrank (kronPowNat T n) ≤ 1 := by
        intro n
        have hns := hno_strict (n + 1) (Nat.succ_pos n)
        rw [mkPow T n] at hns
        have h2cast : (2 : TensorClass F k) = ((2 : ℕ) : TensorClass F k) := by norm_cast
        rw [h2cast] at hns
        have hnle : ¬ (2 : ℕ) ≤ pF.subrank (TensorClass.mk ⟨_, kronPowNat T n⟩) :=
          fun hle => hns ((pF.le_subrank_iff _ 2).mp hle)
        have hbridge : pF.subrank (TensorClass.mk ⟨_, kronPowNat T n⟩)
            = subrank (kronPowNat T n) := (subrank_eq_abstract hk (kronPowNat T n)).symm
        rw [hbridge] at hnle
        omega
      -- (2) Corrected Lemma A contrapositive: some *bipartition* cut `Scut` has
      --     `flatRank T Scut ≤ 1` (survey:2286-2297).
      obtain ⟨Scut, hScut_ne, hScut_univ, hflat⟩ :=
        exists_flatRank_cut_le_one_of_subrank_stable hk T hstable
      obtain ⟨i₀, hi₀⟩ := hScut_ne
      obtain ⟨i₁, hi₁⟩ : ∃ i₁, i₁ ∉ Scut := by
        by_contra hc; push_neg at hc
        exact hScut_univ (Finset.eq_univ_of_forall hc)
      -- (3) `s ≤ flatRank T Scut ≤ 1` (border restriction does not exceed flattening rank).
      have hs_le : s ≤ flatRank T Scut :=
        borderRestricts_le_flatRank hs Scut hi₀ hi₁ ⟨N, A, hvanish, hident⟩
      have hs_le_one : s ≤ 1 := le_trans hs_le hflat
      -- (4) `1 ≤ asympSubrank T` (nonzero `T`): `subrank T ≥ 1`, and `asympSubrank ≥ gF 0`.
      have haF_ne : (TensorClass.mk ⟨d, T⟩ : TensorClass F k) ≠ 0 := by
        intro h0; exact hnot_zero (by rw [haF, h0]; exact pF.refl 0)
      have hone_sub : 1 ≤ subrank T := by
        have h0 : (0 : ℕ) < k := by omega
        have h1 : (1 : ℕ) < k := by omega
        have hne01 : (⟨1, h1⟩ : Fin k) ≠ ⟨0, h0⟩ := by simp [Fin.ext_iff]
        have hres : Restricts (unitTensor F (k := k) 1) T :=
          unitTensor_one_restricts_of_ne_zero T haF_ne
        have hmem : (1 : ℕ) ∈ { r : ℕ | ∃ hr : 0 < r,
            Restricts (unitTensor F (k := k) ⟨r, hr⟩) T } := ⟨one_pos, by simpa using hres⟩
        exact le_csSup (subrank_set_bddAbove' ⟨0, h0⟩ ⟨1, h1⟩ hne01 T) hmem
      have hone_le_Q : (1 : ℝ) ≤ asympSubrank T := by
        have hQeq : asympSubrank T = sSup (Set.range (fun n : ℕ =>
            (subrank (kronPowNat T n) : ℝ) ^ ((1 : ℝ) / ((n : ℝ) + 1)))) := rfl
        have hbddQ : BddAbove (Set.range (fun n : ℕ =>
            (subrank (kronPowNat T n) : ℝ) ^ ((1 : ℝ) / ((n : ℝ) + 1)))) :=
          concrete_asympSubrankSet_bddAbove hk T
        have hmem0 : (subrank (kronPowNat T 0) : ℝ) ^ ((1 : ℝ) / (((0 : ℕ) : ℝ) + 1))
            ∈ Set.range (fun n : ℕ =>
              (subrank (kronPowNat T n) : ℝ) ^ ((1 : ℝ) / ((n : ℝ) + 1))) := ⟨0, rfl⟩
        have hterm0 : (1 : ℝ) ≤ (subrank (kronPowNat T 0) : ℝ)
            ^ ((1 : ℝ) / (((0 : ℕ) : ℝ) + 1)) := by
          have : (subrank (kronPowNat T 0) : ℝ) = (subrank T : ℝ) := by
            simp [kronPowNat]
          rw [this]
          simp only [Nat.cast_zero, zero_add, div_one, Real.rpow_one]
          exact_mod_cast hone_sub
        rw [hQeq]
        exact le_trans hterm0 (le_csSup hbddQ hmem0)
      -- Assemble: `(s:ℝ) ≤ 1 ≤ asympSubrank T`.
      calc (s : ℝ) ≤ (1 : ℝ) := by exact_mod_cast hs_le_one
        _ ≤ asympSubrank T := hone_le_Q
  -- `csSup` of the `borderSubrank` set is `≤ asympSubrank T`.
  unfold borderSubrank
  have hbound : sSup { s : ℕ | ∃ hs : 0 < s, BorderRestricts s hs T }
      ≤ ⌊asympSubrank T⌋₊ := by
    apply csSup_le'
    intro s hs
    rw [Nat.le_floor_iff hQnn]
    exact hmem_le s hs
  calc ((sSup { s : ℕ | ∃ hs : 0 < s, BorderRestricts s hs T } : ℕ) : ℝ)
      ≤ (⌊asympSubrank T⌋₊ : ℝ) := by exact_mod_cast hbound
    _ ≤ asympSubrank T := Nat.floor_le hQnn

end Semicontinuity
