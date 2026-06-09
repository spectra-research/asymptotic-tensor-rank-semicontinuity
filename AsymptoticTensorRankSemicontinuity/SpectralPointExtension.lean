/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.TensorClassBaseChange
import AsymptoticTensorRankSemicontinuity.TensorStrassenPreorder
import AsymptoticTensorRankSemicontinuity.Prerequisites.AsymptoticSpectrumDuality.Surjectivity
import AsymptoticTensorRankSemicontinuity.Prerequisites.AsymptoticSpectrumDuality.Maximal
import AsymptoticTensorRankSemicontinuity.Prerequisites.AsymptoticSpectrumDuality.Duality

/-!
# The abstract ↔ concrete `SpectralPoint` bridge and `exists_spectralPoint_extension`

This file relates concrete spectral points on tensor classes to the abstract
spectral points for the Strassen preorder.

* **(5a)** `toAbstractSpectralPoint` — turn a concrete `SpectralPoint k F`
  (`SpectrumDescend.lean`) into an abstract
  `AsymptoticSpectrumDuality.SpectralPoint (tensorStrassenPreorder hk)`.
* **(5b)** `ofAbstractSpectralPoint` — the converse.
* **(5c)** `upgrade` / `downgrade` — move a spectral point between a Strassen
  preorder `p` and its asymptotic preorder `asympPreorder p`.
* `tensorClass_hord` — base-change order embedding (Strassen 1988
  Theorem 3.10, strassen1988.tex:1264 / Strassen 1987 Proposition 5.3(i),
  strassen1987.tex:873): base change is an order-embedding for the asymptotic
  preorders.
* **(6)** `exists_spectralPoint_extension_bridge` — every concrete spectral
  point over `F` extends to one over a field extension `K`, agreeing on
  base-changed tensors.
-/

namespace Semicontinuity

open AsymptoticSpectrumDuality

universe u

variable {F : Type u} [Field F] {K : Type u} [Field K] [Algebra F K] {k : ℕ}

/-! ## (5a) concrete → abstract spectral point. -/

/-- A concrete spectral point sends the canonical zero tensor to `0`.

`Fspec.add zeroT zeroT` gives `Fspec(zeroT ⊕ₜ zeroT) = 2 · Fspec zeroT`, while
`zeroT ⊕ₜ zeroT ∼ₜ zeroT` (both are zero tensors) gives the left side equals
`Fspec zeroT`; hence `Fspec zeroT = 0`. -/
lemma SpectralPoint.toFun_zeroT [NeZero k] (Fspec : SpectralPoint k F) :
    Fspec.toFun (zeroT (F := F) (k := k)) = 0 := by
  have hadd := Fspec.add (zeroT (F := F) (k := k)) (zeroT (F := F) (k := k))
  -- `zeroT ⊕ₜ zeroT ∼ₜ zeroT`: `zeroT` is defeq to `(0 : KTensor F (fun _ => 1))`,
  -- so `zero_directSum` applies.
  have hequiv : (zeroT (F := F) (k := k) ⊕ₜ zeroT (F := F) (k := k))
      ∼ₜ zeroT (F := F) (k := k) :=
    zero_directSum (dZ := fun _ => (1 : ℕ+)) (zeroT (F := F) (k := k))
  have hinv : Fspec.toFun (zeroT (F := F) (k := k) ⊕ₜ zeroT (F := F) (k := k))
      = Fspec.toFun (zeroT (F := F) (k := k)) :=
    le_antisymm (Fspec.mono _ _ hequiv.1) (Fspec.mono _ _ hequiv.2)
  rw [hinv] at hadd
  linarith

/-- **Concrete → abstract spectral point** (concrete-to-abstract construction).

Lift a concrete `SpectralPoint k F` to an abstract spectral point on the
`StrassenPreorder (TensorClass F k)`. The function descends to the `∼ₜ`-quotient
because `Fspec` is restriction-monotone in both directions, hence
`∼ₜ`-invariant. -/
noncomputable def toAbstractSpectralPoint (hk : 2 ≤ k) (Fspec : SpectralPoint k F) :
    haveI : NeZero k := ⟨by omega⟩
    AsymptoticSpectrumDuality.SpectralPoint (tensorStrassenPreorder (F := F) hk) :=
  haveI : NeZero k := ⟨by omega⟩
  { toFun := Quotient.lift (fun a : TT F k => Fspec.toFun a.2)
      (by
        rintro a b ⟨hab, hba⟩
        exact le_antisymm (Fspec.mono a.2 b.2 hab) (Fspec.mono b.2 a.2 hba))
    map_zero := by
      -- abstract `0 = ⟦⟨_, zeroT⟩⟧`; `Fspec zeroT = 0` via additivity.
      change Quotient.lift (fun a : TT F k => Fspec.toFun a.2) _ (0 : TensorClass F k) = 0
      rw [TensorClass.zero_def]
      exact SpectralPoint.toFun_zeroT Fspec
    map_one := by
      change Quotient.lift (fun a : TT F k => Fspec.toFun a.2) _ (1 : TensorClass F k) = 1
      rw [TensorClass.one_def]
      change Fspec.toFun (unitTensor F (k := k) 1) = 1
      have := Fspec.normalize (1 : ℕ+)
      simpa using this
    map_add := by
      rintro ⟨a⟩ ⟨b⟩
      change Fspec.toFun ((a.2 ⊕ₜ b.2)) = Fspec.toFun a.2 + Fspec.toFun b.2
      exact Fspec.add a.2 b.2
    map_mul := by
      rintro ⟨a⟩ ⟨b⟩
      change Fspec.toFun ((a.2 ⊠ b.2)) = Fspec.toFun a.2 * Fspec.toFun b.2
      exact Fspec.mult a.2 b.2
    monotone := by
      rintro ⟨a⟩ ⟨b⟩ hab
      exact Fspec.mono a.2 b.2 hab
    nonneg := by
      rintro ⟨a⟩
      change 0 ≤ Fspec.toFun a.2
      -- `0 = Fspec zeroT ≤ Fspec a.2` since `zeroT ≤ₜ a.2`.
      have hmono := Fspec.mono (zeroT : KTensor F (fun _ => (1 : ℕ+))) a.2
        (zeroT_restricts a.2)
      rw [SpectralPoint.toFun_zeroT Fspec] at hmono
      exact hmono }

/-! ## (5b) abstract → concrete spectral point. -/

/-- `ψ` sends the semiring-`natCast` of `n` to `(n : ℝ)`. Helper for the
`normalize` field of `ofAbstractSpectralPoint`. -/
lemma abstractSpectralPoint_natCast (hk : 2 ≤ k)
    (ψ : haveI : NeZero k := ⟨by omega⟩
      AsymptoticSpectrumDuality.SpectralPoint (tensorStrassenPreorder (F := K) hk)) (n : ℕ) :
    haveI : NeZero k := ⟨by omega⟩
    ψ.toFun ((n : TensorClass K k)) = (n : ℝ) := by
  haveI : NeZero k := ⟨by omega⟩
  induction n with
  | zero => simp [ψ.map_zero]
  | succ m ih => rw [Nat.cast_succ, ψ.map_add, ψ.map_one, ih]; push_cast; ring

/-- **Abstract → concrete spectral point** (abstract-to-concrete construction). -/
noncomputable def ofAbstractSpectralPoint (hk : 2 ≤ k)
    (ψ : haveI : NeZero k := ⟨by omega⟩
      AsymptoticSpectrumDuality.SpectralPoint (tensorStrassenPreorder (F := K) hk)) :
    SpectralPoint k K :=
  haveI : NeZero k := ⟨by omega⟩
  { toFun := fun {d} (T : KTensor K d) => ψ.toFun (TensorClass.mk ⟨d, T⟩)
    mult := by
      intro dS dT S T
      show ψ.toFun (TensorClass.mk ⟨_, S ⊠ T⟩)
        = ψ.toFun (TensorClass.mk ⟨dS, S⟩) * ψ.toFun (TensorClass.mk ⟨dT, T⟩)
      rw [← ψ.map_mul]
      rfl
    add := by
      intro dS dT S T
      show ψ.toFun (TensorClass.mk ⟨_, S ⊕ₜ T⟩)
        = ψ.toFun (TensorClass.mk ⟨dS, S⟩) + ψ.toFun (TensorClass.mk ⟨dT, T⟩)
      rw [← ψ.map_add]
      rfl
    normalize := by
      intro r
      show ψ.toFun (TensorClass.mk ⟨_, unitTensor K (k := k) r⟩) = (r : ℕ)
      -- `⟦unitTensor r⟧ = unitClass r = (r : TensorClass)`.
      have hr : (TensorClass.mk ⟨_, unitTensor K (k := k) r⟩ : TensorClass K k)
          = ((r : ℕ) : TensorClass K k) := by
        rw [natCast_eq_unitClass, unitClass, dif_pos r.pos]
        have : (⟨(r : ℕ), r.pos⟩ : ℕ+) = r := by ext; rfl
        rw [this]
      rw [hr, abstractSpectralPoint_natCast hk ψ]
    mono := by
      intro dS dT S T hST
      show ψ.toFun (TensorClass.mk ⟨dS, S⟩) ≤ ψ.toFun (TensorClass.mk ⟨dT, T⟩)
      exact ψ.monotone _ _ hST }

/-! ## (5c) asymp upgrade / downgrade. -/

variable {S : Type*} [CommSemiring S]

/-- **Upgrade** (asymptotic-preorder construction): a spectral point for `p` is a spectral point
for `asympPreorder p`. The monotonicity under `AsympRel p` is the framework's
`asymp_implies_spectral`. -/
noncomputable def upgrade (p : StrassenPreorder S)
    (φ : AsymptoticSpectrumDuality.SpectralPoint p) :
    AsymptoticSpectrumDuality.SpectralPoint (asympPreorder p) where
  toFun := φ.toFun
  map_zero := φ.map_zero
  map_one := φ.map_one
  map_add := φ.map_add
  map_mul := φ.map_mul
  monotone := fun _ _ hab => asymp_implies_spectral p hab φ
  nonneg := φ.nonneg

/-- **Downgrade** (asymptotic-preorder construction): a spectral point for `asympPreorder p` is a
spectral point for `p`. The monotonicity under `p.rel` follows from
`p ≤ asympPreorder p` (`AsympRel.of_le`). -/
noncomputable def downgrade (p : StrassenPreorder S)
    (ψ : AsymptoticSpectrumDuality.SpectralPoint (asympPreorder p)) :
    AsymptoticSpectrumDuality.SpectralPoint p where
  toFun := ψ.toFun
  map_zero := ψ.map_zero
  map_one := ψ.map_one
  map_add := ψ.map_add
  map_mul := ψ.map_mul
  monotone := fun a b hab => ψ.monotone a b (AsympRel.of_le hab)
  nonneg := ψ.nonneg

/-! ## Base-change order embedding. -/

/-- **Base change preserves `relClass`** (Theorem 3.10 easy direction lifted to
classes). The Strassen-preorder relation `relClass = Restricts` on representatives
is preserved by scalar extension, because `KTensor.baseChange_restricts`
(FieldExtension.lean:106) sends a restriction `S ≤ T` over `F` to a restriction
`S_K ≤ T_K` over `K`, and `tensorClassBaseChange ⟦⟨d, T⟩⟧ = ⟦⟨d, T_K⟩⟧`. -/
theorem tensorClassBaseChange_rel_mono (hkF : 2 ≤ k) (hkK : 2 ≤ k) :
    haveI : NeZero k := ⟨by omega⟩
    ∀ a b : TensorClass F k,
    (tensorStrassenPreorder (F := F) hkF).rel a b →
      (tensorStrassenPreorder (F := K) hkK).rel
        (tensorClassBaseChange (K := K) a) (tensorClassBaseChange (K := K) b) := by
  haveI : NeZero k := ⟨by omega⟩
  refine Quotient.ind₂ (motive := fun a b =>
    (tensorStrassenPreorder (F := F) hkF).rel a b →
      (tensorStrassenPreorder (F := K) hkK).rel
        (tensorClassBaseChange (K := K) a) (tensorClassBaseChange (K := K) b)) ?_
  intro a b hab
  -- `rel = relClass`, `relClass (mk a) (mk b) = Restricts a.2 b.2`,
  -- `tensorClassBaseChange (mk a) = mk (TT.baseChange a) = mk ⟨a.1, a.2.baseChange⟩`.
  change Restricts a.2 b.2 at hab
  change Restricts (TT.baseChange (K := K) a).2 (TT.baseChange (K := K) b).2
  exact KTensor.baseChange_restricts (K := K) _ _ hab

/-! ## (P1+P2) the finite-extension scalar-corestriction descent.

We decompose `prop53_finite_descent` (Strassen 1987 Prop 5.3(i),
strassen1987.tex:873-896) into:

* **(P1)** `KTensor.baseChange_factor_tower` / `restricts_descend_to_intermediateField`:
  the finitely many structure constants of a `K`-restriction of base-changed
  `F`-tensors lie in a *finite* subextension `K' = F(constants)`; algebraicity of
  `K/F` makes `[K':F] < ∞`.  This is the cleanest, Mathlib-tractable part
  (`IntermediateField.adjoin`, `IntermediateField.finiteDimensional_adjoin`).
* **(P2)** `finiteExt_restricts_descent`: the irreducible algebraic core — a
  `K'`-restriction of base-changed `F`-tensors descends to `F` at the cost of the
  unit-overhead `⟨q⟩`, `q = [K':F]`.  This is Strassen's scalar-restriction /
  projection-formula chain `f ≤ K'⊗f ≤ K'⊗d ≤ ⟨R(K')⟩⊗d` (tex:878-890,
  display (5.8)), with `q = R(K') ≤ [K':F]`.
* **(P3)** uniformity in `N`: the *same* `K'` and `q` work for every Kronecker
  power, because base change is a ring hom and the preorder is multiplicative
  (`pow_mono`), so the single N=1 `K'`-restriction yields `relClass_{K'}` of all
  powers without re-extracting constants.
-/

/-- Base change `F → K` factors through a finite (or any) intermediate field
`K'` with `[K' : K]`-tower `algebraMap K' K`. For `T : KTensor F d`,
`T.baseChange (K := K) = (T.baseChange (K := K')).baseChange (K := K)` along the
tower `F → K' → K`. -/
theorem KTensor.baseChange_factor_tower {K' : Type u} [Field K'] [Algebra F K']
    [Algebra K' K] [IsScalarTower F K' K] {d : Fin k → ℕ+} (T : KTensor F d) :
    T.baseChange (K := K)
      = (T.baseChange (K := K')).baseChange (K := K) := by
  funext idx
  simp only [KTensor.baseChange]
  exact IsScalarTower.algebraMap_apply F K' K (T idx)

/-- **(P1) Descent of a `K`-restriction to a finitely generated subextension.**

If `Restricts (S.baseChange K) (T.baseChange K)` over `K` (with `S, T` defined over
`F`), the finitely many witness matrix entries lie in `K' = F({entries})`.  Under
`Algebra.IsAlgebraic F K`, `K'` is finite-dimensional over `F`, and the restriction
holds already over `K'`:
`Restricts (S.baseChange K') (T.baseChange K')`.

The construction produces the intermediate field together with the tower instances
and finite-dimensionality, packaged so the descent (P2) can consume them. -/
theorem restricts_descend_to_intermediateField [Algebra.IsAlgebraic F K]
    {dS dT : Fin k → ℕ+} (S : KTensor F dS) (T : KTensor F dT)
    (h : Restricts (S.baseChange (K := K)) (T.baseChange (K := K))) :
    ∃ (K' : IntermediateField F K),
      FiniteDimensional F K' ∧
      Restricts (S.baseChange (K := K')) (T.baseChange (K := K')) := by
  classical
  obtain ⟨A, hA⟩ := h
  -- The finite set of witness entries.
  set ent : Finset K :=
    Finset.univ.biUnion (fun i : Fin k =>
      Finset.univ.biUnion (fun a : Fin (dS i) =>
        Finset.univ.image (fun b : Fin (dT i) => A i a b))) with hent
  -- The subextension generated by the entries.
  refine ⟨IntermediateField.adjoin F (ent : Set K), ?_, ?_⟩
  · -- Finite-dimensional: every generator is integral (algebraic) over `F`.
    refine IntermediateField.finiteDimensional_adjoin ?_
    intro x _
    exact Algebra.IsAlgebraic.isIntegral.isIntegral x
  · -- Each entry `A i a b` lies in `K'`; lift the witness to `K'`-matrices.
    set K' := IntermediateField.adjoin F (ent : Set K)
    have hmem : ∀ (i : Fin k) (a : Fin (dS i)) (b : Fin (dT i)), A i a b ∈ K' := by
      intro i a b
      apply IntermediateField.subset_adjoin
      have hentmem : A i a b ∈ ent := by
        simp only [hent, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨i, a, b, rfl⟩
      exact_mod_cast hentmem
    -- The lifted `K'`-witness.
    refine ⟨fun i a b => ⟨A i a b, hmem i a b⟩, ?_⟩
    intro jdx
    -- Prove the `K'`-restriction equation by injecting into `K` (algebraMap K' K is
    -- injective) and using the `K`-equation `hA`.
    apply (algebraMap K' K).injective
    rw [map_sum]
    -- LHS: algebraMap K' K ((S.baseChange K') jdx) = (S.baseChange K) jdx
    have hSeq : (algebraMap K' K) ((S.baseChange (K := K')) jdx)
        = (S.baseChange (K := K)) jdx := by
      simp only [KTensor.baseChange]
      exact (IsScalarTower.algebraMap_apply F K' K (S jdx)).symm
    rw [hSeq, hA jdx]
    refine Finset.sum_congr rfl ?_
    intro idx _
    rw [map_mul, map_prod]
    have hT : (algebraMap K' K) ((T.baseChange (K := K')) idx)
        = (T.baseChange (K := K)) idx := by
      simp only [KTensor.baseChange]
      exact (IsScalarTower.algebraMap_apply F K' K (T idx)).symm
    rw [hT]
    congr 1

/-- **(I1) Projection / embedding** `T ≤_F ⟨r⟩ ⊠ T` (Strassen 1987 tex:884,
the `f ≤ K' ⊗ f` step of display (5.8), specialised to the trivial
restriction `id`).

`T` embeds into `⟨r⟩ ⊠ T` by selecting the `c = 0` component of the unit:
the witness leg matrix `B_i(a, kdx) = 1` iff `kdx = (0, a)` (encoded via
`kronDecodeEquiv`), else `0`.  Summing, only `kdx_i = (0, a_i)` survives;
all left-components are `0`, hence equal, so `⟨r⟩ = 1` there, and the
right-components are `a`, giving `T a`. -/
theorem Restricts.embed_unitKron {dT : Fin k → ℕ+} (r : ℕ+) (T : KTensor F dT) :
    Restricts T (unitTensor F (k := k) r ⊠ T) := by
  classical
  refine ⟨fun i a kdx =>
    if kronDecodeEquiv kdx = ((0 : Fin (r : ℕ)), a) then (1 : F) else 0, ?_⟩
  intro jdx
  -- The unique surviving multi-index: `kdx₀ i = encode (0, jdx i)`.
  set kdx₀ : (∀ i : Fin k, Fin (((r : ℕ+) * dT i : ℕ+) : ℕ)) :=
    fun i => kronDecodeEquiv.symm ((0 : Fin (r : ℕ)), jdx i) with hkdx₀
  rw [Finset.sum_eq_single kdx₀]
  · -- The surviving term equals `T jdx`.
    have hprod : (∏ i, (if kronDecodeEquiv (kdx₀ i) = ((0 : Fin (r : ℕ)), jdx i)
        then (1 : F) else 0)) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      rw [hkdx₀]
      rw [if_pos (by rw [Equiv.apply_symm_apply])]
    rw [hprod, one_mul, kron_apply]
    -- `unit⟨r⟩` at all-zero left index is `1`; right index is `jdx`.
    have hL : (fun i => kronDecodeL (kdx₀ i))
        = (fun _ : Fin k => (0 : Fin (r : ℕ))) := by
      funext i; rw [hkdx₀]
      change (kronDecodeEquiv (kronDecodeEquiv.symm _)).1 = _
      rw [Equiv.apply_symm_apply]
    have hR : (fun i => kronDecodeR (kdx₀ i)) = jdx := by
      funext i; rw [hkdx₀]
      change (kronDecodeEquiv (kronDecodeEquiv.symm _)).2 = _
      rw [Equiv.apply_symm_apply]
    rw [hL, hR]
    have hunit : (unitTensor F (k := k) r) (fun _ : Fin k => (0 : Fin (r : ℕ))) = 1 := by
      rw [unitTensor, if_pos (fun _ _ => rfl)]
    rw [hunit, one_mul]
  · -- All other multi-indices contribute `0`.
    intro kdx _ hne
    apply mul_eq_zero_of_left
    -- Some leg `i` has `kdx i ≠ (0, jdx i)`, so its factor is `0`.
    by_contra hprod_ne
    apply hne
    -- If the product is nonzero, every factor is `1`, forcing `kdx i = encode (0, jdx i)`.
    funext i
    have hfac : (if kronDecodeEquiv (kdx i) = ((0 : Fin (r : ℕ)), jdx i)
        then (1 : F) else 0) ≠ 0 := by
      intro hzero
      apply hprod_ne
      exact Finset.prod_eq_zero (Finset.mem_univ i) hzero
    have hcond : kronDecodeEquiv (kdx i) = ((0 : Fin (r : ℕ)), jdx i) := by
      by_contra hc; exact hfac (if_neg hc)
    change kdx i = kronDecodeEquiv.symm ((0 : Fin (r : ℕ)), jdx i)
    rw [← hcond, Equiv.symm_apply_apply]
  · intro hne; exact absurd (Finset.mem_univ _) hne

/-! ## (I3-core) The multiplication structure tensor of a finite extension `L/F`
and its tensor-rank upper bound `R(L) ≤ [L:F]²`.

This is the source-grounded algebraic ingredient for the descent link
`K ⊗_F d ≤_F ⟨R(L)⟩ ⊠ d` (Strassen 1987 Prop 5.3(i) proof, tex:885-895, the
"`K ⊗ d ≤ ⟨R(K)⟩ ⊗ d` by Proposition 3.2" step). `R(L)` is the **tensor rank of
`L`'s multiplication bilinear map** (Strassen Lemma 5.2, tex:825). The explicit
Kronecker-decomposition bound gives
`R(L) ≤ q0²`, `q0 = [L:F]` — exactly what makes the existential overhead `q` of
`finiteExt_restricts_descent` well-defined. -/

/-- **Multiplication structure 3-tensor** of `L/F` in the basis `bK = Module.finBasis F L`.

`μ_{a,b,c} = (bK.repr (bK a * bK b)) c`, the structure constants of `L`'s
multiplication: `bK a * bK b = ∑_c μ_{a,b,c} • bK c`
(`Algebra.leftMulMatrix_eq_repr_mul`). This is the 3-tensor whose tensor rank is
Strassen's `R(L)` (tex:825, Lemma 5.2). -/
noncomputable def mulStructureTensor (F : Type u) [Field F] (L : Type u) [Field L]
    [Algebra F L] [FiniteDimensional F L] :
    KTensor F (fun _ : Fin 3 => (⟨Module.finrank F L, Module.finrank_pos⟩ : ℕ+)) :=
  fun idx => (Module.finBasis F L).repr
    ((Module.finBasis F L) (idx 0) * (Module.finBasis F L) (idx 1)) (idx 2)

/-- **`R(L) ≤ [L:F]²`** (Strassen 1987 Lemma 5.2, tex:825, upper-bound half).

The multiplication structure tensor of `L/F` has tensor rank `≤ q0²`,
`q0 = [L:F]`: it is a restriction of the rank-`q0²` diagonal unit tensor
`⟨q0²⟩`.  The explicit rank-`q0²` decomposition is the "obvious" one
`μ = ∑_{(a,b)} e_a* ⊗ e_b* ⊗ (bK a * bK b)`: the diagonal index `ℓ ∈ Fin q0²`
is encoded as the pair `(a,b)` via `finProdFinEquiv`; leg `0` selects coordinate
`a` (`A₀(x,ℓ) = δ_{x,a}`), leg `1` selects `b` (`A₁(y,ℓ) = δ_{y,b}`), and leg `2`
carries the structure constant (`A₂(c,ℓ) = μ_{a,b,c}`).  Summing the diagonal
unit `⟨q0²⟩(ℓ,ℓ,ℓ) = 1` against `∏ A_i` collapses to the single pair `(a,b)` and
reproduces `μ_{a,b,c}`.

This gives Strassen's overhead `q = R(L)` as a finite value (`R(L) ≤ q0² < ∞`),
the fact used by the existential in `finiteExt_restricts_descent`. -/
theorem mulStructureTensor_restricts_unitKron (F : Type u) [Field F] (L : Type u)
    [Field L] [Algebra F L] [FiniteDimensional F L] :
    haveI : NeZero (Module.finrank F L) := ⟨Module.finrank_pos.ne'⟩
    Restricts (mulStructureTensor F L)
      (unitTensor F (k := 3)
        (⟨Module.finrank F L * Module.finrank F L,
          Nat.mul_pos Module.finrank_pos Module.finrank_pos⟩ : ℕ+)) := by
  classical
  haveI : NeZero (Module.finrank F L) := ⟨Module.finrank_pos.ne'⟩
  set q0 := Module.finrank F L with hq0
  set bK := Module.finBasis F L with hbK
  -- Encode the diagonal index `ℓ : Fin (q0*q0)` as a pair `(a,b) : Fin q0 × Fin q0`.
  set e := (finProdFinEquiv : Fin q0 × Fin q0 ≃ Fin (q0 * q0)) with he
  -- Leg witness matrices. `Fin (unitTensor format) i = Fin (q0*q0)` for every leg.
  -- Leg `0` selects the first pair coordinate, leg `1` the second, leg `2` carries
  -- the structure constant.  We encode the per-leg choice with `if i = 0 / 1`.
  refine ⟨fun i (x : Fin q0) (ℓ : Fin (q0 * q0)) =>
    if i = 0 then (if (e.symm ℓ).1 = x then (1 : F) else 0)
    else if i = 1 then (if (e.symm ℓ).2 = x then (1 : F) else 0)
    else bK.repr (bK (e.symm ℓ).1 * bK (e.symm ℓ).2) x, ?_⟩
  intro jdx
  -- The unique surviving diagonal index `ℓ₀ = e (jdx 0, jdx 1)`.
  set ℓ₀ : Fin (q0 * q0) := e (jdx 0, jdx 1) with hℓ₀
  beta_reduce
  refine Eq.symm (Eq.trans (Finset.sum_eq_single (M := F) (fun _ : Fin 3 => ℓ₀) ?_ ?_) ?_)
  · -- All other diagonal multi-indices contribute `0`.
    intro idx _ hne
    -- The unit tensor is `0` unless all legs share a coordinate.
    by_cases hdiag : ∀ i j : Fin 3, idx i = idx j
    · -- Diagonal: all legs equal `v := idx 0`. Since `idx ≠ const ℓ₀`, `v ≠ ℓ₀`,
      -- so `(jdx 0, jdx 1) ≠ e.symm v`, killing one of the leg-0/leg-1 delta factors.
      set v := idx 0 with hv
      have hidx_const : idx = fun _ : Fin 3 => v := by
        funext i; exact (hdiag i 0)
      have hvne : v ≠ ℓ₀ := by
        intro hveq; exact hne (by rw [hidx_const, hveq])
      -- `(jdx 0, jdx 1) ≠ e.symm v`.
      have hpairne : (jdx 0, jdx 1) ≠ e.symm v := by
        intro hpaireq
        apply hvne
        have : e (jdx 0, jdx 1) = v := by rw [hpaireq, Equiv.apply_symm_apply]
        rw [hℓ₀]; exact this.symm
      apply mul_eq_zero_of_left
      rw [Fin.prod_univ_three]
      rw [hidx_const]
      -- Either the leg-0 or leg-1 delta is zero.
      by_cases h0 : (e.symm v).1 = jdx 0
      · -- leg-0 ok ⇒ leg-1 must fail.
        have h1 : ¬ ((e.symm v).2 = jdx 1) := by
          intro h1eq; exact hpairne (Prod.ext h0.symm h1eq.symm)
        norm_num [if_neg h1]
      · norm_num [if_neg h0]
    · rw [unitTensor, if_neg hdiag, mul_zero]
  · -- `const ℓ₀ ∈ univ` always, so this branch is vacuous.
    intro hne; exact absurd (Finset.mem_univ _) hne
  · -- The surviving term reproduces `μ_{jdx 0, jdx 1, jdx 2}`.
    have hsym : e.symm ℓ₀ = (jdx 0, jdx 1) := by rw [hℓ₀, Equiv.symm_apply_apply]
    rw [unitTensor, if_pos (fun _ _ => rfl), mul_one]
    rw [Fin.prod_univ_three]
    simp only [hsym, mulStructureTensor, hbK,
      show ((1 : Fin 3) = 0) = False from by simp, ↓reduceIte,
      show ((2 : Fin 3) = 0) = False from by decide,
      show ((2 : Fin 3) = 1) = False from by decide]
    norm_num

/-- **An F-linear functional on `L` that is nonzero at `1`.** Used as the
"co-restriction" projection `λ : L →ₗ[F] F` in the scalar-restriction descent:
applying `λ` to the `L`-restriction equation extracts the `F`-restriction.

It is `(bL.coord c₀)` for the basis coordinate `c₀ : Fin [L:F]` at which `1 : L`
has nonzero `bL`-component (such `c₀` exists since `1 ≠ 0`), so `λ 1 ≠ 0`. -/
theorem exists_linearMap_one_ne_zero (F : Type u) [Field F] (L : Type u) [Field L]
    [Algebra F L] [FiniteDimensional F L] :
    ∃ lam : L →ₗ[F] F, lam (1 : L) ≠ 0 := by
  classical
  set bL := Module.finBasis F L with hbL
  -- Some coordinate of `1` is nonzero, else `1 = 0`.
  have hex : ∃ c : Fin (Module.finrank F L), bL.repr (1 : L) c ≠ 0 := by
    by_contra h
    push_neg at h
    have h1 : (1 : L) = 0 := by
      have hsr := bL.sum_repr (1 : L)
      rw [← hsr]
      exact Finset.sum_eq_zero fun c _ => by rw [h c, zero_smul]
    exact one_ne_zero h1
  obtain ⟨c₀, hc₀⟩ := hex
  exact ⟨bL.coord c₀, by simpa [Module.Basis.coord_apply] using hc₀⟩

/-- **The iterated-multiplication coupling identity** (the heart of Strassen's
`K ⊗ d ≤ ⟨R(K)⟩ ⊗ d`, Prop 3.2 applied to `L`'s multiplication).

Applying an `F`-linear `lam : L →ₗ[F] F` to a `k`-fold product of `L`-elements,
expanded in the basis `bL = Module.finBasis F L`, gives a sum over `bL`-coordinate
tuples `c : Fin k → Fin [L:F]` of `(∏ᵢ repr(xᵢ)(cᵢ)) · lam(∏ᵢ bL(cᵢ))`. The factor
`lam(∏ᵢ bL(cᵢ))` is the iterated-multiplication structure constant of `L`; it
couples all `k` legs, but the `repr`-factors split per leg — this is exactly the
linearization that makes the per-leg `Restricts` witness well-defined. -/
theorem lam_prod_eq_sum_repr (F : Type u) [Field F] (L : Type u) [Field L]
    [Algebra F L] [FiniteDimensional F L] {k : ℕ} (lam : L →ₗ[F] F) (x : Fin k → L) :
    lam (∏ i, x i) = ∑ c : (Fin k → Fin (Module.finrank F L)),
      (∏ i, (Module.finBasis F L).repr (x i) (c i)) *
        lam (∏ i, (Module.finBasis F L) (c i)) := by
  classical
  set bL := Module.finBasis F L with hbL
  have hprod : ∏ i, x i = ∏ i, ∑ c : Fin (Module.finrank F L), (bL.repr (x i) c) • bL c := by
    exact Finset.prod_congr rfl fun i _ => (bL.sum_repr (x i)).symm
  rw [hprod, Finset.prod_univ_sum, map_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [Finset.prod_smul, map_smul, smul_eq_mul]

/-- Auxiliary form of `finiteExt_restricts_descent` (assembled from
`lam_prod_eq_sum_repr` + the per-leg `Restricts` witness; the overhead
`q = [L:F]^k` is a finite — non-optimal — value, sufficient for the existential). -/
theorem finiteExt_restricts_descent_aux (L : Type u) [Field L] [Algebra F L]
    [FiniteDimensional F L] :
    ∃ q : ℕ+, ∀ {dS dT : Fin k → ℕ+} (S : KTensor F dS) (T : KTensor F dT),
      Restricts (S.baseChange (K := L)) (T.baseChange (K := L)) →
      Restricts S (unitTensor F (k := k) q ⊠ T) := by
  classical
  set q0 := Module.finrank F L with hq0def
  have hq0 : 0 < q0 := Module.finrank_pos
  haveI : NeZero q0 := ⟨hq0.ne'⟩
  haveI : Nonempty (Fin k → Fin q0) := ⟨fun _ => ⟨0, hq0⟩⟩
  set bL := Module.finBasis F L with hbL
  -- Overhead `R = q0^k = #(Fin k → Fin q0)`.
  set R : ℕ := Fintype.card (Fin k → Fin q0) with hRdef
  have hRpos : 0 < R := Fintype.card_pos
  set q : ℕ+ := ⟨R, hRpos⟩ with hqdef
  set eR : Fin R ≃ (Fin k → Fin q0) := (Fintype.equivFin (Fin k → Fin q0)).symm with heR
  obtain ⟨lam, hlam⟩ := exists_linearMap_one_ne_zero F L
  refine ⟨q, ?_⟩
  intro dS dT S T h
  obtain ⟨α, hα⟩ := h
  -- (EQ) Apply the F-linear `lam` to the base-changed `L`-restriction equation.
  -- `hα jdx : algebraMap F L (S jdx) = ∑_idx (∏_i α i (jdx i)(idx i)) · algebraMap F L (T idx)`.
  have hEQ : ∀ jdx : (∀ i, Fin (dS i)),
      S jdx * lam 1 =
        ∑ idx : (∀ i, Fin (dT i)),
          T idx * lam (∏ i, α i (jdx i) (idx i)) := by
    intro jdx
    have hbc := hα jdx
    simp only [KTensor.baseChange] at hbc
    -- Apply `lam` to both sides.
    have happ := congrArg lam hbc
    rw [map_sum] at happ
    -- LHS: lam (algebraMap F L (S jdx)) = S jdx • lam 1 = S jdx * lam 1.
    have hLHS : lam (algebraMap F L (S jdx)) = S jdx * lam 1 := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
    -- Each RHS term: lam ((∏α) * algebraMap F L (T idx)) = T idx * lam (∏α).
    have hRHS : ∀ idx : (∀ i, Fin (dT i)),
        lam ((∏ i, α i (jdx i) (idx i)) * algebraMap F L (T idx))
          = T idx * lam (∏ i, α i (jdx i) (idx i)) := by
      intro idx
      rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, map_smul, smul_eq_mul]
    rw [hLHS] at happ
    rw [happ]
    exact Finset.sum_congr rfl fun idx _ => hRHS idx
  -- Per-leg weight: places the iterated-mult structure constant on leg `0`.
  set W : Fin k → Fin R → F :=
    fun i ℓ => if (i : ℕ) = 0 then (lam 1)⁻¹ * lam (∏ i', bL ((eR ℓ) i')) else 1 with hWdef
  -- `∏_i W i ℓ = (lam 1)⁻¹ * lam (∏_i bL ((eR ℓ) i))`.
  have hWprod : ∀ ℓ : Fin R,
      (∏ i, W i ℓ) = (lam 1)⁻¹ * lam (∏ i', bL ((eR ℓ) i')) := by
    intro ℓ
    rcases Nat.eq_zero_or_pos k with hk0 | hk
    · subst hk0
      simp only [Finset.univ_eq_empty, Finset.prod_empty]
      rw [inv_mul_cancel₀ hlam]
    · -- exactly one `i` (namely `⟨0,hk⟩`) satisfies `(i:ℕ)=0`.
      rw [Finset.prod_eq_single (⟨0, hk⟩ : Fin k)]
      · simp only [hWdef, if_pos rfl]
      · intro b _ hb
        simp only [hWdef]
        rw [if_neg]
        intro hb0
        exact hb (Fin.ext hb0)
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
  -- The `Restricts` witness leg matrices.
  refine ⟨fun i (a : Fin (dS i)) (t : Fin ((q * dT i : ℕ+) : ℕ)) =>
    bL.repr (α i a (kronDecodeR (d₁ := q) (d₂ := dT i) t))
        ((eR (kronDecodeL (d₁ := q) (d₂ := dT i) t)) i)
      * W i (kronDecodeL (d₁ := q) (d₂ := dT i) t), ?_⟩
  intro jdx
  beta_reduce
  -- Reindex the RHS sum `idx : ∀ i, Fin (q * dT i)` as `(ℓvec, jj)` via `kronDecodeEquiv`.
  set E : (∀ i, Fin ((q * dT i : ℕ+) : ℕ)) ≃
      (∀ i, Fin (q : ℕ)) × (∀ i, Fin (dT i)) :=
    (Equiv.piCongrRight (fun _ => kronDecodeEquiv)).trans
      (Equiv.arrowProdEquivProdArrow _ _ _) with hE
  rw [← Equiv.sum_comp E.symm
    (fun idx : ∀ i, Fin ((q * dT i : ℕ+) : ℕ) =>
      (∏ i, (bL.repr (α i (jdx i) (kronDecodeR (idx i))) ((eR (kronDecodeL (idx i))) i)
        * W i (kronDecodeL (idx i)))) * (unitTensor F q ⊠ T) idx)]
  rw [Fintype.sum_prod_type]
  -- Decode facts for `E.symm (ℓvec, jj)`.
  have hdec : ∀ (ℓvec : ∀ i, Fin (q : ℕ)) (jj : ∀ i, Fin (dT i)) (i : Fin k),
      kronDecodeEquiv (E.symm (ℓvec, jj) i) = (ℓvec i, jj i) := by
    intro ℓvec jj i
    have hsymm : E.symm (ℓvec, jj) i = kronDecodeEquiv.symm (ℓvec i, jj i) := by
      simp only [hE, Equiv.symm_trans_apply, Equiv.piCongrRight_symm_apply, Pi.map_apply,
        Equiv.arrowProdEquivProdArrow_symm_apply]
    rw [hsymm, Equiv.apply_symm_apply]
  have hdecL : ∀ (ℓvec : ∀ i, Fin (q : ℕ)) (jj : ∀ i, Fin (dT i)) (i : Fin k),
      kronDecodeL (E.symm (ℓvec, jj) i) = ℓvec i := fun ℓvec jj i => by
    have := hdec ℓvec jj i; rw [kronDecodeEquiv_apply] at this; exact (Prod.ext_iff.1 this).1
  have hdecR : ∀ (ℓvec : ∀ i, Fin (q : ℕ)) (jj : ∀ i, Fin (dT i)) (i : Fin k),
      kronDecodeR (E.symm (ℓvec, jj) i) = jj i := fun ℓvec jj i => by
    have := hdec ℓvec jj i; rw [kronDecodeEquiv_apply] at this; exact (Prod.ext_iff.1 this).2
  -- Simplify each summand: decode the factors, evaluate the Kronecker unit.
  have hsummand : ∀ (x : ∀ i, Fin (q : ℕ)) (y : ∀ i, Fin (dT i)),
      (∏ i, (bL.repr (α i (jdx i) (kronDecodeR (E.symm (x, y) i)))
                (eR (kronDecodeL (E.symm (x, y) i)) i)
            * W i (kronDecodeL (E.symm (x, y) i)))) * (unitTensor F q ⊠ T) (E.symm (x, y))
        = (∏ i, (bL.repr (α i (jdx i) (y i)) (eR (x i) i) * W i (x i)))
            * (unitTensor F q x * T y) := by
    intro x y
    have hprod : (∏ i, (bL.repr (α i (jdx i) (kronDecodeR (E.symm (x, y) i)))
                (eR (kronDecodeL (E.symm (x, y) i)) i)
            * W i (kronDecodeL (E.symm (x, y) i))))
        = (∏ i, (bL.repr (α i (jdx i) (y i)) (eR (x i) i) * W i (x i))) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hdecL x y i, hdecR x y i]
    have hkron : (unitTensor F q ⊠ T) (E.symm (x, y)) = unitTensor F q x * T y := by
      rw [kron_apply]
      congr 1
      · congr 1; funext i; rw [hdecL x y i]
      · congr 1; funext i; rw [hdecR x y i]
    rw [hprod, hkron]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hsummand x y))]
  -- Swap `∑ x ∑ y` → `∑ y ∑ x`, pull out `T y`.
  rw [Finset.sum_comm]
  -- For each `y`, the inner `x`-sum collapses to constant tuples (unit kills the rest),
  -- then reindexes (via `eR`) into `lam (∏ α)` by `lam_prod_eq_sum_repr`.
  have hinner : ∀ y : (∀ i, Fin (dT i)),
      (∑ x : (∀ i, Fin (q : ℕ)),
        (∏ i, (bL.repr (α i (jdx i) (y i)) (eR (x i) i) * W i (x i))) *
          (unitTensor F q x * T y))
        = T y * ((lam 1)⁻¹ * lam (∏ i, α i (jdx i) (y i))) := by
    intro y
    -- Collapse the `x`-sum to constant tuples `x = fun _ => ℓ`.
    have hcollapse :
        (∑ ℓ : Fin (q : ℕ),
              ∏ i, (bL.repr (α i (jdx i) (y i)) (eR ℓ i) * W i ℓ))
          = ∑ x : (∀ i, Fin (q : ℕ)),
          (∏ i, (bL.repr (α i (jdx i) (y i)) (eR (x i) i) * W i (x i))) * unitTensor F q x := by
      refine Finset.sum_of_injOn (e := fun ℓ : Fin (q : ℕ) => (fun _ : Fin k => ℓ)) ?_ ?_ ?_ ?_
      · intro a _ b _ hab
        rcases Nat.eq_zero_or_pos k with hk0 | hk
        · -- `k = 0` ⟹ `q = card (Fin 0 → Fin q0) = 1`, so `Fin q` is a subsingleton.
          subst hk0
          have hq1 : (q : ℕ) = 1 := by
            simp only [hqdef, hRdef]; simp
          haveI : Subsingleton (Fin (q : ℕ)) := by rw [hq1]; infer_instance
          exact Subsingleton.elim a b
        · exact congrFun hab ⟨0, hk⟩
      · intro ℓ _; exact Finset.mem_univ _
      · intro x _ hx
        have hne : ¬ (∀ i j : Fin k, x i = x j) := by
          intro hconst
          apply hx
          rcases Nat.eq_zero_or_pos k with hk0 | hk
          · -- `k = 0`: the empty tuple is `e` applied to (anything, e.g. via Subsingleton).
            refine ⟨(⟨0, q.pos⟩ : Fin (q:ℕ)), by simp, ?_⟩
            subst hk0; funext i; exact i.elim0
          · refine ⟨x ⟨0, hk⟩, by simp, ?_⟩
            funext i; exact (hconst i ⟨0, hk⟩).symm
        have huz : unitTensor F q x = 0 := by simp only [unitTensor]; rw [if_neg hne]
        rw [huz, mul_zero]
      · intro ℓ _
        have hud : unitTensor F q (fun _ : Fin k => ℓ) = 1 := by simp [unitTensor]
        rw [hud, mul_one]
    -- Pull `T y` out and apply `hcollapse`, then reindex by `eR` via `lam_prod_eq_sum_repr`.
    have hpull : (∑ x : (∀ i, Fin (q : ℕ)),
          (∏ i, (bL.repr (α i (jdx i) (y i)) (eR (x i) i) * W i (x i))) *
            (unitTensor F q x * T y))
        = (∑ x : (∀ i, Fin (q : ℕ)),
          (∏ i, (bL.repr (α i (jdx i) (y i)) (eR (x i) i) * W i (x i))) *
            unitTensor F q x) * T y := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hpull, ← hcollapse]
    -- Reduce the `ℓ`-sum: split the `W`-factor, reindex by `eR`, apply `lam_prod_eq_sum_repr`.
    have hℓsum : (∑ ℓ : Fin (q : ℕ),
          ∏ i, (bL.repr (α i (jdx i) (y i)) (eR ℓ i) * W i ℓ))
        = (lam 1)⁻¹ * lam (∏ i, α i (jdx i) (y i)) := by
      have hstep : ∀ ℓ : Fin (q : ℕ),
          (∏ i, (bL.repr (α i (jdx i) (y i)) (eR ℓ i) * W i ℓ))
            = (lam 1)⁻¹ *
              ((∏ i, bL.repr (α i (jdx i) (y i)) (eR ℓ i)) * lam (∏ i', bL ((eR ℓ) i'))) := by
        intro ℓ
        rw [Finset.prod_mul_distrib, hWprod ℓ]
        ring
      rw [Finset.sum_congr rfl fun ℓ _ => hstep ℓ, ← Finset.mul_sum]
      congr 1
      -- Reindex `∑_ℓ` by `eR : Fin (q:ℕ) ≃ (Fin k → Fin q0)`, then `lam_prod_eq_sum_repr`.
      rw [lam_prod_eq_sum_repr F L lam (fun i => α i (jdx i) (y i))]
      rw [← Equiv.sum_comp eR
        (fun c : (Fin k → Fin q0) =>
          (∏ i, (Module.finBasis F L).repr (α i (jdx i) (y i)) (c i)) *
            lam (∏ i', (Module.finBasis F L) (c i')))]
      rfl
    rw [hℓsum]; ring
  rw [Finset.sum_congr rfl fun y _ => hinner y]
  -- Final: `∑ y, T y * ((lam 1)⁻¹ * lam (∏ α)) = S jdx`, from `hEQ` divided by `lam 1`.
  have hfinal : (∑ y : (∀ i, Fin (dT i)), T y * ((lam 1)⁻¹ * lam (∏ i, α i (jdx i) (y i))))
      = (lam 1)⁻¹ * (S jdx * lam 1) := by
    rw [hEQ jdx, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [hfinal]
  field_simp

/-- **(P2) The irreducible algebraic core of Prop 5.3(i)** — scalar corestriction
descent (Strassen 1987 **Proposition 5.3(i)**, strassen_1987.tex:873-896,
proof chain at tex:891-895).

For a **finite** field extension `L / F`, a restriction of base-changed `F`-tensors
over `L` descends to `F` at the cost of a unit-overhead `⟨q⟩` whose size `q : ℕ+`
**depends only on `L`** (not on `S, T`); hence the same `q` serves every Kronecker
power in (P3).  This is the existence statement of Strassen's Prop 5.3(i):

  `∃ q ∀ N, f^{⊗N} ≤ ⟨q⟩ ⊗ d^{⊗N}`  (tex:868, line `(i)`).

Verbatim source proof (tex:885-889): with `f = S`, `d = T` and `K = L`,
`f^{⊗N} ≤ K ⊗ f^{⊗N} ≤ K ⊗ d^{⊗N} ≤ ⟨q⟩ ⊗ d^{⊗N}` **"by (5.8) and Proposition 3.2
with `q = R(K)`"**, where `R(K) = R(L)` is the **tensor rank of `L`'s
multiplication bilinear map** and `K ⊗ (·)` denotes the scalar restriction of the
scalar extension (`(f^K)_H ≅ K ⊗_H f`, tex:789).  The three steps are:

* `f ≤ K ⊗ f` — projection (`f` is a direct summand of `K ⊗ f ≅ ⨁_{[L:F]} f`,
  tex:786 left display, "proofs are obvious").
* `K ⊗ f ≤ K ⊗ d` — display (5.8) (tex:786): scalar restriction applied to the
  hypothesis `f^K ≤ d^K` (= `h`).
* `K ⊗ d ≤ ⟨R(L)⟩ ⊗ d` — Proposition 3.2 (tex:518) applied to `L`'s
  multiplication tensor: `L ≤ ⟨R(L)⟩`, then `⊗ d`.

IMPORTANT (source-faithfulness): the overhead is `⟨R(L)⟩`, **not** `⟨[L:F]⟩`.
In general `R(L) > [L : F]` (e.g. `L = k[T]/(F)` of degree `n` has
`R(L) ≥ ⌈n/2⌉` and `≤ 2n−1`, Lemma 5.2 tex:819); the earlier `⟨finrank F L⟩`
overhead was too small and the statement with it is FALSE.  We therefore
existentially quantify `q`, exactly as Strassen does.

The construction realizes Strassen's chain
`f^{⊗N} ≤ K ⊗ f^{⊗N} ≤ K ⊗ d^{⊗N} ≤ ⟨q⟩ ⊗ d^{⊗N}` directly at the witness level:
apply an `F`-linear functional `lam : L →ₗ[F] F` with `lam 1 ≠ 0`
(`exists_linearMap_one_ne_zero`) to the `L`-restriction equation, expand the
`k`-fold product `lam(∏ᵢ αᵢ)` in the basis `bL = Module.finBasis F L` via
`lam_prod_eq_sum_repr`, and assemble the per-leg `F`-witness
`Bᵢ a t = bL.repr(αᵢ a (decodeR t))((eR (decodeL t)) i) · Wᵢ(decodeL t)`,
where the leg-coupling structure constant `lam(∏ᵢ bL(cᵢ))` is carried on leg `0`.
The overhead is `q = [L:F]^k` (a finite — non-optimal vs `R(L)` — value, sufficient
for the existential).  The cross-leg coupling IS linearized, but by the
`repr`-expansion + the `∑_c ∏ᵢ = ∏ᵢ ∑_{cᵢ}` factorization, NOT by a per-leg
`leftMulMatrix` block.  The lemma `mulStructureTensor_restricts_unitKron`
(`R(L) ≤ [L:F]²`) records the sharper source overhead. -/
theorem finiteExt_restricts_descent (L : Type u) [Field L] [Algebra F L]
    [FiniteDimensional F L] :
    ∃ q : ℕ+, ∀ {dS dT : Fin k → ℕ+} (S : KTensor F dS) (T : KTensor F dT),
      Restricts (S.baseChange (K := L)) (T.baseChange (K := L)) →
      Restricts S (unitTensor F (k := k) q ⊠ T) :=
  finiteExt_restricts_descent_aux L

/-- **(P2, class form)** The finite-extension descent of (P2) lifted to
`TensorClass`.  For a finite field extension `L / F` with base-change ring hom
`jL = tensorClassBaseChange : TensorClass F k →+* TensorClass L k`: there is a
single overhead `q : ℕ+` (depending only on `L`, namely `R(L)`) such that every
class-level restriction over `L` of base-changed classes descends to `F` with
overhead `⟨q⟩`:
`∃ q, ∀ u v, relClass_L (jL u) (jL v) → relClass_F u (⟨q⟩ * v)`.

`q` depends only on `L` (not on `u, v`), so the same `q` serves every power. -/
theorem finiteExt_descent_class (hkF : 2 ≤ k) (L : Type u) [Field L] [Algebra F L]
    [FiniteDimensional F L] :
    haveI : NeZero k := ⟨by omega⟩
    ∃ q : ℕ+, ∀ u v : TensorClass F k,
      (tensorStrassenPreorder (F := L) hkF).rel
          (tensorClassBaseChange (K := L) u) (tensorClassBaseChange (K := L) v) →
      (tensorStrassenPreorder (F := F) hkF).rel
        u (((q : ℕ) : TensorClass F k) * v) := by
  haveI : NeZero k := ⟨by omega⟩
  obtain ⟨q, hq⟩ := finiteExt_restricts_descent (F := F) (k := k) L
  refine ⟨q, ?_⟩
  intro u v h
  induction u using Quotient.ind with | _ a =>
  induction v using Quotient.ind with | _ b =>
  obtain ⟨dS, S⟩ := a
  obtain ⟨dT, T⟩ := b
  change Restricts (S.baseChange (K := L)) (T.baseChange (K := L)) at h
  have hres := hq S T h
  have hrhs : (((q : ℕ) : TensorClass F k) * TensorClass.mk ⟨dT, T⟩)
      = TensorClass.mk ⟨_, unitTensor F (k := k) q ⊠ T⟩ := by
    rw [natCast_eq_unitClass, unitClass, dif_pos q.pos, TensorClass.mk_mul]
    have hqeq : (⟨(q : ℕ), q.pos⟩ : ℕ+) = q := rfl
    rw [hqeq]
  change (tensorStrassenPreorder (F := F) hkF).rel (TensorClass.mk ⟨dS, S⟩)
    (((q : ℕ) : TensorClass F k) * TensorClass.mk ⟨dT, T⟩)
  rw [hrhs]
  change Restricts S (unitTensor F (k := k) q ⊠ T)
  exact hres

/-- **Strassen 1987 Proposition 5.3(i)** (strassen1987.tex:873), finite-extension
scalar-restriction descent, TensorClass form.

For an **algebraic** extension `K/F`: if a base-changed class `i s` restricts into
the base-changed class `i t` over `K` (where `i = tensorClassBaseChange`), then
over the base field `F` the power `s^N` restricts into `⟨q⟩ · t^N` for a single
overhead `q : ℕ+` independent of `N`.

Mathematically this is the *scalar restriction* (a.k.a. corestriction) step: the
finitely many structure constants of the `K`-restriction `i s ≤ i t` lie in a
finite subextension `K' = F(structure constants)` with `[K' : F] = q < ∞` (this
is where algebraicity of `K/F` is used — no Nullstellensatz needed). A `K'`-linear
restriction of `F`-tensors descends to an `F`-linear restriction at the cost of the
dimension-`q` overhead `⟨q⟩`, uniformly in the power `N`.

This is the finite-extension scalar-restriction input for the base-change
order-embedding `tensorClass_hord`; the asymptotic real-analysis packaging is
handled below. -/
theorem prop53_finite_descent [Algebra.IsAlgebraic F K] (hkF : 2 ≤ k) (hkK : 2 ≤ k) :
    haveI : NeZero k := ⟨by omega⟩
    ∀ s t : TensorClass F k,
    (tensorStrassenPreorder (F := K) hkK).rel
        (tensorClassBaseChange (K := K) s) (tensorClassBaseChange (K := K) t) →
    ∃ q : ℕ+, ∀ N : ℕ,
      (tensorStrassenPreorder (F := F) hkF).rel
        (s ^ N) (((q : ℕ) : TensorClass F k) * t ^ N) := by
  haveI : NeZero k := ⟨by omega⟩
  intro s t h
  -- Reduce to representatives.
  induction s using Quotient.ind with | _ a =>
  induction t using Quotient.ind with | _ b =>
  obtain ⟨dS, S⟩ := a
  obtain ⟨dT, T⟩ := b
  -- (P1) Confine the `K`-restriction to a finite subextension `K'`.
  change Restricts (S.baseChange (K := K)) (T.baseChange (K := K)) at h
  obtain ⟨K', hfin, hK'⟩ := restricts_descend_to_intermediateField (K := K) S T h
  haveI : FiniteDimensional F K' := hfin
  -- The single uniform overhead `q = R(K')` (depends only on `K'`, not on `N`),
  -- extracted from the finite-extension descent BEFORE quantifying over `N`.
  obtain ⟨q, hqdesc⟩ := finiteExt_descent_class (F := F) hkK K'
  refine ⟨q, ?_⟩
  intro N
  -- Base-change ring hom `jK' : TensorClass F k →+* TensorClass K' k`.
  set jK' := tensorClassBaseChange (F := F) (K := K') (k := k) with hjK'
  -- (P1 output, class form): `relClass_{K'} (jK' s) (jK' t)`.
  have hbase : (tensorStrassenPreorder (F := K') hkK).rel
      (jK' (TensorClass.mk ⟨dS, S⟩)) (jK' (TensorClass.mk ⟨dT, T⟩)) := by
    change Restricts (S.baseChange (K := K')) (T.baseChange (K := K'))
    exact hK'
  -- (P3) Raise to the `N`-th power over `K'` (multiplicative monotonicity), then
  -- rewrite via `map_pow` to `relClass_{K'} (jK' (s^N)) (jK' (t^N))`.
  have hpow : (tensorStrassenPreorder (F := K') hkK).rel
      (jK' (TensorClass.mk ⟨dS, S⟩) ^ N) (jK' (TensorClass.mk ⟨dT, T⟩) ^ N) :=
    (tensorStrassenPreorder (F := K') hkK).pow_mono N hbase
  have hpowN : (tensorStrassenPreorder (F := K') hkK).rel
      (jK' (TensorClass.mk ⟨dS, S⟩ ^ N)) (jK' (TensorClass.mk ⟨dT, T⟩ ^ N)) := by
    rw [map_pow, map_pow]; exact hpow
  -- (P2, class form): descend the `K'`-power-restriction to `F` with the SAME
  -- uniform overhead `q` (independent of `N`).
  exact hqdesc (TensorClass.mk ⟨dS, S⟩ ^ N) (TensorClass.mk ⟨dT, T⟩ ^ N) hpowN

/-- **Strassen 1988 Theorem 3.10** (strassen1988.tex:1264) / **Strassen 1987
Proposition 5.3(i)** (strassen1987.tex:873): base change
`tensorClassBaseChange : TensorClass F k →+* TensorClass K k` is an
order-embedding for the *asymptotic* preorders, i.e. `a ≲ b` over `F` iff
`a_K ≲ b_K` over `K`.

The **forward** direction (`a ≲ b` over `F` ⟹ `a_K ≲ b_K` over `K`) reuses the same witness
`x : ℕ → ℕ` over `K`, transferring each finite restriction `a^n ≤ b^n · x n`
through `tensorClassBaseChange_rel_mono` (`KTensor.baseChange_restricts`) while
the `sInf` rate condition is reused verbatim.

The **reverse** direction is exactly
"`AsympRel` over `K` of base-changed classes descends to `AsympRel` over `F`",
i.e. the hard direction of **Strassen 1988 Theorem 3.10** (strassen1988.tex:1264)
= **Strassen 1987 Proposition 5.3(i)** (strassen1987.tex:873): a restriction
`S^K ≤ T^K` over the extension `K` yields, over the base field `F`, a quantity
`q` such that `S^{⊗N} ≤ ⟨q⟩ ⊗ T^{⊗N}` for all `N` (finite-extension scalar
restriction; Nullstellensatz-avoidable for algebraic `K`). This finite-extension
descent uses the algebraicity hypothesis `[Algebra.IsAlgebraic F K]` to confine
the structure constants of any restriction
to a *finite* subextension, so no Nullstellensatz is needed. -/
theorem tensorClass_hord [Algebra.IsAlgebraic F K] (hkF : 2 ≤ k) (hkK : 2 ≤ k) :
    haveI : NeZero k := ⟨by omega⟩
    ∀ a b : TensorClass F k,
      (asympPreorder (tensorStrassenPreorder (F := F) hkF)).rel a b ↔
      (asympPreorder (tensorStrassenPreorder (F := K) hkK)).rel
        (tensorClassBaseChange (K := K) a) (tensorClassBaseChange (K := K) b) := by
  haveI : NeZero k := ⟨by omega⟩
  intro a b
  constructor
  · -- FORWARD: same witness `x`, transfer each finite restriction by base change.
    intro hF
    -- `(asympPreorder p).rel = AsympRel p` definitionally.
    change AsympRel (tensorStrassenPreorder (F := F) hkF) a b at hF
    change AsympRel (tensorStrassenPreorder (F := K) hkK)
      (tensorClassBaseChange (K := K) a) (tensorClassBaseChange (K := K) b)
    obtain ⟨x, hxrel, hxinf⟩ := hF
    refine ⟨x, ?_, hxinf⟩
    intro n hn
    have hb := tensorClassBaseChange_rel_mono (F := F) (K := K) hkF hkK _ _ (hxrel n hn)
    -- `tensorClassBaseChange` is a ring hom: `i(a^n) = (i a)^n`,
    -- `i(b^n * x n) = (i b)^n * (x n)`.
    simpa only [map_pow, map_mul, map_natCast] using hb
  · -- REVERSE: an asymptotic restriction over `K` descends to one over `F`.
    intro hK
    classical
    set pF := tensorStrassenPreorder (F := F) hkF with hpF_def
    set pK := tensorStrassenPreorder (F := K) hkK with hpK_def
    set i := tensorClassBaseChange (F := F) (K := K) (k := k) with hi_def
    -- `hK : AsympRel pK (i a) (i b)`. Pass to the Tendsto form for a witness `x`.
    change AsympRel pK (i a) (i b) at hK
    rw [AsympRel_iff_tendsto] at hK
    obtain ⟨x0, hx0rel, hx0tend⟩ := hK
    -- Strengthen the witness so that `x n ≥ 1` everywhere: `x n := x0 n + 1`.
    set x : ℕ → ℕ := fun n => x0 n + 1 with hx_def
    have hx_ge1 : ∀ n, 1 ≤ x n := fun n => by simp only [hx_def]; omega
    have hxtend : Filter.Tendsto (fun n => (x n : ℝ) ^ (1 / (n : ℝ)))
        Filter.atTop (nhds 1) := tendsto_succ_rpow_div_of_tendsto x0 hx0tend
    -- The strengthened relation still holds: `x0 n ≤ x n`, monotonicity absorbs the gap.
    have hxrel : ∀ n, n ≥ 1 → pK.rel (i a ^ n) (i b ^ n * ((x n : ℕ) : TensorClass K k)) := by
      intro n hn
      have h := hx0rel n hn
      have hstep : pK.rel (i b ^ n * ((x0 n : ℕ) : TensorClass K k))
          (i b ^ n * ((x n : ℕ) : TensorClass K k)) := by
        have hnat : pK.rel ((x0 n : ℕ) : TensorClass K k) ((x n : ℕ) : TensorClass K k) :=
          (pK.nat_compat (x0 n) (x n)).mp (by simp only [hx_def]; omega)
        have := pK.mul_mono _ _ (i b ^ n) hnat
        simpa only [mul_comm] using this
      exact pK.trans _ _ _ h hstep
    -- For each `n ≥ 1`, `pK.rel (i (a^n)) (i (b^n * x n))`.
    have hKn : ∀ n, n ≥ 1 → pK.rel (i (a ^ n)) (i (b ^ n * ((x n : ℕ) : TensorClass F k))) := by
      intro n hn
      have h := hxrel n hn
      -- `(i a)^n = i (a^n)`, `(i b)^n * (x n : TC K) = i (b^n * (x n : TC F))`.
      simpa only [map_pow, map_mul, map_natCast] using h
    -- Apply the finite-extension descent at each `n` to the pair `(a^n, b^n * x n)`.
    -- For each `n ≥ 1` we obtain an overhead `q n` valid for all powers `M`.
    have hdesc : ∀ n, n ≥ 1 → ∃ q : ℕ+, ∀ M : ℕ,
        pF.rel ((a ^ n) ^ M)
          (((q : ℕ) : TensorClass F k) * (b ^ n * ((x n : ℕ) : TensorClass F k)) ^ M) := by
      intro n hn
      exact prop53_finite_descent (F := F) (K := K) hkF hkK _ _ (hKn n hn)
    -- The target is `AsympRel pF a b`.
    change AsympRel pF a b
    -- CASE `b = 0`: descent of `i a ≤ i 0` gives `a^N ≤ 0` for all `N ≥ 1`.
    by_cases hb0 : b = 0
    · subst hb0
      -- From `hdesc 1`, `pF.rel (a^M) (q * (0 * x 1)^M)`; for `M ≥ 1` the RHS is `0`.
      obtain ⟨q, hq⟩ := hdesc 1 (le_refl 1)
      refine ⟨fun _ => 1, ?_, ?_⟩
      · intro n hn
        have h := hq n
        simp only [pow_one] at h
        -- `(0 * x 1)^n = 0` for `n ≥ 1`, so RHS `= q * 0 = 0`.
        have hzero : ((0 : TensorClass F k) * ((x 1 : ℕ) : TensorClass F k)) ^ n = 0 := by
          rw [zero_mul, zero_pow (by omega : n ≠ 0)]
        rw [hzero, mul_zero] at h
        simpa only [Nat.cast_one, mul_one, zero_pow (by omega : n ≠ 0)] using h
      · -- `sInf` of the constant-`1` sequence is `1`.
        have himg : (fun n : ℕ => ((1 : ℕ) : ℝ) ^ (1 / (n : ℝ))) '' {n : ℕ | 1 ≤ n} = {1} := by
          ext y
          simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
          constructor
          · rintro ⟨n, _, rfl⟩; simp only [Nat.cast_one, Real.one_rpow]
          · intro hy; exact ⟨1, Nat.le_refl 1, by simp [hy]⟩
        rw [himg]; exact csInf_singleton 1
    -- CASE `b ≠ 0`: build the diagonal subsequence and apply `asympRel_of_subseq`.
    -- Choose, for each `n`, the descent overhead `q n` (default `1` when `n = 0`).
    choose! q hq using hdesc
    -- Crude archimedean bound: `a ≤ r·b`, hence `a^n ≤ b^n · r^n`.
    obtain ⟨r0, hr0⟩ := pF.archimedean a b hb0
    set r : ℕ := max r0 1 with hr_def
    have hr1 : 1 ≤ r := le_max_right _ _
    have hcrude : ∀ n, n ≥ 1 → pF.rel (a ^ n)
        (b ^ n * ((r ^ n : ℕ) : TensorClass F k)) := by
      intro n hn
      -- `a ≤ r·b` from `a ≤ r0·b` and `r0 ≤ r`.
      have harb : pF.rel a (((r : ℕ) : TensorClass F k) * b) := by
        have hr0r : pF.rel (((r0 : ℕ) : TensorClass F k) * b) (((r : ℕ) : TensorClass F k) * b) :=
          pF.mul_mono _ _ b ((pF.nat_compat r0 r).mp (le_max_left _ _))
        exact pF.trans _ _ _ hr0 hr0r
      -- raise to the `n`-th power and rearrange.
      have hpow := pF.pow_mono n harb
      -- `(r·b)^n = b^n * r^n`.
      have heq : (((r : ℕ) : TensorClass F k) * b) ^ n
          = b ^ n * ((r ^ n : ℕ) : TensorClass F k) := by
        push_cast; ring
      rwa [heq] at hpow
    -- Per-`n` diagonal data: exponent `expo n = n · q n`, factor `fac n = q n · x n ^ q n`.
    set expo : ℕ → ℕ := fun n => n * (q n : ℕ) with hexpo_def
    set fac : ℕ → ℕ := fun n => (q n : ℕ) * (x n) ^ (q n : ℕ) with hfac_def
    have hexpo_ge : ∀ n, n ≤ expo n := by
      intro n; simp only [hexpo_def]; exact Nat.le_mul_of_pos_right n (q n).pos
    have hfac1 : ∀ n, 1 ≤ fac n := by
      intro n; simp only [hfac_def]
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (q n).pos.ne' (by
        exact pow_ne_zero _ (Nat.one_le_iff_ne_zero.mp (hx_ge1 n))))
    -- The diagonal relation: `a^{expo n} ≤ b^{expo n} · fac n`.
    have hdiag : ∀ n, n ≥ 1 →
        pF.rel (a ^ expo n) (b ^ expo n * ((fac n : ℕ) : TensorClass F k)) := by
      intro n hn
      have h := hq n hn (q n : ℕ)
      -- `(a^n)^{q n} = a^{n·q n} = a^{expo n}`.
      have hlhs : (a ^ n) ^ (q n : ℕ) = a ^ expo n := by
        rw [← pow_mul]
      -- `↑(q n) * (b^n * x n)^{q n} = b^{expo n} * fac n`.
      have hrhs : ((q n : ℕ) : TensorClass F k)
            * (b ^ n * ((x n : ℕ) : TensorClass F k)) ^ (q n : ℕ)
          = b ^ expo n * ((fac n : ℕ) : TensorClass F k) := by
        simp only [hexpo_def, hfac_def]
        push_cast
        rw [mul_pow, ← pow_mul]
        ring
      rw [hlhs, hrhs] at h
      exact h
    -- The diagonal *rate* `fac n ^ {1/expo n} → 1` as `n → ∞`.
    -- Upper bound: `fac n = q_n x_n^{q_n} ≤ (2 x_n)^{q_n}`, so the rate `≤ 2^{1/n} x_n^{1/n}`.
    have htwo : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ (1 / (n : ℝ)))
        Filter.atTop (nhds 1) := by
      have hinv : Filter.Tendsto (fun n : ℕ => (1 / (n : ℝ))) Filter.atTop (nhds 0) := by
        simp only [one_div]
        exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
      have h0 : (2 : ℝ) ^ (0 : ℝ) = 1 := Real.rpow_zero 2
      have htend0 : Filter.Tendsto (fun y : ℝ => (2 : ℝ) ^ y) (nhds 0) (nhds 1) := by
        rw [← h0]; exact (Real.continuous_const_rpow (by norm_num)).continuousAt.tendsto
      exact htend0.comp hinv
    have hrate_n : Filter.Tendsto (fun n => (fac n : ℝ) ^ (1 / (expo n : ℝ)))
        Filter.atTop (nhds 1) := by
      -- Squeeze between `1` and `2^{1/n} · x_n^{1/n}`.
      have hupper_tend : Filter.Tendsto
          (fun n : ℕ => (2 : ℝ) ^ (1 / (n : ℝ)) * (x n : ℝ) ^ (1 / (n : ℝ)))
          Filter.atTop (nhds 1) := by
        have := htwo.mul hxtend; simpa using this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper_tend ?_ ?_
      · -- eventually `1 ≤ rate`
        filter_upwards [Filter.eventually_ge_atTop 1] with n hn
        have hexpo_pos : (0 : ℝ) < (expo n : ℝ) := by
          have : 1 ≤ expo n := le_trans hn (hexpo_ge n)
          exact_mod_cast this
        calc (1 : ℝ) = 1 ^ (1 / (expo n : ℝ)) := by simp
          _ ≤ (fac n : ℝ) ^ (1 / (expo n : ℝ)) := by
              apply Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hfac1 n)
              exact le_of_lt (div_pos one_pos hexpo_pos)
      · -- eventually `rate ≤ 2^{1/n} · x_n^{1/n}`
        filter_upwards [Filter.eventually_ge_atTop 1] with n hn
        set qn : ℕ := (q n : ℕ) with hqn_def
        have hqn1 : 1 ≤ qn := (q n).pos
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have hqn_pos : (0 : ℝ) < (qn : ℝ) := by exact_mod_cast hqn1
        have hexpo_eq : (expo n : ℝ) = (n : ℝ) * (qn : ℝ) := by
          simp only [hexpo_def, hqn_def]; push_cast; ring
        -- `fac n ≤ (2 * x n)^qn`.
        have hfac_le : (fac n : ℝ) ≤ ((2 * x n : ℕ) : ℝ) ^ qn := by
          have hq2 : qn ≤ 2 ^ qn := le_of_lt (Nat.lt_two_pow_self)
          have : fac n ≤ (2 * x n) ^ qn := by
            simp only [hfac_def, hqn_def, mul_pow]
            exact Nat.mul_le_mul_right _ hq2
          exact_mod_cast this
        -- raise the bound to the `1/expo n` power.
        have hexp_pos : (0 : ℝ) ≤ 1 / (expo n : ℝ) :=
          le_of_lt (div_pos one_pos (by rw [hexpo_eq]; positivity))
        calc (fac n : ℝ) ^ (1 / (expo n : ℝ))
            ≤ (((2 * x n : ℕ) : ℝ) ^ qn) ^ (1 / (expo n : ℝ)) :=
              Real.rpow_le_rpow (by positivity) hfac_le hexp_pos
          _ = ((2 * x n : ℕ) : ℝ) ^ (1 / (n : ℝ)) := by
              rw [← Real.rpow_natCast ((2 * x n : ℕ) : ℝ) qn, ← Real.rpow_mul (by positivity)]
              congr 1
              rw [hexpo_eq]
              field_simp
          _ = (2 : ℝ) ^ (1 / (n : ℝ)) * (x n : ℝ) ^ (1 / (n : ℝ)) := by
              push_cast
              rw [Real.mul_rpow (by norm_num) (by positivity)]
    -- Greedy reindex to a STRICTLY MONOTONE subsequence of exponents.
    -- `g 0 = 1`, `g (j+1) = expo (g j) + 1`; then `expo ∘ g` is strictly increasing.
    set g : ℕ → ℕ := fun j => Nat.rec 1 (fun _ gj => expo gj + 1) j with hg_def
    have hg0 : g 0 = 1 := rfl
    have hg_succ : ∀ j, g (j + 1) = expo (g j) + 1 := fun j => rfl
    have hg_ge1 : ∀ j, 1 ≤ g j := by
      intro j; cases j with
      | zero => simp [hg0]
      | succ j => rw [hg_succ]; omega
    -- `g` is strictly monotone (hence tends to `atTop`).
    have hg_mono : StrictMono g := by
      apply strictMono_nat_of_lt_succ
      intro j
      rw [hg_succ]
      have : g j ≤ expo (g j) := hexpo_ge (g j)
      omega
    have hg_atTop : Filter.Tendsto g Filter.atTop Filter.atTop := hg_mono.tendsto_atTop
    -- `expo ∘ g` is strictly monotone.
    have hm_mono : StrictMono (fun j => expo (g j)) := by
      apply strictMono_nat_of_lt_succ
      intro j
      rw [hg_succ]
      have hge : expo (g j) + 1 ≤ expo (expo (g j) + 1) := hexpo_ge _
      omega
    -- Assemble `AsympRel pF a b` via the cofinal-subsequence packaging.
    refine asympRel_of_subseq (m := fun j => expo (g j)) (c := fun j => fac (g j)) (r := r)
      hm_mono (fun j => le_trans (hg_ge1 j) (hexpo_ge (g j))) hr1
      (fun j => hfac1 (g j)) hcrude (fun j => hdiag (g j) (hg_ge1 j)) ?_
    -- Rate along the subsequence: `fac (g j) ^ {1/expo (g j)} → 1`.
    exact hrate_n.comp hg_atTop

/-! ## (6) the extension theorem. -/

/-- **Theorem 3.10 extension form** (build component 6, strassen1988.tex:1264).

Every concrete spectral point over `F` extends to a concrete spectral point over
a field extension `K`, agreeing on base-changed tensors. The order-embedding input
is `tensorClass_hord`. -/
theorem exists_spectralPoint_extension_bridge (hk : 2 ≤ k) (Fspec : SpectralPoint k F)
    (K : Type u) [Field K] [Algebra F K] [Algebra.IsAlgebraic F K] :
    ∃ Gspec : SpectralPoint k K,
      ∀ {d : Fin k → ℕ+} (T : KTensor F d),
        Gspec.toFun (T.baseChange (K := K)) = Fspec.toFun T := by
  haveI : NeZero k := ⟨by omega⟩
  -- Abstract spectral point over `F`, upgraded to the asymptotic preorder.
  set pF := tensorStrassenPreorder (F := F) hk with hpF
  set pK := tensorStrassenPreorder (F := K) hk with hpK
  set φF : AsymptoticSpectrumDuality.SpectralPoint (asympPreorder pF) :=
    upgrade pF (toAbstractSpectralPoint hk Fspec) with hφF
  -- Apply restriction surjectivity to the base-change ring hom.
  obtain ⟨ψ, hψ⟩ := restriction_surjective (asympPreorder pF) (asympPreorder pK)
    (tensorClassBaseChange (F := F) (K := K) (k := k))
    (tensorClass_hord (F := F) (K := K) hk hk) φF
  -- Downgrade and convert back to a concrete spectral point.
  refine ⟨ofAbstractSpectralPoint hk (downgrade pK ψ), ?_⟩
  intro d T
  change (downgrade pK ψ).toFun (TensorClass.mk ⟨d, T.baseChange (K := K)⟩) = Fspec.toFun T
  -- `⟦⟨d, T_K⟩⟧ = tensorClassBaseChange ⟦⟨d, T⟩⟧`.
  have hbc : (TensorClass.mk ⟨d, T.baseChange (K := K)⟩ : TensorClass K k)
      = tensorClassBaseChange (F := F) (K := K) (TensorClass.mk ⟨d, T⟩) := rfl
  change ψ.toFun (TensorClass.mk ⟨d, T.baseChange (K := K)⟩) = Fspec.toFun T
  rw [hbc, hψ (TensorClass.mk ⟨d, T⟩)]
  -- `φF ⟦⟨d, T⟩⟧ = Fspec.toFun T`.
  change (toAbstractSpectralPoint hk Fspec).toFun (TensorClass.mk ⟨d, T⟩) = Fspec.toFun T
  rfl

end Semicontinuity
