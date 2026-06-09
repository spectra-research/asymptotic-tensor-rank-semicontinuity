/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.Degeneration.Assembly
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.BorderSubrank

/-!
# Substrate bridge: `TensorK.borderSubrankK` ⟶ `Semicontinuity.borderSubrank`

The GHZ degeneration assembly (`AsymptoticSubrank/Degeneration/Assembly.lean`) proves the
headline degeneration bound in the **`TensorK F k fmt`** encoding
(`Prerequisites/TensorK.lean`,
`TensorK R m idx = ((j : Fin m) → idx j) → R`) using
`TensorK.borderSubrankK` (`Prerequisites/BorderSubrankK.lean`), where the legs
`fmt = localIdx inc n` are **arbitrary `Fintype`s** `{e // inc v e} → Fin n`.

The Corollary 3.5 min-cut target (`MaxRankBound.lean:4868`,
`asympSubrank_ge_min_flatRank`) lives in the **`KTensor F d`** encoding
(`MaxRankBound.lean:69`, `KTensor F d = (∀ i, Fin (d i)) → F`), with formats
`d : Fin k → ℕ+`, and the border subrank `Semicontinuity.borderSubrank`
(`AsymptoticSubrank/BorderSubrank.lean:120`) bridges to `asympSubrank` via
`subrank_le_borderSubrank` + `borderSubrank_le_asympSubrank`.

## The relationship (a faithful leg-reindex)

The two `borderSubrank*` definitions are the **same** degeneration notion, modulo a
per-leg `Fintype`-equiv:

* `TensorK.borderSubrankK F k alpha T`
    `= sSup {s | ∃ N (A : ∀ j, Fin s → alpha j → F[X]), vanish<N ∧ coeff N = identityK F k s ρ}`
* `Semicontinuity.borderSubrank T'`  (on `KTensor F d`)
    `= sSup {s | ∃ hs, ∃ N (A : ∀ i, Fin s → Fin (d i) → F[X]),`
    `          vanish<N ∧ coeff N = unitTensor F ⟨s,hs⟩ (..ρ..)}`

The only differences are:

1. the leg type `alpha j` vs `Fin (d j)` — bridged by any equiv `e j : alpha j ≃ Fin (d j)`,
   under which the contraction sum `∑_{g : ∀j, alpha j}` reindexes verbatim to
   `∑_{g' : ∀j, Fin (d j)}` (`Equiv.piCongrRight` + `Fintype.sum_equiv`), the leading
   coefficient identity transports because `identityK F k s = unitTensor F ⟨s,hs⟩` up to
   `Fin.cast` (both `= if (∀ j₁ j₂, ρ j₁ = ρ j₂) then 1 else 0`);
2. the `∃ hs : 0 < s` packaging in `borderSubrank`'s set — for `s = 0` both sets agree
   (`0 ≤ anything`) so the bound is vacuous there; for the witnesses we transport, `s > 0`.

So the bridge is an **honest identification**, not a redefinition.  We build the clean
downstream direction
`TensorK.borderSubrankK k alpha T ≤ Semicontinuity.borderSubrank (reindexKTensor e T)`.

## `ℕ+` / empty-leg handling

`KTensor` formats are `ℕ+`, so each leg cardinality must be `> 0`.  For the GHZ legs
`localIdx inc n v = {e // inc v e} → Fin n` this needs `n ≥ 1` (then `Fin n` is nonempty,
so the function type is nonempty, so `Fintype.card > 0`).  The assembly's headline already
carries `hn : 1 ≤ n`, which we use to package each `d v := ⟨Fintype.card (localIdx inc n v), _⟩`
as a `ℕ+`.  The *general* bridge lemma takes the `ℕ+` format and the per-leg equiv as
explicit hypotheses, sidestepping the positivity packaging; the GHZ specialization supplies
them from `hn`.

## Main results

* `reindexKTensor` — repack a `TensorK F k alpha` (finite legs) as `KTensor F d` along
  equivs `e i : alpha i ≃ Fin (d i)`.
* `borderRestricts_of_TensorK` — a `borderSubrankK`-witness `s` (the raw `∃ N A …` body)
  transports to a `BorderRestricts s hs (reindexKTensor e T)`.
* `borderSubrankK_le_borderSubrank_reindex` — **the bridge**:
  `borderSubrankK k alpha T ≤ borderSubrank (reindexKTensor e T)` (given `BddAbove` of the
  target set).
* `ghzH_asKTensor` — the GHZ tensor repacked to `KTensor F (ghzHFormat …)`.
* `solCount_le_borderSubrank_ghzH` — **the GHZ specialization**:
  `solCount c n g ≤ borderSubrank (ghzH_asKTensor …)`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset BigOperators Polynomial

namespace Semicontinuity

universe u

variable {F : Type u} [Field F] {k : ℕ}

/-! ## Repacking a finite-leg `TensorK` as a `KTensor`. -/

/-- Repack a `k`-tensor `T : TensorK F k alpha` with finite legs into a
    `KTensor F d`, along per-leg equivalences `e i : alpha i ≃ Fin (d i)`.

    `reindexKTensor e T g := T (fun i => (e i).symm (g i))`: read off the
    `KTensor` entry at the multi-index `g : ∀ i, Fin (d i)` by pulling each leg
    coordinate back through `(e i).symm` into the original leg type `alpha i`.
    This is a *relabeling* of the same array — no entry is changed. -/
def reindexKTensor {alpha : Fin k → Type*} {d : Fin k → ℕ+}
    (e : ∀ i, alpha i ≃ Fin (d i)) (T : TensorK F k alpha) : KTensor F d :=
  fun g => T (fun i => (e i).symm (g i))

/-! ## The leading-coefficient identity transports. -/

/-- `identityK F k s ρ = unitTensor F ⟨s,hs⟩ (fun i => Fin.cast h (ρ i))`:
    both are the diagonal indicator `if (∀ leg-pair agrees) then 1 else 0`, so the
    `TensorK` identity tensor and the `KTensor` unit tensor coincide under the
    canonical `Fin s ≃ Fin ((⟨s,hs⟩ : ℕ+) : ℕ)` recast.  This is the leg-`ρ`
    diagonal value that both `borderSubrankK` and `BorderRestricts` realize at
    degree `N`. -/
theorem identityK_eq_unitTensor {s : ℕ} (hs : 0 < s) (ρ : Fin k → Fin s) :
    TensorK.identityK F k s ρ
      = unitTensor F (k := k) ⟨s, hs⟩
          (fun i => (Fin.cast (by rfl) (ρ i) : Fin ((⟨s, hs⟩ : ℕ+) : ℕ))) := by
  -- `Fin.cast (rfl)` is the identity, so the two diagonal conditions are defeq:
  -- `congr 1` reduces both `if`-indicators to the same predicate.
  unfold TensorK.identityK unitTensor
  congr 1

/-! ## The contraction sum reindexes verbatim. -/

/-- Under the per-leg equivs `e`, the `KTensor` contraction of `reindexKTensor e T`
    against a polynomial family `A` equals the original `TensorK` contraction of `T`
    against the relabeled family `A i a ∘ (e i).symm` — *as polynomials*, hence with
    matching coefficients at every degree. The reindex is `Equiv.piCongrRight e`. -/
theorem reindex_contraction_eq {alpha : Fin k → Type*}
    [∀ i, Fintype (alpha i)] {d : Fin k → ℕ+}
    (e : ∀ i, alpha i ≃ Fin (d i)) (T : TensorK F k alpha) {s : ℕ}
    (A : ∀ i : Fin k, Fin s → alpha i → Polynomial F) (ρ : Fin k → Fin s) :
    (∑ g : ∀ i : Fin k, Fin (d i),
        (∏ i, (fun (a : Fin s) (b : Fin (d i)) => A i a ((e i).symm b)) (ρ i) (g i))
          * Polynomial.C (reindexKTensor e T g))
      = ∑ f : ∀ i : Fin k, alpha i,
          (∏ i, A i (ρ i) (f i)) * Polynomial.C (T f) := by
  classical
  rw [← Equiv.sum_comp (Equiv.piCongrRight e)]
  apply Finset.sum_congr rfl
  intro f _
  simp only [Equiv.piCongrRight_apply, reindexKTensor, Pi.map_apply,
    Equiv.symm_apply_apply]

/-! ## A `borderSubrankK`-witness transports to a `BorderRestricts`. -/

/-- A raw `borderSubrankK`-membership witness for `s > 0` (a degree-`N` polynomial
    family in the `TensorK` encoding) transports to a `BorderRestricts s hs
    (reindexKTensor e T)` in the `KTensor` encoding.  The transported family is
    `A' i a b := A i a ((e i).symm b)`; the vanishing and the leading-coefficient
    identity carry over by `reindex_contraction_eq` and `identityK_eq_unitTensor`. -/
theorem borderRestricts_of_TensorK {alpha : Fin k → Type*}
    [∀ i, Fintype (alpha i)] [∀ i, DecidableEq (alpha i)] {d : Fin k → ℕ+}
    (e : ∀ i, alpha i ≃ Fin (d i)) (T : TensorK F k alpha)
    {s : ℕ} (hs : 0 < s) {N : ℕ}
    (A : ∀ i : Fin k, Fin s → alpha i → Polynomial F)
    (hvanish : ∀ ρ : Fin k → Fin s, ∀ l : ℕ, l < N →
      (∑ f : ∀ i : Fin k, alpha i,
        (∏ i, A i (ρ i) (f i)) * Polynomial.C (T f)).coeff l = 0)
    (hident : ∀ ρ : Fin k → Fin s,
      (∑ f : ∀ i : Fin k, alpha i,
        (∏ i, A i (ρ i) (f i)) * Polynomial.C (T f)).coeff N
        = TensorK.identityK F k s ρ) :
    BorderRestricts (F := F) s hs (reindexKTensor e T) := by
  classical
  refine ⟨N, (fun i a b => A i a ((e i).symm b)), ?_, ?_⟩
  · intro ρ l hl
    rw [reindex_contraction_eq e T A ρ]
    exact hvanish ρ l hl
  · intro ρ
    rw [reindex_contraction_eq e T A ρ, hident ρ, identityK_eq_unitTensor hs ρ]

/-! ## The bridge at the `sSup` level. -/

/-- **Substrate bridge** `borderSubrankK ⟶ borderSubrank`.  Given finite legs
    `alpha`, formats `d : Fin k → ℕ+`, and per-leg equivs `e i : alpha i ≃ Fin (d i)`,
    the `TensorK` border subrank is dominated by the `KTensor` border subrank of the
    repacked tensor:

      `TensorK.borderSubrankK F k alpha T ≤ Semicontinuity.borderSubrank (reindexKTensor e T)`.

    Every `s` in the `borderSubrankK` `sSup`-set with `s > 0` transports (via
    `borderRestricts_of_TensorK`) to the `borderSubrank` set; the `s = 0` case is
    `0 ≤ _`.  Requires `BddAbove` of the target set (supplied downstream exactly as
    `subrank_le_borderSubrank` / the Assembly headline require it). -/
theorem borderSubrankK_le_borderSubrank_reindex {alpha : Fin k → Type*}
    [∀ i, Fintype (alpha i)] [∀ i, DecidableEq (alpha i)] {d : Fin k → ℕ+}
    (e : ∀ i, alpha i ≃ Fin (d i)) (T : TensorK F k alpha)
    (hbdd : BddAbove
      { s : ℕ | ∃ hs : 0 < s, BorderRestricts (F := F) s hs (reindexKTensor e T) }) :
    TensorK.borderSubrankK (F := F) k alpha T
      ≤ borderSubrank (reindexKTensor e T) := by
  classical
  -- `borderSubrankK = sSup S₁`.  Bound each `s ∈ S₁` by `borderSubrank`:
  --   `s = 0` ⟹ `0 ≤ _`;  `s > 0` ⟹ `s ∈ S₂` (target set), so `s ≤ sSup S₂` by `le_csSup`.
  -- This avoids the false "literal subset" claim (`0` can be in `S₁` but never in `S₂`),
  -- keeping the bridge an honest `≤` rather than a set inclusion.  When `S₁` is empty,
  -- `sSup ∅ = 0` over `ℕ`, again `≤ _`.
  unfold TensorK.borderSubrankK
  rcases Set.eq_empty_or_nonempty
      { s : ℕ | ∃ (N : ℕ) (A : (j : Fin k) → Fin s → alpha j → Polynomial F),
          (∀ (ρ : Fin k → Fin s), ∀ n : ℕ, n < N →
            (∑ g : (j : Fin k) → alpha j,
              (∏ j : Fin k, A j (ρ j) (g j)) * Polynomial.C (T g)).coeff n = 0) ∧
          (∀ (ρ : Fin k → Fin s),
            (∑ g : (j : Fin k) → alpha j,
              (∏ j : Fin k, A j (ρ j) (g j)) * Polynomial.C (T g)).coeff N
            = TensorK.identityK F k s ρ)} with hempty | hne
  · rw [hempty]; simp
  · refine csSup_le hne ?_
    rintro s ⟨N, A, hvanish, hident⟩
    rcases Nat.eq_zero_or_pos s with hs0 | hs
    · subst hs0; exact Nat.zero_le _
    · exact le_csSup hbdd ⟨hs, borderRestricts_of_TensorK e T hs A hvanish hident⟩

/-! ## GHZ specialization: `solCount ≤ borderSubrank (ghzH_asKTensor …)`. -/

open VC.Degeneration in
/-- The `KTensor` format for the repacked `GHZ^H_n`: leg `v` has dimension
    `Fintype.card (localIdx inc n v)`, a `ℕ+` because for `n ≥ 1` the local index
    space `{e // inc v e} → Fin n` is nonempty (`Fin n` inhabited). -/
noncomputable def ghzHFormat {E : Type*} [Fintype E] [DecidableEq E] {k : ℕ}
    (inc : Fin k → E → Prop) [∀ v e, Decidable (inc v e)] {n : ℕ} (hn : 1 ≤ n) :
    Fin k → ℕ+ :=
  fun v => ⟨Fintype.card (localIdx inc n v),
    by haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩; exact Fintype.card_pos⟩

open VC.Degeneration in
/-- The per-leg `Fintype`-equiv `localIdx inc n v ≃ Fin (ghzHFormat … v)`, i.e.
    `Fintype.equivFin`, used to repack `ghzHTensor` into a `KTensor`. -/
noncomputable def ghzHEquiv {E : Type*} [Fintype E] [DecidableEq E] {k : ℕ}
    (inc : Fin k → E → Prop) [∀ v e, Decidable (inc v e)] {n : ℕ} (hn : 1 ≤ n) :
    ∀ v : Fin k, localIdx inc n v ≃ Fin ((ghzHFormat inc hn v : ℕ+) : ℕ) :=
  fun v => Fintype.equivFin (localIdx inc n v)

open VC.Degeneration in
/-- **`GHZ^H_n` repacked as a `KTensor`** (`ghzH_asKTensor inc hn`).  This is the
    `KTensor F (ghzHFormat inc hn)` relabeling of the `TensorK`-encoded
    `ghzHTensor inc n` along the canonical per-leg `Fintype`-equiv `ghzHEquiv`.
    Same diagonal-consistency array, now on `Fin (d v)` legs with `d : Fin k → ℕ+`,
    so it lives in the `MaxRankBound` substrate where `asympSubrank` and the
    Cor 3.5 min-cut target (`MaxRankBound.lean:4868`) are stated. -/
noncomputable def ghzH_asKTensor {E : Type*} [Fintype E] [DecidableEq E] {k : ℕ}
    (inc : Fin k → E → Prop) [∀ v e, Decidable (inc v e)] {n : ℕ} (hn : 1 ≤ n) :
    KTensor F (ghzHFormat inc hn) :=
  reindexKTensor (ghzHEquiv inc hn) (ghzHTensor (F := F) inc n)

open VC.Degeneration in
/-- **GHZ substrate bridge** (`solCount ≤ borderSubrank (ghzH_asKTensor …)`).
    Transports the Assembly headline `borderSubrankK_ghzH_ge_solCount`
    (`Assembly.lean:311`, in the `TensorK`/`borderSubrankK` encoding) across the
    leg-reindex into the `KTensor`/`borderSubrank` substrate of `MaxRankBound`.

    Composed with `subrank_le_borderSubrank` + `borderSubrank_le_asympSubrank`
    (`BorderSubrank.lean`), this delivers the
    `asympSubrank (ghzH_asKTensor …) ≥ solCount` lower bound feeding Cor 3.5.

    `hbddT` / `hbddK` are the two `BddAbove` side-conditions (the source headline
    already takes `hbddT`; `hbddK` is the `KTensor`-side analogue, both supplied
    from the flattening witness as in `FieldInvariance.subrank_set_bddAbove`). -/
theorem solCount_le_borderSubrank_ghzH {E : Type*} [Fintype E] [DecidableEq E]
    {k D : ℕ} (inc : Fin k → E → Prop) [∀ v e, Decidable (inc v e)]
    (c : E → Fin D → ℤ)
    (horth : ∀ e f : E, ¬ edgesIncident inc e f → idot (c e) (c f) = 0)
    (edgeOwner : E → Fin k) (pairOwner : E → E → Fin k) (gVertex : Fin k)
    (hEdgeInc : ∀ e, inc (edgeOwner e) e)
    (hPairInc : ∀ e f, e ≠ f → idot (c e) (c f) ≠ 0 →
      inc (pairOwner e f) e ∧ inc (pairOwner e f) f)
    {n : ℕ} (hn : 1 ≤ n) (hk : 0 < k) (g : Fin D → ℤ)
    (hgp : GeneralPositionInjective (k := k) inc c n g)
    (hbddT : BddAbove {s : ℕ | ∃ (N : ℕ)
      (A : (v : Fin k) → Fin s → localIdx inc n v → Polynomial F),
      (∀ ρ : Fin k → Fin s, ∀ l : ℕ, l < N →
        (∑ f : (v : Fin k) → localIdx inc n v,
          (∏ v, A v (ρ v) (f v)) *
            Polynomial.C (ghzHTensor (F := F) inc n f)).coeff l = 0) ∧
      (∀ ρ : Fin k → Fin s,
        (∑ f : (v : Fin k) → localIdx inc n v,
          (∏ v, A v (ρ v) (f v)) *
            Polynomial.C (ghzHTensor (F := F) inc n f)).coeff N =
        TensorK.identityK F k s ρ)})
    (hbddK : BddAbove
      { s : ℕ | ∃ hs : 0 < s,
        BorderRestricts (F := F) s hs (ghzH_asKTensor inc hn) }) :
    solCount c n g ≤ borderSubrank (ghzH_asKTensor (F := F) inc hn) := by
  -- Source headline in the `TensorK` encoding.
  have hsrc : solCount c n g ≤
      TensorK.borderSubrankK (F := F) k (localIdx inc n) (ghzHTensor (F := F) inc n) :=
    borderSubrankK_ghzH_ge_solCount (F := F) inc c horth edgeOwner pairOwner gVertex
      hEdgeInc hPairInc n hn hk g hgp hbddT
  -- Bridge across the leg-reindex.
  refine le_trans hsrc ?_
  exact borderSubrankK_le_borderSubrank_reindex
    (ghzHEquiv inc hn) (ghzHTensor (F := F) inc n) hbddK

end Semicontinuity
