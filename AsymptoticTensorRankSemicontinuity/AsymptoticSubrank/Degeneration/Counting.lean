/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Solution-counting (pigeonhole) lemma for the Corollary 3.5 degeneration

This file formalizes the averaging/pigeonhole step of the Vrana–Christandl degeneration
(arXiv:1603.03964, `genmamu.tex` lines 169-189): after fixing the orthogonal-representation
coefficients `c : E → ℤ^D`, the right-hand side `g` of the linear system `∑_e c_e i_e = g`
can be chosen so that the system has **many** solutions `i : E → [0,n)`.

## Source (genmamu:169-181)

The argument (Vrana–Christandl) averages over a target `g` drawn from a cube of
side `≈ 2Cn`, where `C` bounds the `1`-norms of the `c_e`: the expected number of
solutions is `(2C)^{-d} n^{l-d}`, so some `g` admits at least
`M := ⌈(2C)^{-d} n^{l-d}⌉` solutions of `∑_e c_e i_e = g`.

The probabilistic phrasing is the standard "max ≥ average" pigeonhole: every index tuple `i`
contributes its image `∑_e c_e i_e` to **exactly one** point `g` of the cube (because that image
lands in the cube — the load-bearing containment, verified in `linImg_mem_cube`). Hence

  `∑_{g ∈ cube} solCount c n g = #(E → Fin n) = n^l`,

and since the cube has `(2Cn)^D` points, some `g` has `solCount ≥ n^l / (2Cn)^D`, stated
division-free as `(2*C*n)^D * solCount c n g ≥ n^l`.

## Main definitions

* `solCount c n g` — the number of `i : E → Fin n` solving `∀ r, ∑_e c_e r · i_e = g_r`.
* `cubeBound c` — the explicit `C := 1 + ∑_e ∑_r |c_e r|` (a `1`-norm bound, `≥ 1`).

## Main results

* `linImg_mem_cube` — the image `r ↦ ∑_e c_e r · i_e` lands in `[-Cn, Cn-1]^D` (the containment
  driving the fiberwise count; genmamu:169).
* `sum_solCount_cube` — `∑_{g ∈ cube} solCount c n g = n^l` (fiberwise count; genmamu:171-179).
* `exists_g_solCount_ge` — **the headline** (genmamu:181): `∃ g, (2Cn)^D · solCount c n g ≥ n^l`.

## Method

The cycle-specific development counts solutions via a closed-form
parametrization (`countM`, `card_solSet_eq_countM`); here we do the **abstract**
averaging/pigeonhole over an arbitrary `c`, so the count is a `card_eq_sum_card_fiberwise`
reindexing plus `exists_le_of_sum_le`, not a bijection.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset BigOperators

namespace VC.Degeneration

variable {E : Type*} [Fintype E] [DecidableEq E] {D : ℕ}

/-! ### The solution count -/

/-- **The solution count** `solCount c n g` (genmamu:170-171): the number of index tuples
    `i : E → Fin n` (so `i_e ∈ [0,n)`) solving the linear system `∀ r, ∑_e c_e r · i_e = g_r`. -/
def solCount (c : E → Fin D → ℤ) (n : ℕ) (g : Fin D → ℤ) : ℕ :=
  (Finset.univ.filter
    (fun i : E → Fin n => ∀ r, ∑ e, (c e r) * (i e : ℤ) = g r)).card

/-! ### The cube bound `C` (genmamu:169) -/

/-- **The cube bound `C`** (genmamu:169, "the maximum of `1`-norms of the vectors `{c_e}`").

    We take the slightly coarser but explicit `C := 1 + ∑_e ∑_r |c_e r|`, which dominates each
    coordinate's column `1`-norm `∑_e |c_e r|` (and is `≥ 1`), so that the linear image lands in
    `[-Cn, Cn-1]^D` (`linImg_mem_cube`). -/
def cubeBound (c : E → Fin D → ℤ) : ℕ :=
  1 + (∑ e, ∑ r, (c e r).natAbs)

/-- `cubeBound ≥ 1`. -/
lemma one_le_cubeBound (c : E → Fin D → ℤ) : 1 ≤ cubeBound c := Nat.le_add_right 1 _

/-- The column `1`-norm in coordinate `r` is strictly below `C`: `∑_e |c_e r| < C`. -/
lemma colNorm_lt_cubeBound (c : E → Fin D → ℤ) (r : Fin D) :
    (∑ e, |c e r|) < (cubeBound c : ℤ) := by
  have hcol : (∑ e, |c e r|) = ((∑ e, (c e r).natAbs : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [Int.abs_eq_natAbs]
  have hmono : (∑ e, (c e r).natAbs) ≤ ∑ e, ∑ r, (c e r).natAbs := by
    apply Finset.sum_le_sum
    intro e _
    exact Finset.single_le_sum (f := fun r => (c e r).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
  rw [hcol]
  have : (∑ e, (c e r).natAbs) < cubeBound c := by
    unfold cubeBound; omega
  exact_mod_cast this

/-! ### The cube and the load-bearing containment (genmamu:169) -/

/-- The `r`-th edge of the cube `[-Cn, Cn-1]` in `ℤ`. -/
private def cubeIcc (C n : ℕ) : Finset ℤ := Finset.Icc (-((C * n : ℕ) : ℤ)) (((C * n : ℕ) : ℤ) - 1)

/-- **The cube** `[-Cn, Cn-1]^D ∩ ℤ^D` (genmamu:169), as a `Finset (Fin D → ℤ)`. -/
def cube (C n : ℕ) : Finset (Fin D → ℤ) :=
  Fintype.piFinset (fun _ : Fin D => cubeIcc C n)

/-- Each edge `[-Cn, Cn-1]` of the cube has `2Cn` integer points. -/
private lemma card_cubeIcc (C n : ℕ) : (cubeIcc C n).card = 2 * C * n := by
  unfold cubeIcc
  rw [Int.card_Icc]
  have : (((C * n : ℕ) : ℤ) - 1) + 1 - (-((C * n : ℕ) : ℤ)) = ((2 * C * n : ℕ) : ℤ) := by
    push_cast; ring
  rw [this, Int.toNat_natCast]

/-- **The cube has `(2Cn)^D` points** (genmamu:169). -/
theorem card_cube (C n : ℕ) : (cube C n : Finset (Fin D → ℤ)).card = (2 * C * n) ^ D := by
  unfold cube
  rw [Fintype.card_piFinset]
  simp only [card_cubeIcc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The load-bearing containment** (genmamu:169): for any index tuple `i : E → Fin n`, the
    linear image `r ↦ ∑_e c_e r · i_e` lands in the cube `[-Cn, Cn-1]^D`.

    Proof of the coordinate bound: `|∑_e c_e r i_e| ≤ (∑_e |c_e r|)·(n-1) ≤ (C-1)·(n-1) ≤ Cn-1`. -/
theorem linImg_mem_cube (c : E → Fin D → ℤ) (n : ℕ) (hn : 1 ≤ n) (i : E → Fin n) :
    (fun r => ∑ e, (c e r) * (i e : ℤ)) ∈ cube (cubeBound c) n := by
  rw [cube, Fintype.mem_piFinset]
  intro r
  rw [cubeIcc, Finset.mem_Icc]
  set C := cubeBound c with hCdef
  -- Coordinate bound: |∑_e c_e r i_e| ≤ (∑_e |c_e r|) * (n-1).
  have hbound : |∑ e, (c e r) * (i e : ℤ)| ≤ (∑ e, |c e r|) * ((n : ℤ) - 1) := by
    calc |∑ e, (c e r) * (i e : ℤ)|
        ≤ ∑ e, |(c e r) * (i e : ℤ)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ e, |c e r| * |(i e : ℤ)| := by
            apply Finset.sum_congr rfl; intro e _; rw [abs_mul]
      _ ≤ ∑ e, |c e r| * ((n : ℤ) - 1) := by
            apply Finset.sum_le_sum
            intro e _
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            have hie : (i e : ℤ) ≤ (n : ℤ) - 1 := by
              have := (i e).isLt; have : ((i e : ℕ) : ℤ) ≤ (n : ℤ) - 1 := by
                exact_mod_cast Nat.le_sub_one_of_lt (i e).isLt
              simpa using this
            have hie0 : (0 : ℤ) ≤ (i e : ℤ) := by positivity
            rw [abs_of_nonneg hie0]; exact hie
      _ = (∑ e, |c e r|) * ((n : ℤ) - 1) := by rw [Finset.sum_mul]
  -- (∑_e |c_e r|) < C  and  n ≥ 1  give  (∑_e |c_e r|)*(n-1) ≤ (C-1)*(n-1) ≤ Cn-1.
  have hcol : (∑ e, |c e r|) < (C : ℤ) := colNorm_lt_cubeBound c r
  have hcol0 : (0 : ℤ) ≤ ∑ e, |c e r| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hC1 : (1 : ℤ) ≤ (C : ℤ) := by exact_mod_cast one_le_cubeBound c
  have hn1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hfinal : |∑ e, (c e r) * (i e : ℤ)| ≤ ((C : ℕ) * n : ℕ) - 1 := by
    have hCn : ((C * n : ℕ) : ℤ) = (C : ℤ) * (n : ℤ) := by push_cast; ring
    have hle : (∑ e, |c e r|) * ((n : ℤ) - 1) ≤ (C : ℤ) * (n : ℤ) - 1 := by
      nlinarith [hbound, hcol, hcol0, hC1, hn1]
    have : |∑ e, (c e r) * (i e : ℤ)| ≤ (C : ℤ) * (n : ℤ) - 1 := le_trans hbound hle
    rw [show (((C : ℕ) * n : ℕ) : ℤ) - 1 = (C : ℤ) * (n : ℤ) - 1 from by rw [hCn]]
    exact this
  rw [abs_le] at hfinal
  exact ⟨by linarith [hfinal.1], by linarith [hfinal.2]⟩

/-! ### The fiberwise count (genmamu:171-179) -/

/-- The fiber of `g` under `i ↦ (r ↦ ∑_e c_e r i_e)` is exactly the solution set of `g`,
    so its card is `solCount c n g`. -/
private lemma card_fiber_eq_solCount (c : E → Fin D → ℤ) (n : ℕ) (g : Fin D → ℤ) :
    {i ∈ (Finset.univ : Finset (E → Fin n)) |
        (fun r => ∑ e, (c e r) * (i e : ℤ)) = g}.card = solCount c n g := by
  unfold solCount
  congr 1
  apply Finset.filter_congr
  intro i _
  constructor
  · intro h r; exact congrFun h r
  · intro h; funext r; exact h r

/-- **The total count is `n^l`** (genmamu:171-179): summing `solCount c n g` over the cube gives
    the total number of index tuples `n^l`, because each tuple lands in exactly one cube point
    (`linImg_mem_cube`). This is the `E[N]` bookkeeping done as an exact fiberwise sum. -/
theorem sum_solCount_cube (c : E → Fin D → ℤ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ g ∈ cube (cubeBound c) n, solCount c n g = n ^ (Fintype.card E) := by
  classical
  have hmaps : Set.MapsTo (fun i : E → Fin n => (fun r => ∑ e, (c e r) * (i e : ℤ)))
      ↑(Finset.univ : Finset (E → Fin n))
      (↑(cube (D := D) (cubeBound c) n) : Set (Fin D → ℤ)) := by
    intro i _; exact linImg_mem_cube c n hn i
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  -- LHS card of univ = n^l, RHS = ∑_g (fiber card) = ∑_g solCount.
  rw [Finset.card_univ, Fintype.card_pi] at hcard
  simp only [Fintype.card_fin, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcard
  rw [hcard]
  apply Finset.sum_congr rfl
  intro g _
  exact (card_fiber_eq_solCount c n g).symm

/-! ### The pigeonhole conclusion (genmamu:181) -/

/-- **Headline pigeonhole lemma** (genmamu:181, `\GHZ` degeneration solution count).

    After fixing the orthogonal-representation coefficients `c`, there exists a right-hand side
    `g` such that the linear system `∑_e c_e i_e = g` has at least `n^l / (2Cn)^D` solutions,
    stated division-free as `(2Cn)^D · solCount c n g ≥ n^l`, where `C = cubeBound c` is the
    `1`-norm bound and `l = |E|`. This is the count `M := ⌈(2C)^{-D} n^{l-D}⌉` driving the
    degeneration (the `GHZ` state has this many terms). -/
theorem exists_g_solCount_ge (c : E → Fin D → ℤ) (n : ℕ) (hn : 1 ≤ n) :
    ∃ g : Fin D → ℤ,
      (2 * cubeBound c * n) ^ D * solCount c n g ≥ n ^ (Fintype.card E) := by
  classical
  set C := cubeBound c with hCdef
  -- Nonempty cube (so `exists_le_of_sum_le` applies): `[-Cn, Cn-1]` is nonempty since C,n ≥ 1.
  have hCpos : 1 ≤ C := one_le_cubeBound c
  have hcube_ne : (cube C n : Finset (Fin D → ℤ)).Nonempty := by
    rw [cube, Fintype.piFinset_nonempty]
    intro r
    refine ⟨-((C * n : ℕ) : ℤ), ?_⟩
    rw [cubeIcc, Finset.mem_Icc]
    refine ⟨le_refl _, ?_⟩
    have h1 : 1 ≤ C * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have h1' : (1 : ℤ) ≤ ((C * n : ℕ) : ℤ) := by exact_mod_cast h1
    linarith
  -- Averaging: ∑_g (n^l) ≤ ∑_g ((2Cn)^D · solCount g), since the totals are equal.
  -- ∑_g solCount = n^l  and  #cube = (2Cn)^D, so ∑_g (cube.card · solCount) = cube.card · n^l.
  have hsum : ∑ g ∈ cube C n, solCount c n g = n ^ (Fintype.card E) :=
    sum_solCount_cube c n hn
  set Ncard := (2 * C * n) ^ D with hN
  have hcardcube : (cube C n : Finset (Fin D → ℤ)).card = Ncard := card_cube C n
  -- We want: ∃ g ∈ cube, n^l ≤ Ncard * solCount g.  Use exists_le_of_sum_le with f = const n^l,
  -- g = Ncard * solCount, since ∑ f = #cube * n^l = Ncard * ∑ solCount = ∑ g.
  have hle : ∑ g ∈ cube (D := D) C n, (n ^ (Fintype.card E))
      ≤ ∑ g ∈ cube (D := D) C n, Ncard * solCount c n g := by
    rw [Finset.sum_const, ← Finset.mul_sum, hsum, hcardcube, smul_eq_mul]
    -- goal: Ncard * n^l ≤ Ncard * n^l
  obtain ⟨g, hg_mem, hg⟩ := Finset.exists_le_of_sum_le hcube_ne hle
  exact ⟨g, hg⟩

end VC.Degeneration
