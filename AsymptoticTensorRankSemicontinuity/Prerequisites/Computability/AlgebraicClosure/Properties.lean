/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.AlgebraicClosure.Closure

/-!
# `ComputableAlgebraicClosure F` is the algebraic closure of `F`

The two halves of Rabin's Theorem 7 conclusion (`rabin.tex`:415-427):

* **Algebraicity** `Algebra.IsIntegral F (ComputableAlgebraicClosure F)`: every variable
  image `mk (X n)` is a root of a monic block polynomial (hence integral), and these generate
  `ComputableAlgebraicClosure F`, so the whole quotient is integral over `F`.
* **Splitting**: every monic polynomial splits.

Together with `IsAlgClosure.of_splits` these give `IsAlgClosure F (ComputableAlgebraicClosure F)` —
`ComputableAlgebraicClosure F` is the algebraic closure of `F`.
-/

universe u

namespace Semicontinuity
namespace GreedyIdeal

open Polynomial

variable {F : Type u} [Field F] [Primcodable F] [ComputableField F]

/-! ## Every variable lies in a block -/

omit [ComputableField F] in
/-- The blocks tile `ℕ`: every variable index is `blockVar j i` for some block. -/
theorem exists_blockVar_eq (n : ℕ) :
    ∃ (j : ℕ) (i : Fin (blockDeg F j)), blockVar F j i = n := by
  set j₀ := Nat.findGreatest (fun j => blockOffset F j ≤ n) n with hj₀
  have hP0 : blockOffset F 0 ≤ n := by simp [blockOffset]
  have hle : blockOffset F j₀ ≤ n :=
    Nat.findGreatest_spec (P := fun j => blockOffset F j ≤ n) (Nat.zero_le n) hP0
  have hgt : n < blockOffset F (j₀ + 1) := by
    by_contra h
    push_neg at h
    have hj₁n : j₀ + 1 ≤ n := le_trans (le_blockOffset (F := F) (j₀ + 1)) h
    have : j₀ + 1 ≤ j₀ := Nat.le_findGreatest hj₁n h
    omega
  rw [blockOffset_succ] at hgt
  have hi : n - blockOffset F j₀ < blockDeg F j₀ := by omega
  exact ⟨j₀, ⟨n - blockOffset F j₀, hi⟩, by simp [blockVar]; omega⟩

/-! ## Algebraicity -/

/-- Each variable image is a root of its block's monic polynomial, hence integral. -/
theorem isIntegral_mk_X (n : ℕ) :
    IsIntegral F (mk (F := F) (MvPolynomial.X n)) := by
  obtain ⟨j, i, hji⟩ := exists_blockVar_eq (F := F) n
  refine ⟨enumMonic F j, enumMonic_monic (F := F) j, ?_⟩
  -- the goal is `eval₂ (algebraMap) (mk (X n)) (enumMonic j) = 0`
  rw [← Polynomial.eval_map, map_enumMonic_eq_prod, Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, hji, sub_self]

/-- The variable images generate `ComputableAlgebraicClosure F` as an `F`-algebra. -/
theorem adjoin_range_mk_X_eq_top :
    Algebra.adjoin F (Set.range fun n => mk (F := F) (MvPolynomial.X n)) = ⊤ := by
  have hmk : Function.Surjective (Ideal.Quotient.mkₐ F (U (F := F))) :=
    Ideal.Quotient.mkₐ_surjective F _
  rw [show (Set.range fun n => mk (F := F) (MvPolynomial.X n))
      = (Ideal.Quotient.mkₐ F (U (F := F))) '' Set.range MvPolynomial.X by
    rw [← Set.range_comp]; rfl]
  rw [← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top]
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨a, ha⟩ := hmk x
  exact ⟨a, ha⟩

/-- **Algebraicity**: `ComputableAlgebraicClosure F` is integral (algebraic) over `F`. -/
instance : Algebra.IsIntegral F (ComputableAlgebraicClosure F) := by
  rw [← integralClosure_eq_top_iff, eq_top_iff, ← adjoin_range_mk_X_eq_top (F := F)]
  refine Algebra.adjoin_le ?_
  rintro x ⟨n, rfl⟩
  exact isIntegral_mk_X (F := F) n

/-! ## The algebraic closure -/

/-- **Rabin Theorem 7** (`rabin.tex`:415-427): `ComputableAlgebraicClosure F` is the algebraic
closure of `F`.  Every monic irreducible polynomial splits and
`ComputableAlgebraicClosure F` is integral over `F`, so by `IsAlgClosure.of_splits` it is an
algebraic closure. -/
instance instIsAlgClosure : IsAlgClosure F (ComputableAlgebraicClosure F) :=
  IsAlgClosure.of_splits fun _ hm hirr =>
    monic_splits (F := F) hm hirr.natDegree_pos

instance : IsAlgClosed (ComputableAlgebraicClosure F) := instIsAlgClosure.isAlgClosed

instance : Algebra.IsAlgebraic F (ComputableAlgebraicClosure F) := instIsAlgClosure.isAlgebraic

/-- Rabin's computable algebraic closure agrees, up to an `F`-algebra isomorphism,
with Mathlib's (noncomputable, Zorn-built) `AlgebraicClosure F`: both are
algebraic closures of `F`, and any two algebraic closures of a field are
isomorphic (`IsAlgClosure.equiv`).  Necessarily noncomputable, since
`AlgebraicClosure F` and the comparison are. -/
noncomputable def equivAlgebraicClosure :
    ComputableAlgebraicClosure F ≃ₐ[F] AlgebraicClosure F :=
  IsAlgClosure.equiv F (ComputableAlgebraicClosure F) (AlgebraicClosure F)

end GreedyIdeal
end Semicontinuity
