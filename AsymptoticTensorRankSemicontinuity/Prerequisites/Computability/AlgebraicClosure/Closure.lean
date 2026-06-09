/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.AlgebraicClosure.GreedyMaximal

/-!
# `ComputableAlgebraicClosure F := R / U`: the computable algebraic closure

With `U` a maximal ideal of `R = F[x₁,x₂,…]` containing `Γ₁`, the quotient
`ComputableAlgebraicClosure F := R ⧸ U` is a field (Rabin `rabin.tex`:400-408).  This
file sets up the field/algebra structure and proves the **splitting** half of
"`ComputableAlgebraicClosure F` is the algebraic closure of `F`": every monic
`f ∈ F[t]` splits into linear factors in `ComputableAlgebraicClosure F`, because its
Vieta block lies in `U`.
-/

universe u

namespace Semicontinuity
namespace GreedyIdeal

open Polynomial

variable {F : Type u} [Field F] [Primcodable F] [ComputableField F]

/-- Rabin's computable algebraic closure `R / U` (`rabin.tex`:400). -/
noncomputable abbrev ComputableAlgebraicClosure (F : Type u) [Field F] [Primcodable F]
    [ComputableField F] : Type u :=
  MvPolynomial ℕ F ⧸ U (F := F)

noncomputable instance : Field (ComputableAlgebraicClosure F) := Ideal.Quotient.field (U (F := F))

/-- The quotient map `R → ComputableAlgebraicClosure F`. -/
noncomputable abbrev mk : MvPolynomial ℕ F →+* ComputableAlgebraicClosure F :=
  Ideal.Quotient.mk (U (F := F))

theorem mk_comp_C :
    (mk (F := F)).comp (MvPolynomial.C) = algebraMap F (ComputableAlgebraicClosure F) := by
  rfl

/-- The image in `ComputableAlgebraicClosure F` of a polynomial that lies in `U` is zero. -/
theorem mk_eq_zero_of_mem_U {p : MvPolynomial ℕ F} (h : p ∈ U (F := F)) :
    mk (F := F) p = 0 := by
  rwa [Ideal.Quotient.eq_zero_iff_mem]

/-! ## Splitting -/

/-- The Vieta block of `f_j`, mapped into `ComputableAlgebraicClosure F`, equals `f_j` mapped in. -/
theorem map_blockProd_eq_map_enumMonic (j : ℕ) :
    (blockProd F j).map (mk (F := F)) =
      (enumMonic F j).map (algebraMap F (ComputableAlgebraicClosure F)) := by
  apply Polynomial.ext
  intro k
  rw [Polynomial.coeff_map, Polynomial.coeff_map]
  -- `mk ((blockProd j).coeff k) = algebraMap ((enumMonic j).coeff k)`
  by_cases hk : k ≤ blockDeg F j
  · -- coefficient difference is a Vieta equation, hence in `U`
    have hmem : (blockProd F j).coeff k - MvPolynomial.C ((enumMonic F j).coeff k)
        ∈ U (F := F) := by
      refine gamma1Flat_subset_U (F := F) (j + 1) _ ?_
      rw [mem_gamma1Flat_iff]
      refine ⟨j, Nat.lt_succ_self j, ?_⟩
      rw [vietaEqs, List.mem_map]
      exact ⟨k, List.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩
    have := mk_eq_zero_of_mem_U (F := F) hmem
    rw [map_sub, sub_eq_zero] at this
    rw [this]
    rfl
  · -- both coefficients vanish beyond the degree
    push_neg at hk
    have hbp : (blockProd F j).coeff k = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [blockProd_natDegree]; exact hk
    have hem : (enumMonic F j).coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt hk
    rw [hbp, hem, map_zero, map_zero]

/-- `f_j` mapped into `ComputableAlgebraicClosure F` is the product of linear factors
`X - C (root)`. -/
theorem map_enumMonic_eq_prod (j : ℕ) :
    (enumMonic F j).map (algebraMap F (ComputableAlgebraicClosure F)) =
      ∏ i : Fin (blockDeg F j),
        (Polynomial.X - Polynomial.C (mk (F := F) (MvPolynomial.X (blockVar F j i)))) := by
  rw [← map_blockProd_eq_map_enumMonic, blockProd, Polynomial.map_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

/-- **Every monic `f_j` splits in `ComputableAlgebraicClosure F`.** -/
theorem enumMonic_splits (j : ℕ) :
    Polynomial.Splits ((enumMonic F j).map (algebraMap F (ComputableAlgebraicClosure F))) := by
  rw [map_enumMonic_eq_prod]
  exact Polynomial.Splits.prod (fun i _ => Polynomial.Splits.X_sub_C _)

/-- **Every monic polynomial of positive degree splits in `ComputableAlgebraicClosure F`.** -/
theorem monic_splits {f : Polynomial F} (hm : f.Monic) (hd : 1 ≤ f.natDegree) :
    Polynomial.Splits (f.map (algebraMap F (ComputableAlgebraicClosure F))) := by
  have := enumMonic_splits (F := F) (Encodable.encode f)
  rwa [enumMonic_surj (F := F) f hm hd] at this

end GreedyIdeal
end Semicontinuity
