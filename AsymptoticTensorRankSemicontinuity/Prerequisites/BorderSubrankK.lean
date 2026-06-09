/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.TensorK
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Border Subrank for k-Tensors

This file contains the declarations from the underlying matrix-theoretic
development that this repository uses.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open BigOperators

namespace TensorK

variable (F : Type*) [Field F]

/-- The border subrank of a k-tensor with m factors.

    This is the supremum of s such that there exist polynomial families
    `A : (j : Fin m) → Fin s → alpha j → Polynomial F` satisfying:
    1. All coefficients below degree N vanish (vanishing condition)
    2. The N-th coefficient equals the identity k-tensor (identity condition)

    The sum is over all tuples `g : (j : Fin m) → alpha j` and the product
    is over all m factors. -/
noncomputable def borderSubrankK (m : ℕ) (alpha : Fin m → Type*)
    [∀ j, Fintype (alpha j)] [∀ j, DecidableEq (alpha j)]
    (T : TensorK F m alpha) : ℕ :=
  sSup {s : ℕ | ∃ (N : ℕ)
    (A : (j : Fin m) → Fin s → alpha j → Polynomial F),
    -- Vanishing below degree N
    (∀ (ρ : Fin m → Fin s), ∀ n : ℕ, n < N →
      (∑ g : (j : Fin m) → alpha j,
        (∏ j : Fin m, A j (ρ j) (g j)) * Polynomial.C (T g)).coeff n = 0) ∧
    -- The N-th coefficient equals the identity k-tensor
    (∀ (ρ : Fin m → Fin s),
      (∑ g : (j : Fin m) → alpha j,
        (∏ j : Fin m, A j (ρ j) (g j)) * Polynomial.C (T g)).coeff N =
      identityK F m s ρ)}

end TensorK
