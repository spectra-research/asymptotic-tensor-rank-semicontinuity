/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.Data.Fin.Basic

/-!
# Tensors over arbitrary finite index types (`TensorK`)

This file contains the declarations from the underlying matrix-theoretic
development that this repository uses.
-/

/-! ### k-Tensor Type -/

/-- A k-tensor with m factors, where factor j has index type `idx j`.
    This is the function type from dependent tuples to the coefficient ring. -/
def TensorK (R : Type*) (m : ℕ) (idx : Fin m → Type*) :=
  ((j : Fin m) → idx j) → R

namespace TensorK

/-! ### Unit/Identity k-Tensor -/

variable (R : Type*)

/-- The identity/unit k-tensor: entry is 1 iff all indices are equal.
    For m factors each indexed by `Fin s`, this is the GHZ diagonal tensor. -/
def identityK [One R] [Zero R] (m s : ℕ) : TensorK R m (fun _ => Fin s) :=
  fun f => if ∀ j₁ j₂ : Fin m, f j₁ = f j₂ then 1 else 0

end TensorK
