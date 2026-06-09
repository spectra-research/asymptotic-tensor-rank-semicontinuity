/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.RingTheory.Henselian
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Semicontinuity: admissible functionals and Zariski closure

Source: Christandl–Hoeberechts–Nieuwboer–Vrana–Zuiddam,
*Asymptotic tensor rank is characterized by polynomials* (arXiv:2411.15789).

This file fixes the abstract setup of §2.1–§2.2 of the paper:
* `AdmissibleFunctional V` — Definition 2.1 (tex:525-551).
* `AdmissibleFunctional.regularize` — the regularization
  `F̃(T) = ⨅ n, F_n(T^{⊗n})^{1/n}` of Definition 2.1 (tex:540-545).
* `zariskiClosure A` — the Zariski closure of a subset of an `F`-vector space,
  as defined at tex:578-583.

All vector spaces in the paper are finite-dimensional (tex:391), so we carry
`[Module.Finite F V]` throughout.
-/

namespace Semicontinuity

open scoped TensorProduct

universe u v

variable {F : Type u} [Field F]
variable {V : Type v} [AddCommGroup V] [Module F V] [Module.Finite F V]

/-! ## Admissible functionals — Definition 2.1 (tex:525-551)

The paper's `\begin{definition}[Admissible functional] \label{def:admissible functional}`
fixes a vector space `V` over a field `F` and a family of functions
`F_n : V^{⊗n} → ℝ_{≥0}` indexed by `n ∈ ℤ_{≥1}` (tex:528) satisfying:

  (i)   `F_n(T + S) ≤ F_n(T) + F_n(S)`                                            (tex:530)
  (ii)  `F_{n+n'}(T ⊗ S) ≤ F_n(T) · F_{n'}(S)`                                    (tex:531)
  (iii) `F_{n_1 + ⋯ + n_ℓ}(T_1 ⊗ ⋯ ⊗ T_ℓ)` is invariant under permutation of factors (tex:532)
  (iv)  `F_n(α · T) = F_n(T)` for `α ∈ F^×`                                       (tex:533)
  (v)   `F_1` is bounded: `∃ c, ∀ T ∈ V, F_1(T) ≤ c`                              (tex:534-536)

We index by `ℕ+` to match the paper's `ℤ_{≥1}`.

Properties (ii) and (iii) require canonical isomorphisms of tensor powers,
which we treat formally below via the existing `TensorPower R n M = ⨂[R]^n M`
notation in Mathlib. The associator (`TensorPower R (n + n') M ≃ₗ[R]
TensorPower R n M ⊗[R] TensorPower R n' M`) and permutation action of
`Equiv.Perm (Fin ℓ)` on `TensorPower R (n_1 + ⋯ + n_ℓ) M` are encoded via
`tensorPowerAdd` / `tensorPowerPerm` below.
-/

/-- Canonical iso `TensorPower R (m + n) M ≃ₗ[R] TensorPower R m M ⊗[R] TensorPower R n M`.

Used to state property (ii) of `AdmissibleFunctional` (tex:531). Realized as
the inverse of mathlib's `TensorPower.mulEquiv`. -/
noncomputable def tensorPowerAdd
    (R : Type*) [CommSemiring R] (M : Type*) [AddCommMonoid M] [Module R M] (m n : ℕ) :
    TensorPower R (m + n) M ≃ₗ[R] TensorPower R m M ⊗[R] TensorPower R n M :=
  TensorPower.mulEquiv.symm

/-- Block tensor-product assembly: given `Ts i : TensorPower F (nVec i) V` for
`i : Fin ℓ`, produces `T_1 ⊗ ⋯ ⊗ T_ℓ : TensorPower F (∑ nVec) V`.

Used to state property (iii) of `AdmissibleFunctional` (tex:532), where the
paper's invariance is on block-decomposable tensors `T_1 ⊗ ⋯ ⊗ T_ℓ`.

**Implementation**: recursive on `ℓ`. For `ℓ = 0` we have `∑ _ : Fin 0, _ = 0`
and the value is `TensorPower.algebraMap₀ 1 : TensorPower R 0 M`. For `ℓ + 1`
we glue `Ts 0 : TensorPower R (nVec 0) M` with the recursive tail
`tensorPowerBlock (nVec ∘ Fin.succ) (Ts ∘ Fin.succ) :
  TensorPower R (∑ i : Fin ℓ, nVec i.succ) M` via `TensorPower.mulEquiv`,
then cast across the equality `∑ i : Fin (ℓ+1), nVec i = nVec 0 + ∑ i, nVec i.succ`
(which is `Fin.sum_univ_succ`). -/
noncomputable def tensorPowerBlock
    (R : Type*) [CommSemiring R] (M : Type*) [AddCommMonoid M] [Module R M] :
    ∀ {ℓ : ℕ} (nVec : Fin ℓ → ℕ) (_ : ∀ i : Fin ℓ, TensorPower R (nVec i) M),
      TensorPower R (∑ i, nVec i) M
  | 0, _, _ =>
      -- ∑ i : Fin 0, _ = 0, so the result type is TensorPower R 0 M.
      (TensorPower.cast R M (by simp : (0 : ℕ) = ∑ i : Fin 0, (0 : ℕ)))
        (TensorPower.algebraMap₀ (1 : R))
  | ℓ + 1, nVec, Ts =>
      -- Recurse on the tail nVec ∘ Fin.succ, glue with TensorPower.mulEquiv,
      -- and cast across `∑ i : Fin (ℓ+1), nVec i = nVec 0 + ∑ i : Fin ℓ, nVec i.succ`.
      (TensorPower.cast R M
        (Fin.sum_univ_succ (fun i => nVec i)).symm)
        (TensorPower.mulEquiv
          (Ts 0 ⊗ₜ[R]
            tensorPowerBlock R M (fun i : Fin ℓ => nVec i.succ)
              (fun i : Fin ℓ => Ts i.succ)))

/-- **Definition 2.1** (Admissible functional, tex:525-551, `\label{def:admissible functional}`).

A family `F_n : V^{⊗n} → ℝ_{≥0}`, indexed by `n ∈ ℕ+`, satisfying subadditivity,
submultiplicativity under the tensor product, permutation-invariance,
scalar-invariance, and `F_1`-boundedness. -/
structure AdmissibleFunctional (F : Type u) (V : Type v)
    [Field F] [AddCommGroup V] [Module F V] where
  /-- The level-`n` component `F_n : V^{⊗n} → ℝ_{≥0}` (tex:528, indexed over `ℕ+`). -/
  toFun (n : ℕ+) : TensorPower F (n : ℕ) V → NNReal
  /-- (i) Subadditivity: `F_n(T + S) ≤ F_n(T) + F_n(S)` (tex:530). -/
  subadd (n : ℕ+) (T S : TensorPower F (n : ℕ) V) :
    toFun n (T + S) ≤ toFun n T + toFun n S
  /-- (ii) Submultiplicativity (tex:531): `F_{n+n'}(T ⊗ S) ≤ F_n(T) · F_{n'}(S)`,
      stated through the canonical iso `tensorPowerAdd`. -/
  submul (n n' : ℕ+) (T : TensorPower F (n : ℕ) V) (S : TensorPower F (n' : ℕ) V) :
    toFun ⟨(n : ℕ) + (n' : ℕ), Nat.add_pos_left n.pos _⟩
      ((tensorPowerAdd F V (n : ℕ) (n' : ℕ)).symm (T ⊗ₜ[F] S))
      ≤ toFun n T * toFun n' S
  /-- (iii) Permutation invariance of `F` on a block tensor product (tex:532).

      The paper's `F_{n_1+⋯+n_ℓ}(T_1 ⊗ ⋯ ⊗ T_ℓ) = F_{n_1+⋯+n_ℓ}(T_{σ(1)} ⊗ ⋯ ⊗ T_{σ(ℓ)})`
      is stated only on block-decomposable tensors, not all of `V^{⊗(∑ n_i)}`. -/
  perm_inv {ℓ : ℕ} (nVec : Fin ℓ → ℕ+) (σ : Equiv.Perm (Fin ℓ))
    (Ts : ∀ i : Fin ℓ, TensorPower F (nVec i : ℕ) V)
    (hpos₁ : 0 < ∑ i, (nVec i : ℕ)) (hpos₂ : 0 < ∑ i, ((nVec (σ i)) : ℕ)) :
    toFun ⟨_, hpos₁⟩ (tensorPowerBlock F V (fun i => (nVec i : ℕ)) Ts) =
    toFun ⟨_, hpos₂⟩
      (tensorPowerBlock F V (fun i => ((nVec (σ i)) : ℕ)) (fun i => Ts (σ i)))
  /-- (iv) Scalar invariance: `F_n(α • T) = F_n(T)` for `α ≠ 0` (tex:533). -/
  scalar_inv (n : ℕ+) (α : F) (hα : α ≠ 0) (T : TensorPower F (n : ℕ) V) :
    toFun n (α • T) = toFun n T
  /-- (v) `F_1` is bounded by some constant `c` (tex:534-536). -/
  bdd_one : ∃ c : NNReal, ∀ T : TensorPower F 1 V, toFun 1 T ≤ c

/-- The `n`-th tensor power of `T : V` as an element of `V^{⊗n}`.
    Realized as `PiTensorProduct.tprod` applied to the constant family `fun _ => T`. -/
noncomputable def tensorPow (n : ℕ+) (T : V) : TensorPower F (n : ℕ) V :=
  PiTensorProduct.tprod F (fun _ : Fin (n : ℕ) => T)

namespace AdmissibleFunctional

instance : CoeFun (AdmissibleFunctional F V)
    (fun _ => ∀ n : ℕ+, TensorPower F (n : ℕ) V → NNReal) :=
  ⟨fun Func n => Func.toFun n⟩

/-- **Regularization** `F̃(T) = ⨅ n, F_n(T^{⊗n})^{1/n}` (tex:540-545).

    The paper notes the limit exists by Fekete's lemma and equals the infimum;
    we take the infimum form as the definition. -/
noncomputable def regularize (Func : AdmissibleFunctional F V) (T : V) : ℝ :=
  ⨅ n : ℕ+, ((Func.toFun n (tensorPow (F := F) (V := V) n T) : ℝ)) ^ ((1 : ℝ) / (n : ℕ))

@[inherit_doc] scoped notation "F̃" => AdmissibleFunctional.regularize

/-- **`asympFunctional[A]`** (tex:546-549):
    `F̃[A] = sup_{T ∈ A} F̃(T)`. -/
noncomputable def asympOnSet (Func : AdmissibleFunctional F V) (A : Set V) : ℝ :=
  ⨆ T ∈ A, Func.regularize T

end AdmissibleFunctional

/-! ## Polynomial functions on `V` and Zariski closure — tex:578-583

The paper writes (for a vector space `V` over a field `F`, with `F[V]` the polynomial
functions on `V`):

```
\overline{A} = { T ∈ V : ∀ f ∈ F[V], f|_A ≡ 0 ⇒ f(T) = 0 }
```

We encode `F[V]` via `MvPolynomial (Fin n) F` evaluated through a chosen basis
of the finite-dimensional `V`. The resulting set is basis-independent; a
`zariskiClosure_eq` lemma would state the change-of-basis invariance explicitly.
-/

/-- A function `V → F` is **polynomial** if, for some (equivalently, every) basis,
it is the pullback of an `MvPolynomial` evaluated on coordinates.

We use `Module.finBasis` as the canonical choice. -/
def IsPolynomialFunction (f : V → F) : Prop :=
  ∃ p : MvPolynomial (Fin (Module.finrank F V)) F,
    ∀ T : V, f T = MvPolynomial.eval (fun i => (Module.finBasis F V).repr T i) p

/-- **Zariski closure** of `A ⊆ V` (tex:578-583).

`T ∈ Z̄(A)` iff every polynomial function `f : V → F` that vanishes on all of `A`
also vanishes at `T`. -/
def zariskiClosure (A : Set V) : Set V :=
  { T : V | ∀ f : V → F, IsPolynomialFunction (F := F) (V := V) f →
      (∀ S ∈ A, f S = 0) → f T = 0 }

/-- `A ⊆ V` is **Zariski-closed**: it equals its own Zariski-closure. -/
def IsZariskiClosed (A : Set V) : Prop :=
  zariskiClosure (F := F) A = A

/-- The `n`-th "power" of a subset, used in Lemma 2.3 (tex:622):
    `A^{(n)} = { T^{⊗n} : T ∈ A } ⊆ V^{⊗n}`, for `n ∈ ℕ+`. -/
def powerSet (A : Set V) (n : ℕ+) : Set (TensorPower F (n : ℕ) V) :=
  { S | ∃ T ∈ A, S = tensorPow (F := F) (V := V) n T }

end Semicontinuity
