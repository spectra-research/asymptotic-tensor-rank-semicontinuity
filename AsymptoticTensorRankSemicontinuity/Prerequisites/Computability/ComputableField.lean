/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.Computability.Halting
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Computable fields

A field is **computable** in the sense of Rabin (*Computable algebra, general
theory and theory of computable fields*, Trans. AMS 95, 1960) if it admits an
*admissible indexing*: a one-to-one coding of its elements into the natural
numbers with recursive range, under which the field operations are computable
functions on codes (Rabin, Definitions 3–5 applied to fields, §2.1).

We render the admissible indexing as a `Primcodable` instance and the
operation conditions as `Computable₂` facts. Following Rabin, nothing else is
assumed: equality of elements is decidable computably because the coding is
injective into `ℕ`, and computability of negation and inversion is derivable
(Rabin, Lemma 1) rather than postulated.
-/

universe u

/-- **Computable ring** (Rabin 1960, §1.6, tex:264: "computable fields are a
special case of computable rings"): a commutative ring with a `Primcodable`
coding under which addition and multiplication are computable. -/
class ComputableRing (R : Type u) [CommRing R] [Primcodable R] : Prop where
  /-- Addition is computable on codes. -/
  computable_add : Computable₂ ((· + ·) : R → R → R)
  /-- Multiplication is computable on codes. -/
  computable_mul : Computable₂ ((· * ·) : R → R → R)

/-- **Computable field** (Rabin 1960, Definitions 3–5 and §2.1): a field with a
`Primcodable` coding under which addition and multiplication are computable. -/
class ComputableField (F : Type u) [Field F] [Primcodable F] : Prop where
  /-- Addition is computable on codes. -/
  computable_add : Computable₂ ((· + ·) : F → F → F)
  /-- Multiplication is computable on codes. -/
  computable_mul : Computable₂ ((· * ·) : F → F → F)

instance ComputableField.toComputableRing {F : Type u} [Field F]
    [Primcodable F] [ComputableField F] : ComputableRing F :=
  ⟨ComputableField.computable_add, ComputableField.computable_mul⟩

namespace ComputableRing

variable {R : Type u} [CommRing R] [Primcodable R] [ComputableRing R]

/-- Negation is computable: `-a = (-1) * a`. -/
theorem computable_neg : Computable (Neg.neg : R → R) :=
  (computable_mul.comp (Computable.const (-1 : R)) Computable.id).of_eq
    fun a => neg_one_mul a

/-- Subtraction is computable. -/
theorem computable₂_sub : Computable₂ ((· - ·) : R → R → R) := by
  have h : Computable fun p : R × R => p.1 + -p.2 :=
    computable_add.comp Computable.fst (computable_neg.comp Computable.snd)
  exact (h.of_eq fun p => (sub_eq_add_neg p.1 p.2).symm).to₂

end ComputableRing

namespace ComputableField

variable {F : Type u} [Field F] [Primcodable F] [ComputableField F]

omit [Field F] [ComputableField F] in
/-- Equality is computably decidable in a computable field: the coding into `ℕ`
is injective, so equality of elements is equality of codes (Rabin, Definition 3). -/
theorem computablePred_eq : ComputablePred fun p : F × F => p.1 = p.2 :=
  PrimrecPred.computablePred Primrec.eq

omit [Field F] [ComputableField F] in
/-- Testing equality against a fixed element (in particular the zero test) is
computably decidable. -/
theorem computablePred_eq_const (c : F) : ComputablePred fun a : F => a = c :=
  PrimrecPred.computablePred (Primrec.eq.comp Primrec.id (Primrec.const c))

/-- Evaluating a fixed multivariate polynomial is computable in a computable
field: the evaluation is a finite arithmetic circuit in the (computable)
addition and multiplication, with the coefficients as fixed constants. -/
theorem computable_mvPolynomial_eval {N : ℕ} (q : MvPolynomial (Fin N) F) :
    Computable fun v : Fin N → F => MvPolynomial.eval v q := by
  induction q using MvPolynomial.induction_on with
  | C a => exact (Computable.const a).of_eq (by simp)
  | add p₁ p₂ h₁ h₂ =>
      exact (computable_add.comp h₁ h₂).of_eq (by simp)
  | mul_X p i h =>
      have hproj : Computable fun v : Fin N → F => v i :=
        (Primrec.fin_app.comp .id (.const i)).to_comp
      exact (computable_mul.comp h hproj).of_eq (by simp)

end ComputableField
