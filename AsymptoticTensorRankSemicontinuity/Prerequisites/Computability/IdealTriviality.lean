/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Adjoin.Polynomial
import Mathlib.RingTheory.Ideal.Operations

/-!
# Ideal triviality and common zeroes

Rabin's Lemma 5 proof (Rabin 1960, `rabin.tex`:336-351) invokes the standard
weak Nullstellensatz equivalence: an equation
`r₁ f₁ + ⋯ + rₙ fₙ = 1` is solvable exactly when the equations `fᵢ = 0` have
no common solution in the algebraic closure of the coefficient field.

This file formalizes only that pure algebraic equivalence.  This is the audited
plan's deviation D1: instead of formalizing Rabin's elimination-theoretic
search argument here, we use Mathlib's Nullstellensatz, where Rabin writes that
the equivalence is "well known".  Rabin states the certificates in the full
polynomial ring `F[x₁, x₂, ...]`; the finite-variable certificate coefficients
used below are without loss for this stage because the input polynomials use
only the displayed variables.  The reduction from a full ring with fresh
variables is reserved for Phase D.
-/

noncomputable section

universe u

namespace Semicontinuity

open scoped BigOperators

open MvPolynomial
open Polynomial

variable {F : Type u} [Field F]

private theorem polynomial_aeval_mv_aeval {A : Type*} [CommSemiring A] [Algebra F A]
    {m : ℕ} (y : A) (g : Fin m → Polynomial F) (q : MvPolynomial (Fin m) F) :
    Polynomial.aeval y (MvPolynomial.aeval g q) =
      MvPolynomial.aeval (fun j => Polynomial.aeval y (g j)) q :=
  MvPolynomial.comp_aeval_apply g (Polynomial.aeval y) q

private theorem span_singleton_ne_top_of_natDegree_pos (p : Polynomial F)
    (hdeg : 1 ≤ p.natDegree) : Ideal.span ({p} : Set (Polynomial F)) ≠ ⊤ := by
  rw [Ideal.ne_top_iff_one]
  intro h1
  have hp_dvd_one : p ∣ (1 : Polynomial F) := by
    rwa [Ideal.mem_span_singleton] at h1
  have hunit : IsUnit p := isUnit_of_dvd_one hp_dvd_one
  have hdeg0 : p.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hunit
  omega

private theorem finite_quotient_of_span_singleton_le (p : Polynomial F) (hmonic : p.Monic)
    (M : Ideal (Polynomial F)) (hle : Ideal.span ({p} : Set (Polynomial F)) ≤ M) :
    Module.Finite F (Polynomial F ⧸ M) := by
  let q : AdjoinRoot p →ₐ[F] Polynomial F ⧸ M := Ideal.Quotient.factorₐ F hle
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mkₐ_surjective F M x
    exact ⟨AdjoinRoot.mk p r, rfl⟩
  haveI : Module.Finite F (AdjoinRoot p) := hmonic.finite_adjoinRoot
  exact Module.Finite.of_surjective q.toLinearMap hq

private theorem list_sum_ofFn_eq_finset_sum {R : Type*} [AddCommMonoid R] {n : ℕ}
    (g : Fin n → R) : (List.ofFn g).sum = ∑ i, g i := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, Fin.sum_univ_succ]
      exact congrArg (g 0 + ·) (ih fun i => g i.succ)

private theorem zipWith_ofFn_eq_ofFn {α β γ : Type*} {n : ℕ} (g : α → β → γ)
    (a : Fin n → α) (b : Fin n → β) :
    List.zipWith g (List.ofFn a) (List.ofFn b) = List.ofFn fun i => g (a i) (b i) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.zipWith_cons_cons, List.ofFn_succ]
      exact congrArg (g (a 0) (b 0) :: ·) (ih (fun i => a i.succ) fun i => b i.succ)

private theorem zipWith_mul_sum_eq_finset_sum_get {R : Type*} [Semiring R] :
    ∀ (rs fs : List R) (h : rs.length = fs.length),
      (List.zipWith (· * ·) rs fs).sum =
        ∑ i : Fin fs.length, rs[i.val]'(by rw [h]; exact i.isLt) * fs[i]
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | r :: rs, f :: fs, h => by
      have htail : rs.length = fs.length := Nat.succ.inj h
      calc
        (List.zipWith (· * ·) (r :: rs) (f :: fs)).sum
            = r * f + ∑ i : Fin fs.length, rs[i.val]'(by rw [htail]; exact i.isLt) * fs[i] := by
              rw [List.zipWith_cons_cons, List.sum_cons,
                zipWith_mul_sum_eq_finset_sum_get rs fs htail]
        _ = ∑ i : Fin (f :: fs).length,
              (r :: rs)[i.val]'(by rw [h]; exact i.isLt) * (f :: fs)[i] := by
              simp [Fin.sum_univ_succ]

private theorem common_zero_get_iff_common_zero_mem {m : ℕ}
    (fs : List (MvPolynomial (Fin m) F)) :
    (∃ ξ : Fin m → AlgebraicClosure F, ∀ i : Fin fs.length,
        MvPolynomial.aeval ξ fs[i] = 0) ↔
      ∃ ξ : Fin m → AlgebraicClosure F, ∀ g ∈ fs, MvPolynomial.aeval ξ g = 0 := by
  constructor
  · rintro ⟨ξ, hξ⟩
    refine ⟨ξ, ?_⟩
    intro g hg
    rw [List.mem_iff_get] at hg
    obtain ⟨i, rfl⟩ := hg
    exact hξ i
  · rintro ⟨ξ, hξ⟩
    refine ⟨ξ, ?_⟩
    intro i
    exact hξ fs[i] (List.getElem_mem i.isLt)

/-- Rabin Lemma 5 (`rabin.tex`:336-351), Nullstellensatz form:
`1` lies in the ideal generated by finitely many polynomials iff those
polynomials have no common zero over the algebraic closure. -/
theorem one_mem_span_iff_no_common_zero {m n : ℕ}
    (f : Fin n → MvPolynomial (Fin m) F) :
    (1 : MvPolynomial (Fin m) F) ∈ Ideal.span (Set.range f) ↔
      ¬ ∃ ξ : Fin m → AlgebraicClosure F, ∀ i, MvPolynomial.aeval ξ (f i) = 0 := by
  let I : Ideal (MvPolynomial (Fin m) F) := Ideal.span (Set.range f)
  constructor
  · intro h1 hξ
    obtain ⟨ξ, hξ⟩ := hξ
    have hξI : ξ ∈ MvPolynomial.zeroLocus (AlgebraicClosure F) I := by
      rw [MvPolynomial.zeroLocus_span]
      intro p hp
      obtain ⟨i, rfl⟩ := hp
      exact hξ i
    exact (one_ne_zero (α := AlgebraicClosure F)) (by simpa using hξI 1 h1)
  · intro hno
    have hzero : MvPolynomial.zeroLocus (AlgebraicClosure F) I = ∅ := by
      rw [MvPolynomial.zeroLocus_span]
      ext ξ
      constructor
      · intro hξ
        exfalso
        exact hno ⟨ξ, fun i => hξ (f i) ⟨i, rfl⟩⟩
      · intro hξ
        cases hξ
    have hrad : I.radical = ⊤ := by
      rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical
        (K := AlgebraicClosure F) I, hzero, MvPolynomial.vanishingIdeal_empty]
    have htop : I = ⊤ := Ideal.radical_eq_top.mp hrad
    change (1 : MvPolynomial (Fin m) F) ∈ I
    rw [htop]
    exact Submodule.mem_top

/-- Rabin Lemma 5 (`rabin.tex`:336-351), certificate form:
the equation `∑ i, rᵢ fᵢ = 1` is solvable iff the `fᵢ` have no common zero in
the algebraic closure. -/
theorem exists_certificate_iff_no_common_zero {m n : ℕ}
    (f : Fin n → MvPolynomial (Fin m) F) :
    (∃ r : Fin n → MvPolynomial (Fin m) F, ∑ i, r i * f i = 1) ↔
      ¬ ∃ ξ : Fin m → AlgebraicClosure F, ∀ i, MvPolynomial.aeval ξ (f i) = 0 := by
  rw [← one_mem_span_iff_no_common_zero f, Ideal.mem_span_range_iff_exists_fun]

/-- Rabin Lemma 5 (`rabin.tex`:336-351), audited deviation D1, soundness of the
negative-search witness.

The witness is not Rabin's elimination process.  It is the search candidate used
in the audited plan: a monic polynomial `p ∈ F[y]` of positive degree and
polynomial coordinates `g j ∈ F[y]`.  The divisibilities say that the tuple
`g j (θ)` is a common zero in the finite algebra `F[y] ⧸ (p)`.  Soundness pushes
this candidate through a maximal ideal over `(p)` and then through
`IsAlgClosed.lift` into the algebraic closure.  No perfectness hypothesis is
used here. -/
theorem common_zero_of_candidate {m n : ℕ}
    (f : Fin n → MvPolynomial (Fin m) F) (p : Polynomial F) (hmonic : p.Monic)
    (hdeg : 1 ≤ p.natDegree) (g : Fin m → Polynomial F)
    (h : ∀ i, p ∣ MvPolynomial.aeval g (f i)) :
    ∃ ξ : Fin m → AlgebraicClosure F, ∀ i, MvPolynomial.aeval ξ (f i) = 0 := by
  let I : Ideal (Polynomial F) := Ideal.span ({p} : Set (Polynomial F))
  have hI : I ≠ ⊤ := span_singleton_ne_top_of_natDegree_pos p hdeg
  obtain ⟨M, hMmax, hIM⟩ := Ideal.exists_le_maximal I hI
  letI : Field (Polynomial F ⧸ M) := Ideal.Quotient.field M
  haveI : Module.Finite F (Polynomial F ⧸ M) :=
    finite_quotient_of_span_singleton_le p hmonic M hIM
  haveI : Algebra.IsAlgebraic F (Polynomial F ⧸ M) := inferInstance
  let φ : Polynomial F ⧸ M →ₐ[F] AlgebraicClosure F := IsAlgClosed.lift
  let ξ : Fin m → AlgebraicClosure F := fun j => φ (Ideal.Quotient.mk M (g j))
  refine ⟨ξ, ?_⟩
  intro i
  have hpM : p ∈ M := hIM (Ideal.subset_span (Set.mem_singleton p))
  have hmem : MvPolynomial.aeval g (f i) ∈ M := by
    obtain ⟨q, hq⟩ := h i
    rw [hq]
    exact M.mul_mem_right q hpM
  have hquot : Ideal.Quotient.mk M (MvPolynomial.aeval g (f i)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  calc
    MvPolynomial.aeval ξ (f i)
        = φ (MvPolynomial.aeval (fun j => Ideal.Quotient.mk M (g j)) (f i)) := by
          exact (MvPolynomial.comp_aeval_apply
            (φ := φ) (f := fun j => Ideal.Quotient.mk M (g j)) (f i)).symm
    _ = φ (Ideal.Quotient.mk M (MvPolynomial.aeval g (f i))) := by
          exact congrArg φ (by
            simpa [Function.comp_def] using
              (MvPolynomial.aeval_algebraMap_apply (B := Polynomial F ⧸ M) g (f i)))
    _ = 0 := by
          rw [hquot, map_zero]

/-- Rabin Lemma 5 (`rabin.tex`:336-351), audited deviation D1, completeness of
the negative-search witness.

This is the converse to `common_zero_of_candidate`: a common zero in `F̄` is
encoded by a monic positive-degree `p ∈ F[y]` and coordinates `g j ∈ F[y]`.
The proof uses perfectness only here, to make the finite field generated by the
coordinates separable and therefore primitive.  Then the primitive element
represents every coordinate as `g j (θ)`, and the minimal polynomial of `θ`
divides each substituted equation.  This replaces Rabin's elimination-theoretic
decision procedure by the audited candidate search. -/
theorem candidate_of_common_zero {m n : ℕ} [PerfectField F]
    (f : Fin n → MvPolynomial (Fin m) F)
    (h : ∃ ξ : Fin m → AlgebraicClosure F, ∀ i, MvPolynomial.aeval ξ (f i) = 0) :
    ∃ (p : Polynomial F) (g : Fin m → Polynomial F),
      p.Monic ∧ 1 ≤ p.natDegree ∧ ∀ i, p ∣ MvPolynomial.aeval g (f i) := by
  obtain ⟨ξ, hξ⟩ := h
  let K : IntermediateField F (AlgebraicClosure F) :=
    IntermediateField.adjoin F (Set.range ξ)
  haveI : Finite (Set.range ξ) := (Set.finite_range ξ).to_subtype
  have hKfin : FiniteDimensional F K := by
    dsimp [K]
    exact IntermediateField.finiteDimensional_adjoin (K := F)
      (L := AlgebraicClosure F) (S := Set.range ξ) fun x _ =>
        Algebra.IsIntegral.isIntegral x
  haveI : FiniteDimensional F K := hKfin
  haveI : Algebra.IsAlgebraic F K := inferInstance
  haveI : Algebra.IsSeparable F K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element F K
  have hθint : IsIntegral F θ := Algebra.IsIntegral.isIntegral θ
  have hθalg : IsAlgebraic F θ := hθint.isAlgebraic
  let θbar : AlgebraicClosure F := algebraMap K (AlgebraicClosure F) θ
  let xK : Fin m → K := fun j =>
    ⟨ξ j, IntermediateField.subset_adjoin F (Set.range ξ)
      (show ξ j ∈ Set.range ξ from ⟨j, rfl⟩)⟩
  have hxK_mem : ∀ j, (xK j : K) ∈ Algebra.adjoin F {θ} := by
    intro j
    have hmemIF : (xK j : K) ∈
        ((IntermediateField.adjoin F ({θ} : Set K)) : Set K) := by
      rw [hθ]
      exact trivial
    change (xK j : K) ∈
      ((IntermediateField.adjoin F ({θ} : Set K)).toSubalgebra : Set K) at hmemIF
    rwa [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθalg] at hmemIF
  choose g hg using fun j => Algebra.adjoin_mem_exists_aeval F θ (hxK_mem j)
  refine ⟨minpoly F θ, g, minpoly.monic hθint, minpoly.natDegree_pos hθint, ?_⟩
  intro i
  apply minpoly.dvd F θ
  apply (algebraMap K (AlgebraicClosure F)).injective
  calc
    algebraMap K (AlgebraicClosure F)
        (Polynomial.aeval θ (MvPolynomial.aeval g (f i)))
        = Polynomial.aeval θbar (MvPolynomial.aeval g (f i)) := by
          rw [Polynomial.aeval_algebraMap_apply]
    _ = MvPolynomial.aeval (fun j => Polynomial.aeval θbar (g j)) (f i) := by
          exact polynomial_aeval_mv_aeval θbar g (f i)
    _ = MvPolynomial.aeval ξ (f i) := by
          congr 1
          ext j
          have hj := congrArg (algebraMap K (AlgebraicClosure F)) (hg j)
          simpa [θbar, xK, Polynomial.aeval_algebraMap_apply] using hj
    _ = 0 := hξ i
    _ = algebraMap K (AlgebraicClosure F) 0 := by simp

/-- Rabin Lemma 5 (`rabin.tex`:336-351), audited deviation D1 search dichotomy.

Over a perfect field, either the positive certificate `∑ i, rᵢ fᵢ = 1` exists,
or the negative candidate search can return a monic positive-degree
`p ∈ F[y]` and coordinates `g j ∈ F[y]` whose residue class is a common zero in
a finite extension.  Perfectness is used only through
`candidate_of_common_zero`, not in the Nullstellensatz certificate direction. -/
theorem certificate_or_candidate {m n : ℕ} [PerfectField F]
    (f : Fin n → MvPolynomial (Fin m) F) :
    (∃ r : Fin n → MvPolynomial (Fin m) F, ∑ i, r i * f i = 1) ∨
      (∃ (p : Polynomial F) (g : Fin m → Polynomial F),
        p.Monic ∧ 1 ≤ p.natDegree ∧ ∀ i, p ∣ MvPolynomial.aeval g (f i)) := by
  by_cases hzero :
    ∃ ξ : Fin m → AlgebraicClosure F, ∀ i, MvPolynomial.aeval ξ (f i) = 0
  · exact Or.inr (candidate_of_common_zero f hzero)
  · exact Or.inl ((exists_certificate_iff_no_common_zero f).mpr hzero)

/-- Rabin Lemma 5 (`rabin.tex`:336-351), audited deviation D1 consistency.

A positive Bezout certificate and a negative candidate witness cannot both
exist.  The proof uses the Phase C1 Nullstellensatz form to turn the certificate
into absence of common zeroes, and `common_zero_of_candidate` to turn the
candidate into an actual common zero in `F̄`.  No perfectness hypothesis is
needed for this incompatibility. -/
theorem not_certificate_and_candidate {m n : ℕ}
    (f : Fin n → MvPolynomial (Fin m) F)
    (hc : ∃ r : Fin n → MvPolynomial (Fin m) F, ∑ i, r i * f i = 1)
    (hw : ∃ (p : Polynomial F) (g : Fin m → Polynomial F),
      p.Monic ∧ 1 ≤ p.natDegree ∧ ∀ i, p ∣ MvPolynomial.aeval g (f i)) : False := by
  have hno := (exists_certificate_iff_no_common_zero f).mp hc
  obtain ⟨p, g, hmonic, hdeg, hdiv⟩ := hw
  exact hno (common_zero_of_candidate f p hmonic hdeg g hdiv)

/-- Rabin Lemma 5 (`rabin.tex`:336-351), list-input certificate form:
list coefficients solve the Bezout equation exactly when the listed
polynomials have no common zero in the algebraic closure. -/
theorem exists_certificate_list_iff {m : ℕ} (fs : List (MvPolynomial (Fin m) F)) :
    (∃ rs : List (MvPolynomial (Fin m) F), rs.length = fs.length ∧
        (List.zipWith (· * ·) rs fs).sum = 1) ↔
      ¬ ∃ ξ : Fin m → AlgebraicClosure F, ∀ g ∈ fs, MvPolynomial.aeval ξ g = 0 := by
  let f : Fin fs.length → MvPolynomial (Fin m) F := fun i => fs[i]
  rw [← common_zero_get_iff_common_zero_mem fs]
  constructor
  · rintro ⟨rs, hrs, hsum⟩ hξ
    have hsum' : (∑ i : Fin fs.length, rs[i.val]'(by rw [hrs]; exact i.isLt) * f i) = 1 := by
      rw [← hsum]
      exact (zipWith_mul_sum_eq_finset_sum_get rs fs hrs).symm
    exact (exists_certificate_iff_no_common_zero f).mp
      ⟨fun i => rs[i.val]'(by rw [hrs]; exact i.isLt), hsum'⟩
      hξ
  · intro hno
    obtain ⟨r, hr⟩ := (exists_certificate_iff_no_common_zero f).mpr hno
    refine ⟨List.ofFn r, by simp, ?_⟩
    rw [zipWith_mul_sum_eq_finset_sum_get (List.ofFn r) fs (by simp)]
    simpa [f] using hr

end Semicontinuity
