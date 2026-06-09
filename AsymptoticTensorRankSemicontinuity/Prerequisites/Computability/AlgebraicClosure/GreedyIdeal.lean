/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.MvPolynomialNatComputable
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits

/-!
# The `Γ₁` Vieta blocks for Rabin's greedy algebraic closure construction

This file formalizes the first, purely algebraic, part of Rabin's Theorem 7
construction (`rabin.tex`:362-386), with the audited Vieta deviation:
instead of Rabin's `n(j)` distinct-root variables and the
`D_n` distinctness gadget, each monic nonconstant polynomial receives a fresh
block of `deg f` variables and the coefficientwise splitting certificate

`∏ᵢ (T - xᵢ) = f`.

The consistency theorem says exactly that every finite prefix of these
certificates has a common zero over the algebraic closure of the base field.
-/

noncomputable section

set_option linter.unnecessarySimpa false

universe u

namespace Semicontinuity
namespace GreedyIdeal

open Polynomial

variable {F : Type u} [Field F] [Primcodable F]

/-! ## Monic nonconstant enumeration -/

/-- A total enumeration of monic positive-degree polynomials. Nonmatching
codes and codes for other polynomials are sent to `X`. -/
def enumMonic (F : Type u) [Field F] [Primcodable F] (j : ℕ) : Polynomial F :=
  by
    classical
    exact
      match Encodable.decode (α := Polynomial F) j with
      | some p => if p.Monic ∧ 1 ≤ p.natDegree then p else Polynomial.X
      | none => Polynomial.X

lemma enumMonic_monic [Nontrivial F] (j : ℕ) :
    (enumMonic F j).Monic := by
  classical
  unfold enumMonic
  cases h : Encodable.decode (α := Polynomial F) j with
  | none =>
      exact Polynomial.monic_X
  | some p =>
      by_cases hp : p.Monic ∧ 1 ≤ p.natDegree
      · simpa [hp] using hp.1
      · simpa [hp] using (Polynomial.monic_X : (Polynomial.X : Polynomial F).Monic)

lemma enumMonic_natDegree_pos [Nontrivial F] (j : ℕ) :
    1 ≤ (enumMonic F j).natDegree := by
  classical
  unfold enumMonic
  cases h : Encodable.decode (α := Polynomial F) j with
  | none =>
      rw [Polynomial.natDegree_X]
  | some p =>
      by_cases hp : p.Monic ∧ 1 ≤ p.natDegree
      · simpa [hp] using hp.2
      · simpa [hp, Polynomial.natDegree_X]

lemma enumMonic_surj (p : Polynomial F) (hm : p.Monic) (hd : 1 ≤ p.natDegree) :
    enumMonic F (Encodable.encode p) = p := by
  classical
  unfold enumMonic
  simp [Encodable.encodek, hm, hd]

private theorem computable_decide_nat_le_nat :
    Computable₂ fun a b : ℕ => decide (a ≤ b) := by
  exact Primrec.nat_le.decide.to_comp

private theorem computable_decide_eq {β : Type*} [Primcodable β] [DecidableEq β] :
    Computable₂ fun a b : β => decide (a = b) := by
  exact Primrec.eq.decide.to_comp

set_option linter.flexible false in
open Classical in
theorem computable_enumMonic [ComputableField F] :
    Computable (enumMonic F) := by
  let Q := Polynomial F
  have hdecode : Computable fun j : ℕ => Encodable.decode (α := Q) j :=
    Computable.decode
  have hlead : Computable fun x : ℕ × Q =>
      decide (x.2.leadingCoeff = (1 : F)) :=
    computable_decide_eq.comp
      (computable_poly_leadingCoeff.comp Computable.snd) (Computable.const 1)
  have hdeg : Computable fun x : ℕ × Q => decide (1 ≤ x.2.natDegree) :=
    computable_decide_nat_le_nat.comp (Computable.const 1)
      (computable_poly_natDegree.comp Computable.snd)
  have htest : Computable fun x : ℕ × Q =>
      decide (x.2.leadingCoeff = (1 : F)) && decide (1 ≤ x.2.natDegree) :=
    Primrec.and.to_comp.comp hlead hdeg
  have hsome : Computable₂ fun (_ : ℕ) (p : Q) =>
      bif decide (p.leadingCoeff = (1 : F)) && decide (1 ≤ p.natDegree)
      then p else Polynomial.X := by
    exact (Computable.cond htest Computable.snd (Computable.const Polynomial.X)).to₂
  exact (Computable.option_casesOn hdecode (Computable.const Polynomial.X) hsome).of_eq
    fun j => by
      unfold enumMonic
      cases h : Encodable.decode (α := Q) j with
      | none =>
          rfl
      | some p =>
          by_cases hlead' : p.leadingCoeff = (1 : F)
          · by_cases hdeg' : 1 ≤ p.natDegree
            · simp [hlead', hdeg', Polynomial.Monic.def]
            · simp [hlead', hdeg', Polynomial.Monic.def]
          · simp [hlead', Polynomial.Monic.def]

/-! ## Fresh block layout -/

def blockDeg (F : Type u) [Field F] [Primcodable F] (j : ℕ) : ℕ :=
  (enumMonic F j).natDegree

def blockOffset (F : Type u) [Field F] [Primcodable F] (j : ℕ) : ℕ :=
  ((List.range j).map (blockDeg F)).sum

def blockVar (F : Type u) [Field F] [Primcodable F] (j : ℕ) (i : Fin (blockDeg F j)) : ℕ :=
  blockOffset F j + i

lemma blockDeg_pos [Nontrivial F] (j : ℕ) :
    1 ≤ blockDeg F j := by
  exact enumMonic_natDegree_pos (F := F) j

@[simp] lemma blockOffset_zero : blockOffset F 0 = 0 := by
  simp [blockOffset]

lemma blockOffset_succ (j : ℕ) :
    blockOffset F (j + 1) = blockOffset F j + blockDeg F j := by
  simp [blockOffset, List.range_succ, List.map_append]

lemma blockOffset_add_le [Nontrivial F] (j : ℕ) :
    blockOffset F j + blockDeg F j ≤ blockOffset F (j + 1) := by
  rw [blockOffset_succ]

lemma blockOffset_strictMono [Nontrivial F] :
    StrictMono (blockOffset F) := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base =>
      rw [blockOffset_succ]
      exact Nat.lt_add_of_pos_right (Nat.succ_le_iff.mp (blockDeg_pos (F := F) a))
  | succ b hle ih =>
      exact lt_trans ih (by
        rw [blockOffset_succ]
        exact Nat.lt_add_of_pos_right (Nat.succ_le_iff.mp (blockDeg_pos (F := F) b)))

lemma blockVar_lt_nextOffset [Nontrivial F] (j : ℕ) (i : Fin (blockDeg F j)) :
    blockVar F j i < blockOffset F (j + 1) := by
  rw [blockVar, blockOffset_succ]
  exact Nat.add_lt_add_left i.2 _

lemma blockOffset_le_blockVar (j : ℕ) (i : Fin (blockDeg F j)) :
    blockOffset F j ≤ blockVar F j i := by
  exact Nat.le_add_right _ _

lemma blockVar_injective [Nontrivial F] :
    Function.Injective
      (fun x : Sigma fun j : ℕ => Fin (blockDeg F j) => blockVar F x.1 x.2) := by
  intro x y hxy
  rcases x with ⟨j, i⟩
  rcases y with ⟨k, l⟩
  rcases Nat.lt_trichotomy j k with hjk | hjk | hkj
  · exfalso
    have hlt : blockVar F j i < blockVar F k l := by
      exact lt_of_lt_of_le (blockVar_lt_nextOffset (F := F) j i)
        (le_trans ((blockOffset_strictMono (F := F)).monotone (Nat.succ_le_of_lt hjk))
          (blockOffset_le_blockVar (F := F) k l))
    have hbad : blockVar F k l < blockVar F k l := by
      simp [hxy] at hlt
    exact (Nat.lt_irrefl (blockVar F k l) hbad)
  · subst k
    have hval : (i : ℕ) = (l : ℕ) := by
      exact Nat.add_left_cancel hxy
    cases Fin.ext hval
    rfl
  · exfalso
    have hlt : blockVar F k l < blockVar F j i := by
      exact lt_of_lt_of_le (blockVar_lt_nextOffset (F := F) k l)
        (le_trans ((blockOffset_strictMono (F := F)).monotone (Nat.succ_le_of_lt hkj))
          (blockOffset_le_blockVar (F := F) j i))
    have hbad : blockVar F j i < blockVar F j i := by
      simp [hxy] at hlt
    exact (Nat.lt_irrefl (blockVar F j i) hbad)

/-! ## Vieta blocks -/

/-- The formal product `∏ᵢ (T - X_{j,i})` attached to block `j`. -/
def blockProd (F : Type u) [Field F] [Primcodable F] (j : ℕ) :
    Polynomial (MvPolynomial ℕ F) :=
  ∏ i : Fin (blockDeg F j),
    (Polynomial.X - Polynomial.C (MvPolynomial.X (blockVar F j i)))

/-- Coefficientwise Vieta equations for block `j`. -/
def vietaEqs (F : Type u) [Field F] [Primcodable F] (j : ℕ) :
    List (MvPolynomial ℕ F) :=
  (List.range (blockDeg F j + 1)).map fun k =>
    (blockProd F j).coeff k - MvPolynomial.C ((enumMonic F j).coeff k)

/-- The first `K` Vieta blocks, flattened as one finite list. -/
def gamma1Flat (F : Type u) [Field F] [Primcodable F] (K : ℕ) :
    List (MvPolynomial ℕ F) :=
  ((List.range K).map (vietaEqs F)).flatten

lemma blockProd_monic [Nontrivial F] (j : ℕ) :
    (blockProd F j).Monic := by
  classical
  simpa [blockProd] using
    Polynomial.monic_prod_X_sub_C
      (fun i : Fin (blockDeg F j) => MvPolynomial.X (blockVar F j i)) Finset.univ

lemma blockProd_natDegree [Nontrivial F] (j : ℕ) :
    (blockProd F j).natDegree = blockDeg F j := by
  classical
  simpa [blockProd] using
    Polynomial.natDegree_finset_prod_X_sub_C_eq_card
      (s := Finset.univ)
      (f := fun i : Fin (blockDeg F j) => MvPolynomial.X (blockVar F j i))

lemma enumMonic_map_C_natDegree [Nontrivial F] (j : ℕ) :
    (Polynomial.map (MvPolynomial.C : F →+* MvPolynomial ℕ F)
      (enumMonic F j)).natDegree = blockDeg F j := by
  rw [(enumMonic_monic (F := F) j).natDegree_map]
  rfl

/-- Coefficient vanishing up to the common degree is equivalent to the Vieta
polynomial identity. -/
lemma blockProd_eq_iff [Nontrivial F] (j : ℕ) :
    blockProd F j =
        (enumMonic F j).map (MvPolynomial.C : F →+* MvPolynomial ℕ F) ↔
      ∀ k ∈ List.range (blockDeg F j + 1),
        (blockProd F j).coeff k - MvPolynomial.C ((enumMonic F j).coeff k) = 0 := by
  classical
  rw [Polynomial.ext_iff_natDegree_le
    (by rw [blockProd_natDegree (F := F) j])
    (by rw [enumMonic_map_C_natDegree (F := F) j])]
  constructor
  · intro h k hk
    rw [List.mem_range] at hk
    have hk' : k ≤ blockDeg F j := Nat.lt_succ_iff.mp hk
    specialize h k hk'
    rw [Polynomial.coeff_map] at h
    exact sub_eq_zero.mpr h
  · intro h k hk
    have hk' : k ∈ List.range (blockDeg F j + 1) := by
      rw [List.mem_range]
      exact Nat.lt_succ_iff.mpr hk
    specialize h k hk'
    rw [Polynomial.coeff_map]
    exact sub_eq_zero.mp h

/-! ## Consistency of finite prefixes -/

/-- Rabin Γ₁ prefix consistency: enumerate the multiset of roots of each mapped
monic polynomial over `AlgebraicClosure F`, assign those roots to the fresh block
variables (`blockVar_injective`), bridge the `Fin d` product to
`Polynomial.Splits.eq_prod_roots_of_monic`, and evaluate each coefficient equation
through `MvPolynomial.aeval`. -/
theorem gamma1_consistent (K : ℕ) :
    ∃ ξ : ℕ → AlgebraicClosure F, ∀ g ∈ gamma1Flat F K,
      MvPolynomial.aeval ξ g = 0 := by
  classical
  let A := AlgebraicClosure F
  have hroot_exists :
      ∀ j : ℕ, ∃ r : Fin (blockDeg F j) → A,
        (∏ i : Fin (blockDeg F j), (Polynomial.X - Polynomial.C (r i))) =
          (enumMonic F j).map (algebraMap F A) := by
    intro j
    let p : Polynomial A := (enumMonic F j).map (algebraMap F A)
    let d := blockDeg F j
    change ∃ r : Fin d → A,
      (∏ i : Fin d, (Polynomial.X - Polynomial.C (r i))) = p
    have hmonic : p.Monic := by
      exact (enumMonic_monic (F := F) j).map (algebraMap F A)
    have hsplits : p.Splits := IsAlgClosed.splits p
    have hdeg : p.natDegree = d := by
      dsimp [p, d, blockDeg]
      rw [(enumMonic_monic (F := F) j).natDegree_map]
    have hcard : p.roots.card = d := by
      exact (splits_iff_card_roots.mp hsplits).trans hdeg
    let l := p.roots.toList
    have hlen : l.length = d := by
      rw [Multiset.length_toList, hcard]
    refine ⟨fun i : Fin d => l[(i.cast hlen.symm).1], ?_⟩
    calc
      (∏ i : Fin d,
          (Polynomial.X - Polynomial.C (l[(i.cast hlen.symm).1]))) =
          ∏ i : Fin l.length, (Polynomial.X - Polynomial.C (l[i.1])) := by
        simpa using
          (Fin.prod_congr'
            (fun i : Fin l.length => (Polynomial.X : Polynomial A) - Polynomial.C (l[i.1]))
            hlen.symm)
      _ =
          (l.map fun a : A => Polynomial.X - Polynomial.C a).prod := by
        simpa using
          (Fin.prod_univ_fun_getElem l
            (fun a : A => (Polynomial.X : Polynomial A) - Polynomial.C a))
      _ = (p.roots.map fun a : A => Polynomial.X - Polynomial.C a).prod := by
        simp [l]
      _ = p := (hsplits.eq_prod_roots_of_monic hmonic).symm
  let rootVec : (j : ℕ) → Fin (blockDeg F j) → A :=
    fun j => Classical.choose (hroot_exists j)
  have hroot_prod :
      ∀ j : ℕ,
        (∏ i : Fin (blockDeg F j),
            (Polynomial.X - Polynomial.C (rootVec j i))) =
          (enumMonic F j).map (algebraMap F A) :=
    fun j => Classical.choose_spec (hroot_exists j)
  let P : ℕ → Prop := fun n =>
    ∃ x : Sigma fun j : ℕ => Fin (blockDeg F j), blockVar F x.1 x.2 = n ∧ x.1 < K
  let ξ : ℕ → A := fun n =>
    if h : P n then
      rootVec h.choose.1 h.choose.2
    else 0
  have xi_blockVar (j : ℕ) (hj : j < K) (i : Fin (blockDeg F j)) :
      ξ (blockVar F j i) = rootVec j i := by
    have hex : P (blockVar F j i) := by
      exact ⟨⟨j, i⟩, rfl, hj⟩
    have hchosen :
        (Exists.choose hex : Sigma fun j : ℕ => Fin (blockDeg F j)) = ⟨j, i⟩ := by
      apply blockVar_injective (F := F)
      exact (Exists.choose_spec hex).1
    change (if h : P (blockVar F j i) then rootVec h.choose.1 h.choose.2 else 0) =
        rootVec j i
    rw [dif_pos hex]
    rw [hchosen]
  let evalHom : MvPolynomial ℕ F →+* A :=
    ((MvPolynomial.aeval (R := F) ξ : MvPolynomial ℕ F →ₐ[F] A) :
      MvPolynomial ℕ F →+* A)
  have hmap_block (j : ℕ) (hj : j < K) :
      (blockProd F j).map evalHom =
        (enumMonic F j).map (algebraMap F A) := by
    calc
      (blockProd F j).map evalHom =
          ∏ i : Fin (blockDeg F j),
            (Polynomial.X - Polynomial.C (ξ (blockVar F j i))) := by
        rw [blockProd, Polynomial.map_prod]
        simp [evalHom]
      _ = ∏ i : Fin (blockDeg F j),
            (Polynomial.X - Polynomial.C (rootVec j i)) := by
        simp [xi_blockVar j hj]
      _ = (enumMonic F j).map (algebraMap F A) := hroot_prod j
  refine ⟨ξ, ?_⟩
  intro g hg
  rw [gamma1Flat, List.mem_flatten] at hg
  rcases hg with ⟨gs, hgs, hmem⟩
  rw [List.mem_map] at hgs
  rcases hgs with ⟨j, hjrange, rfl⟩
  have hj : j < K := by
    simpa using hjrange
  rw [vietaEqs, List.mem_map] at hmem
  rcases hmem with ⟨k, _hkrange, rfl⟩
  change evalHom ((blockProd F j).coeff k -
      MvPolynomial.C ((enumMonic F j).coeff k)) = 0
  rw [map_sub]
  have heval_C :
      evalHom (MvPolynomial.C ((enumMonic F j).coeff k)) =
        algebraMap F A ((enumMonic F j).coeff k) := by
    simp [evalHom]
  rw [heval_C]
  rw [← Polynomial.coeff_map (f := evalHom) (p := blockProd F j) (n := k),
    ← Polynomial.coeff_map (f := algebraMap F A) (p := enumMonic F j) (n := k),
    hmap_block j hj]
  simp

end GreedyIdeal
end Semicontinuity
