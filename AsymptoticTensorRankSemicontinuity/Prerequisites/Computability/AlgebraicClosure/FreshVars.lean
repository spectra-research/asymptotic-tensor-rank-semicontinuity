/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.IdealTrivialityNat
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.AlgebraicClosure.GreedyIdeal
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Finset.NatAntidiagonal

/-!
# Fresh-variable reductions for the greedy algebraic-closure construction

This file isolates the pure algebra used in Rabin's greedy construction
(`rabin.tex`:402-408): adjoining a separately consistent finite system in
fresh variables does not change whether the current finite system generates
the unit ideal.
-/

noncomputable section

universe u

namespace Semicontinuity

open scoped BigOperators

open MvPolynomial

variable {F : Type u} [Field F]

/-- A finite list of countable-variable polynomials has a common zero over the
algebraic closure of the coefficient field. -/
def hasCommonZero (L : List (MvPolynomial ℕ F)) : Prop :=
  ∃ ξ : ℕ → AlgebraicClosure F, ∀ g ∈ L, MvPolynomial.aeval ξ g = 0

theorem hasCommonZero_mono {L L' : List (MvPolynomial ℕ F)} (h : L ⊆ L') :
    hasCommonZero (F := F) L' → hasCommonZero (F := F) L := by
  rintro ⟨ξ, hξ⟩
  exact ⟨ξ, fun g hg => hξ g (h hg)⟩

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
        (List.zipWith (· * ·) (r :: rs) (f :: fs)).sum =
            r * f + ∑ i : Fin fs.length,
              rs[i.val]'(by rw [htail]; exact i.isLt) * fs[i] := by
          rw [List.zipWith_cons_cons, List.sum_cons,
            zipWith_mul_sum_eq_finset_sum_get rs fs htail]
        _ = ∑ i : Fin (f :: fs).length,
              (r :: rs)[i.val]'(by rw [h]; exact i.isLt) * (f :: fs)[i] := by
          simp [Fin.sum_univ_succ]


private def levelMax (L : List (MvPolynomial ℕ F)) : ℕ :=
  L.foldl (fun n g => max n (MvPolynomialNat.level (F := F) g)) 0

private theorem foldl_levelMax_acc_le (L : List (MvPolynomial ℕ F)) (n : ℕ) :
    n ≤ L.foldl (fun k g => max k (MvPolynomialNat.level (F := F) g)) n := by
  induction L generalizing n with
  | nil => simp
  | cons g L ih =>
      exact le_trans (Nat.le_max_left n (MvPolynomialNat.level (F := F) g)) (ih _)

private theorem level_le_foldl_levelMax_of_mem {L : List (MvPolynomial ℕ F)}
    {g : MvPolynomial ℕ F} (hg : g ∈ L) (n : ℕ) :
    MvPolynomialNat.level (F := F) g ≤
      L.foldl (fun k h => max k (MvPolynomialNat.level (F := F) h)) n := by
  induction L generalizing n with
  | nil => cases hg
  | cons h L ih =>
      rw [List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact le_trans (Nat.le_max_right n (MvPolynomialNat.level (F := F) g))
          (foldl_levelMax_acc_le (F := F) L _)
      · exact ih hg _

private theorem level_le_levelMax_of_mem {L : List (MvPolynomial ℕ F)}
    {g : MvPolynomial ℕ F} (hg : g ∈ L) :
    MvPolynomialNat.level (F := F) g ≤ levelMax (F := F) L :=
  level_le_foldl_levelMax_of_mem (F := F) hg 0

private theorem aeval_inclLevel {A : Type*} [CommSemiring A] [Algebra F A] {m : ℕ}
    (ξ : ℕ → A) (q : MvPolynomial (Fin m) F) :
    MvPolynomial.aeval ξ (MvPolynomialNat.inclLevel (F := F) m q) =
      MvPolynomial.aeval (fun i : Fin m => ξ i) q := by
  rw [MvPolynomialNat.inclLevel, MvPolynomial.aeval_rename]
  rfl

private theorem aeval_restrictLevel_of_level_le {A : Type*} [CommSemiring A] [Algebra F A]
    {m : ℕ} {g : MvPolynomial ℕ F} (ξ : ℕ → A)
    (hg : MvPolynomialNat.level (F := F) g ≤ m) :
    MvPolynomial.aeval (fun i : Fin m => ξ i)
        (MvPolynomialNat.restrictLevel (F := F) m g) =
      MvPolynomial.aeval ξ g := by
  calc
    MvPolynomial.aeval (fun i : Fin m => ξ i)
        (MvPolynomialNat.restrictLevel (F := F) m g) =
        MvPolynomial.aeval ξ
          (MvPolynomialNat.inclLevel (F := F) m
            (MvPolynomialNat.restrictLevel (F := F) m g)) := by
      rw [aeval_inclLevel]
    _ = MvPolynomial.aeval ξ g := by
      rw [MvPolynomialNat.incl_restrictLevel_of_level_le (F := F) hg]

private theorem restricted_common_zero_iff {m : ℕ} (L : List (MvPolynomial ℕ F))
    (hlevel : ∀ g ∈ L, MvPolynomialNat.level (F := F) g ≤ m) :
    (∃ ξ : Fin m → AlgebraicClosure F,
        ∀ g ∈ L.map (MvPolynomialNat.restrictLevel (F := F) m),
          MvPolynomial.aeval ξ g = 0) ↔
      hasCommonZero (F := F) L := by
  constructor
  · rintro ⟨ξ, hξ⟩
    let η : ℕ → AlgebraicClosure F := fun i =>
      if h : i < m then ξ ⟨i, h⟩ else 0
    refine ⟨η, ?_⟩
    intro g hg
    have hη : (fun i : Fin m => η i) = ξ := by
      funext i
      simp [η, i.isLt]
    have hev := aeval_restrictLevel_of_level_le (F := F) (A := AlgebraicClosure F)
      (m := m) (g := g) η (hlevel g hg)
    rw [← hev, hη]
    exact hξ (MvPolynomialNat.restrictLevel (F := F) m g) (List.mem_map.mpr ⟨g, hg, rfl⟩)
  · rintro ⟨ξ, hξ⟩
    refine ⟨fun i : Fin m => ξ i, ?_⟩
    intro g hg
    rw [List.mem_map] at hg
    rcases hg with ⟨p, hp, rfl⟩
    rw [aeval_restrictLevel_of_level_le (F := F) (A := AlgebraicClosure F)
      (m := m) (g := p) ξ (hlevel p hp)]
    exact hξ p hp

/-- Countable-carrier Nullstellensatz, in certificate form. -/
theorem one_mem_span_nat_iff_not_hasCommonZero (L : List (MvPolynomial ℕ F)) :
    (∃ rs : List (MvPolynomial ℕ F), rs.length = L.length ∧
        (List.zipWith (· * ·) rs L).sum = 1) ↔
      ¬ hasCommonZero (F := F) L := by
  let m := levelMax (F := F) L
  have hlevel : ∀ g ∈ L, MvPolynomialNat.level (F := F) g ≤ m :=
    fun g hg => level_le_levelMax_of_mem (F := F) hg
  have hfin := one_mem_span_nat_iff_no_common_zero (F := F) (m := m) L hlevel
  have hzero := restricted_common_zero_iff (F := F) (m := m) L hlevel
  exact hfin.trans (not_congr hzero)

private theorem aeval_congr_vars {A : Type*} [CommSemiring A] [Algebra F A]
    {ξ η : ℕ → A} {g : MvPolynomial ℕ F}
    (h : ∀ i, i ∈ g.vars → ξ i = η i) :
    MvPolynomial.aeval ξ g = MvPolynomial.aeval η g := by
  exact MvPolynomial.eval₂Hom_congr' rfl (fun i hi _ => h i hi) rfl

/-- Common zeroes glue across disjoint variable sets. -/
theorem hasCommonZero_append_of_varsDisjoint
    {S T : List (MvPolynomial ℕ F)} {A B : Set ℕ}
    (hSvars : ∀ g ∈ S, (g.vars : Set ℕ) ⊆ A)
    (hTvars : ∀ g ∈ T, (g.vars : Set ℕ) ⊆ B)
    (hAB : Disjoint A B)
    (hS : hasCommonZero (F := F) S) (hT : hasCommonZero (F := F) T) :
    hasCommonZero (F := F) (S ++ T) := by
  classical
  rcases hS with ⟨ξS, hξS⟩
  rcases hT with ⟨ξT, hξT⟩
  let ξ : ℕ → AlgebraicClosure F := fun n => if n ∈ A then ξS n else ξT n
  refine ⟨ξ, ?_⟩
  intro g hg
  rw [List.mem_append] at hg
  rcases hg with hgS | hgT
  · have hagree : ∀ i, i ∈ g.vars → ξ i = ξS i := by
      intro i hi
      simp [ξ, hSvars g hgS hi]
    rw [aeval_congr_vars (F := F) (ξ := ξ) (η := ξS) (g := g) hagree]
    exact hξS g hgS
  · have hagree : ∀ i, i ∈ g.vars → ξ i = ξT i := by
      intro i hi
      have hiB : i ∈ B := hTvars g hgT hi
      have hiA : i ∉ A := by
        intro hiA
        exact hAB.le_bot ⟨hiA, hiB⟩
      simp [ξ, hiA]
    rw [aeval_congr_vars (F := F) (ξ := ξ) (η := ξT) (g := g) hagree]
    exact hξT g hgT

/-- Adding a consistent system in fresh variables does not change certificate
existence for the unit ideal. -/
theorem freshVar_span_iff
    {S T : List (MvPolynomial ℕ F)} {A B : Set ℕ}
    (hSvars : ∀ g ∈ S, (g.vars : Set ℕ) ⊆ A)
    (hTvars : ∀ g ∈ T, (g.vars : Set ℕ) ⊆ B)
    (hAB : Disjoint A B) (hT : hasCommonZero (F := F) T) :
    (∃ rs : List (MvPolynomial ℕ F), rs.length = (S ++ T).length ∧
        (List.zipWith (· * ·) rs (S ++ T)).sum = 1) ↔
      (∃ rs : List (MvPolynomial ℕ F), rs.length = S.length ∧
        (List.zipWith (· * ·) rs S).sum = 1) := by
  have hzero :
      hasCommonZero (F := F) (S ++ T) ↔ hasCommonZero (F := F) S := by
    constructor
    · exact hasCommonZero_mono (F := F) (fun g hg => List.mem_append_left T hg)
    · intro hS
      exact hasCommonZero_append_of_varsDisjoint (F := F) hSvars hTvars hAB hS hT
  rw [one_mem_span_nat_iff_not_hasCommonZero (F := F) (L := S ++ T),
    one_mem_span_nat_iff_not_hasCommonZero (F := F) (L := S)]
  exact not_congr hzero

/-- Span form of `freshVar_span_iff`. -/
theorem freshVar_one_mem_span_iff
    {S T : List (MvPolynomial ℕ F)} {A B : Set ℕ}
    (hSvars : ∀ g ∈ S, (g.vars : Set ℕ) ⊆ A)
    (hTvars : ∀ g ∈ T, (g.vars : Set ℕ) ⊆ B)
    (hAB : Disjoint A B) (hT : hasCommonZero (F := F) T) :
    (1 : MvPolynomial ℕ F) ∈ Ideal.span {g | g ∈ S ++ T} ↔
      (1 : MvPolynomial ℕ F) ∈ Ideal.span {g | g ∈ S} := by
  rw [one_mem_span_iff_list_certificate (fs := S ++ T),
    one_mem_span_iff_list_certificate (fs := S)]
  exact freshVar_span_iff (F := F) hSvars hTvars hAB hT

namespace GreedyIdeal

variable [Primcodable F]

/-- Any sublist of a consistent Γ₁ prefix is consistent. -/
theorem gamma1_sublist_consistent {L : List (MvPolynomial ℕ F)} {K : ℕ}
    (h : L ⊆ gamma1Flat F K) :
    hasCommonZero (F := F) L := by
  exact hasCommonZero_mono (F := F) h (gamma1_consistent (F := F) K)

/-- Variables in a Γ₁ block are at least the block offset. -/
theorem blockVar_ge_offset (j : ℕ) (i : Fin (blockDeg F j)) :
    blockOffset F j ≤ blockVar F j i :=
  blockOffset_le_blockVar (F := F) j i

/-- Variables in a Γ₁ block are below the next block offset. -/
theorem blockVar_lt_succ_offset (j : ℕ) (i : Fin (blockDeg F j)) :
    blockVar F j i < blockOffset F (j + 1) :=
  blockVar_lt_nextOffset (F := F) j i

omit [Primcodable F] in
private theorem vars_coeff_poly_mul_subset {A : Set ℕ}
    {p q : Polynomial (MvPolynomial ℕ F)} (hp : ∀ n, ((p.coeff n).vars : Set ℕ) ⊆ A)
    (hq : ∀ n, ((q.coeff n).vars : Set ℕ) ⊆ A) (n : ℕ) :
    (((p * q).coeff n).vars : Set ℕ) ⊆ A := by
  classical
  rw [Polynomial.coeff_mul]
  intro x hx
  have hx' := MvPolynomial.vars_sum_subset (Finset.antidiagonal n)
      (fun ij : ℕ × ℕ => p.coeff ij.1 * q.coeff ij.2) hx
  rw [Finset.mem_biUnion] at hx'
  rcases hx' with ⟨ij, _hij, hxij⟩
  have hmul := MvPolynomial.vars_mul (p.coeff ij.1) (q.coeff ij.2) hxij
  rw [Finset.mem_union] at hmul
  exact hmul.elim (fun hx => hp ij.1 hx) (fun hx => hq ij.2 hx)

omit [Primcodable F] in
private theorem vars_coeff_poly_prod_subset {ι : Type*} {A : Set ℕ}
    (s : Finset ι) (f : ι → Polynomial (MvPolynomial ℕ F))
    (hf : ∀ i ∈ s, ∀ n, (((f i).coeff n).vars : Set ℕ) ⊆ A) (n : ℕ) :
    ((((∏ i ∈ s, f i) : Polynomial (MvPolynomial ℕ F)).coeff n).vars : Set ℕ) ⊆ A := by
  classical
  revert n
  induction s using Finset.induction_on with
  | empty =>
    intro n
    have hvars :
        ((((1 : Polynomial (MvPolynomial ℕ F)).coeff n).vars : Set ℕ) = ∅) := by
      by_cases hn : n = 0 <;> simp [Polynomial.coeff_one, hn]
    rw [Finset.prod_empty, hvars]
    intro x hx
    cases hx
  | insert i s his ih =>
    intro n
    rw [Finset.prod_insert his]
    exact vars_coeff_poly_mul_subset
      (A := A)
      (p := f i)
      (q := ∏ x ∈ s, f x)
      (fun n => hf i (Finset.mem_insert_self i s) n)
      (fun n => ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)) n)
      n

omit [Primcodable F] in
private theorem vars_coeff_X_sub_C_X_subset (v : ℕ) (n : ℕ) :
    ((((Polynomial.X : Polynomial (MvPolynomial ℕ F)) -
        Polynomial.C (MvPolynomial.X v)).coeff n).vars : Set ℕ) ⊆ ({v} : Set ℕ) := by
  classical
  intro x hx
  rw [Polynomial.coeff_sub] at hx
  by_cases h0 : n = 0
  · subst n
    simp at hx
    simpa [Set.mem_singleton_iff] using hx
  · by_cases h1 : n = 1
    · subst n
      simp at hx
    · have hX : (Polynomial.X : Polynomial (MvPolynomial ℕ F)).coeff n = 0 :=
        Polynomial.coeff_X_of_ne_one h1
      have hC : (Polynomial.C (MvPolynomial.X v) : Polynomial (MvPolynomial ℕ F)).coeff n = 0 := by
        rw [Polynomial.coeff_C]
        simp [h0]
      simp [hX, hC] at hx

theorem vars_blockProd_coeff_subset (j k : ℕ) :
    ((((blockProd F j).coeff k).vars : Set ℕ) ⊆
      {n | blockOffset F j ≤ n ∧ n < blockOffset F (j + 1)}) := by
  classical
  rw [blockProd]
  refine vars_coeff_poly_prod_subset
    (F := F)
    (A := {n | blockOffset F j ≤ n ∧ n < blockOffset F (j + 1)})
    (s := Finset.univ)
    (f := fun i : Fin (blockDeg F j) =>
      (Polynomial.X : Polynomial (MvPolynomial ℕ F)) -
        Polynomial.C (MvPolynomial.X (blockVar F j i))) ?_ k
  intro i _ n x hx
  have hxv := vars_coeff_X_sub_C_X_subset (F := F) (v := blockVar F j i) n hx
  rw [Set.mem_singleton_iff] at hxv
  subst x
  exact ⟨blockOffset_le_blockVar (F := F) j i, blockVar_lt_nextOffset (F := F) j i⟩

theorem vars_vietaEqs_subset_block (j : ℕ) :
    ∀ g ∈ vietaEqs F j,
      ((g.vars : Set ℕ) ⊆ {n | blockOffset F j ≤ n ∧ n < blockOffset F (j + 1)}) := by
  classical
  intro g hg
  rw [vietaEqs, List.mem_map] at hg
  rcases hg with ⟨k, _hk, rfl⟩
  intro x hx
  have hsub := (MvPolynomial.vars_sub_subset
      (p := (blockProd F j).coeff k)
      (q := MvPolynomial.C ((enumMonic F j).coeff k))) hx
  rw [Finset.mem_union] at hsub
  rcases hsub with hxcoeff | hxC
  · exact vars_blockProd_coeff_subset (F := F) j k hxcoeff
  · simp at hxC

/-- Variables of the first `K` Γ₁ blocks lie below `blockOffset F K`. -/
theorem gamma1_vars_subset (K : ℕ) :
    ∀ g ∈ gamma1Flat F K,
      ((g.vars : Set ℕ) ⊆ {n | n < blockOffset F K}) := by
  classical
  intro g hg x hx
  rw [gamma1Flat, List.mem_flatten] at hg
  rcases hg with ⟨gs, hgs, hg⟩
  rw [List.mem_map] at hgs
  rcases hgs with ⟨j, hjrange, rfl⟩
  rw [List.mem_range] at hjrange
  have hxblock := vars_vietaEqs_subset_block (F := F) j g hg hx
  exact lt_of_lt_of_le hxblock.2
    ((blockOffset_strictMono (F := F)).monotone (Nat.succ_le_of_lt hjrange))

/-- The Γ₁ tail made of blocks `a ≤ j < K`. -/
def gamma1TailFlat (F : Type u) [Field F] [Primcodable F] (a K : ℕ) :
    List (MvPolynomial ℕ F) :=
  ((List.range K).filter fun j => a ≤ j).map (vietaEqs F) |>.flatten

/-- Variables of Γ₁ tail blocks are at least the tail offset. -/
theorem gamma1_tail_vars_ge (a K : ℕ) :
    ∀ g ∈ gamma1TailFlat F a K,
      ((g.vars : Set ℕ) ⊆ {n | blockOffset F a ≤ n}) := by
  classical
  intro g hg x hx
  rw [gamma1TailFlat, List.mem_flatten] at hg
  rcases hg with ⟨gs, hgs, hg⟩
  rw [List.mem_map] at hgs
  rcases hgs with ⟨j, hjfilter, rfl⟩
  rw [List.mem_filter] at hjfilter
  have hxblock := vars_vietaEqs_subset_block (F := F) j g hg hx
  have haj : a ≤ j := of_decide_eq_true hjfilter.2
  exact le_trans ((blockOffset_strictMono (F := F)).monotone haj) hxblock.1

end GreedyIdeal

end Semicontinuity
