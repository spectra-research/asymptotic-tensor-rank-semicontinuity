/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.AlgebraicClosure.GreedyU
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.AlgebraicClosure.FreshVars

/-!
# Properness of Rabin's greedy ideal `U`

The stage invariant (Rabin's "the reader can verify", `rabin.tex`:394-400): for
every `j` and every `Γ₁`-prefix length `K`, the list `acceptedList j ++ gamma1Flat
F K` has a common zero in `F̄`.  Base case = `Γ₁`-consistency; step = the
fresh-variables reduction.  Compactness then gives **global properness**:
`1 ∉ Ideal.span (U ∪ Γ₁)`, the load-bearing fact for ideal-closedness and
maximality of `U`.
-/

universe u

namespace Semicontinuity
namespace GreedyIdeal

variable {F : Type u} [Field F] [Primcodable F] [ComputableField F]

/-! ## `hasCommonZero` bridges and congruence -/

omit [Primcodable F] [ComputableField F] in
/-- A list has a common zero iff it does not generate the unit ideal. -/
theorem hasCommonZero_iff_one_not_mem_span (L : List (MvPolynomial ℕ F)) :
    hasCommonZero (F := F) L ↔ (1 : MvPolynomial ℕ F) ∉ Ideal.span {g | g ∈ L} := by
  rw [one_mem_span_iff_list_certificate (fs := L),
    one_mem_span_nat_iff_not_hasCommonZero (F := F) L]
  tauto

omit [Primcodable F] [ComputableField F] in
/-- `hasCommonZero` depends only on the set of elements. -/
theorem hasCommonZero_congr {L L' : List (MvPolynomial ℕ F)}
    (h : ∀ g, g ∈ L ↔ g ∈ L') : hasCommonZero (F := F) L ↔ hasCommonZero (F := F) L' :=
  ⟨hasCommonZero_mono (F := F) (fun g hg => (h g).2 hg),
   hasCommonZero_mono (F := F) (fun g hg => (h g).1 hg)⟩

omit [Primcodable F] [ComputableField F] in
/-- The proper-test Boolean is `true` exactly when the list has a common zero. -/
theorem properTest_iff_hasCommonZero (L : List (MvPolynomial ℕ F)) :
    properTest (F := F) L = true ↔ hasCommonZero (F := F) L := by
  classical
  unfold properTest
  rw [decide_eq_true_iff, ← hasCommonZero_iff_one_not_mem_span]

/-! ## The stage step in `hasCommonZero` form -/

/-- The head list of stage `j`: accepted-before, then `r_j`. -/
noncomputable def headList (j : ℕ) : List (MvPolynomial ℕ F) :=
  acceptedList (F := F) j ++ [rCode (F := F) j]

/-- The stage-`j` test set in `acceptedList` form. -/
noncomputable def stageTest (j : ℕ) : List (MvPolynomial ℕ F) :=
  headList (F := F) j ++ gamma1Flat F (kBound (F := F) (headList (F := F) j))

theorem acceptU_iff (j : ℕ) :
    acceptU (F := F) j = true ↔
      canonicalCode (F := F) j = true ∧ hasCommonZero (F := F) (stageTest (F := F) j) := by
  rw [acceptU_eq, Bool.and_eq_true, properTest_iff_hasCommonZero]
  rfl

/-! ## Structural lemmas -/

theorem acceptedList_zero : acceptedList (F := F) 0 = [] := by
  rw [acceptedList_eq]; rfl

theorem acceptedList_succ (j : ℕ) :
    acceptedList (F := F) (j + 1) =
      acceptedList (F := F) j ++ (if acceptU (F := F) j then [rCode (F := F) j] else []) := by
  rw [acceptedList_eq, acceptedList_eq, List.range_succ, List.filterMap_append]
  congr 1
  simp only [List.filterMap_cons, List.filterMap_nil]
  by_cases h : acceptU (F := F) j <;> simp [h]

omit [ComputableField F] in
theorem mem_gamma1Flat_iff (K : ℕ) (g : MvPolynomial ℕ F) :
    g ∈ gamma1Flat F K ↔ ∃ j, j < K ∧ g ∈ vietaEqs F j := by
  rw [gamma1Flat, List.mem_flatten]
  constructor
  · rintro ⟨l, hl, hgl⟩
    rw [List.mem_map] at hl
    rcases hl with ⟨j, hj, rfl⟩
    exact ⟨j, List.mem_range.mp hj, hgl⟩
  · rintro ⟨j, hj, hgj⟩
    exact ⟨vietaEqs F j, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩, hgj⟩

omit [ComputableField F] in
theorem mem_gamma1TailFlat_iff (a K : ℕ) (g : MvPolynomial ℕ F) :
    g ∈ gamma1TailFlat F a K ↔ ∃ j, (j < K ∧ a ≤ j) ∧ g ∈ vietaEqs F j := by
  rw [gamma1TailFlat, List.mem_flatten]
  constructor
  · rintro ⟨l, hl, hgl⟩
    rw [List.mem_map] at hl
    rcases hl with ⟨j, hj, rfl⟩
    rw [List.mem_filter, List.mem_range] at hj
    exact ⟨j, ⟨hj.1, of_decide_eq_true hj.2⟩, hgl⟩
  · rintro ⟨j, ⟨hjK, haj⟩, hgj⟩
    refine ⟨vietaEqs F j, List.mem_map.mpr ⟨j, ?_, rfl⟩, hgj⟩
    rw [List.mem_filter, List.mem_range]
    exact ⟨hjK, decide_eq_true haj⟩

omit [ComputableField F] in
theorem gamma1Flat_subset {K K' : ℕ} (h : K ≤ K') :
    gamma1Flat F K ⊆ gamma1Flat F K' := by
  intro g hg
  rw [mem_gamma1Flat_iff] at hg ⊢
  rcases hg with ⟨j, hj, hgj⟩
  exact ⟨j, lt_of_lt_of_le hj h, hgj⟩

omit [ComputableField F] in
/-- The element set of `gamma1Flat F K'` splits into the prefix and the tail. -/
theorem mem_gamma1Flat_split {K K' : ℕ} (h : K ≤ K') (g : MvPolynomial ℕ F) :
    g ∈ gamma1Flat F K' ↔ g ∈ gamma1Flat F K ∨ g ∈ gamma1TailFlat F K K' := by
  rw [mem_gamma1Flat_iff, mem_gamma1Flat_iff, mem_gamma1TailFlat_iff]
  constructor
  · rintro ⟨j, hjK', hgj⟩
    rcases lt_or_ge j K with hjK | hKj
    · exact Or.inl ⟨j, hjK, hgj⟩
    · exact Or.inr ⟨j, ⟨hjK', hKj⟩, hgj⟩
  · rintro (⟨j, hj, hgj⟩ | ⟨j, ⟨hjK', _⟩, hgj⟩)
    · exact ⟨j, lt_of_lt_of_le hj h, hgj⟩
    · exact ⟨j, hjK', hgj⟩

omit [ComputableField F] in
/-- `blockOffset` dominates its index (each block has positive degree). -/
theorem le_blockOffset (K : ℕ) : K ≤ blockOffset F K :=
  (blockOffset_strictMono (F := F)).le_apply

/-- Variables of the stage-`j` head list are below its `kBound`. -/
theorem headList_vars_lt (j : ℕ) :
    ∀ g ∈ headList (F := F) j, ∀ i ∈ g.vars,
      i < kBound (F := F) (headList (F := F) j) := by
  intro g hg i hi
  have h1 : i < MvPolynomialNat.level (F := F) g := MvPolynomialNat.mem_vars_lt_level hi
  have h2 : MvPolynomialNat.level (F := F) g ≤ levelMaxList (F := F) (headList (F := F) j) :=
    level_le_levelMaxList (F := F) hg
  unfold kBound
  omega

/-! ## The stage invariant -/

/-- Rabin's reader-verify (`rabin.tex`:394-400): every stage list, together with
any `Γ₁` prefix, has a common zero in `F̄`. -/
theorem acceptedStageConsistent (j : ℕ) :
    ∀ K, hasCommonZero (F := F) (acceptedList (F := F) j ++ gamma1Flat F K) := by
  induction j with
  | zero =>
      intro K
      rw [acceptedList_zero, List.nil_append]
      exact gamma1_consistent (F := F) K
  | succ j ih =>
      intro K
      rw [acceptedList_succ]
      by_cases hU : acceptU (F := F) j = true
      · rw [if_pos hU]
        have hgoal_eq : (acceptedList (F := F) j ++ [rCode (F := F) j]) ++ gamma1Flat F K
            = headList (F := F) j ++ gamma1Flat F K := rfl
        rw [hgoal_eq]
        set kb := kBound (F := F) (headList (F := F) j) with hkb
        have hstage : hasCommonZero (F := F) (headList (F := F) j ++ gamma1Flat F kb) :=
          ((acceptU_iff (F := F) j).mp hU).2
        by_cases hKkb : K ≤ kb
        · refine hasCommonZero_mono (F := F) ?_ hstage
          intro g hg
          rw [List.mem_append] at hg ⊢
          rcases hg with hgh | hgK
          · exact Or.inl hgh
          · exact Or.inr (gamma1Flat_subset (F := F) hKkb hgK)
        · have hkbK' : kb ≤ K := le_of_lt (not_le.mp hKkb)
          set S := headList (F := F) j ++ gamma1Flat F kb with hS
          set T := gamma1TailFlat F kb K with hT
          have hSvars : ∀ g ∈ S, (g.vars : Set ℕ) ⊆ {n | n < blockOffset F kb} := by
            intro g hg i hi
            simp only [Set.mem_setOf_eq, Finset.mem_coe] at hi ⊢
            rw [hS, List.mem_append] at hg
            rcases hg with hgh | hgK
            · exact lt_of_lt_of_le (headList_vars_lt (F := F) j g hgh i hi)
                (le_blockOffset (F := F) kb)
            · exact gamma1_vars_subset (F := F) kb g hgK hi
          have hTvars : ∀ g ∈ T, (g.vars : Set ℕ) ⊆ {n | blockOffset F kb ≤ n} :=
            fun g hg => gamma1_tail_vars_ge (F := F) kb K g hg
          have hAB : Disjoint {n : ℕ | n < blockOffset F kb}
              {n : ℕ | blockOffset F kb ≤ n} := by
            rw [Set.disjoint_left]
            intro n hn hn'
            simp only [Set.mem_setOf_eq] at hn hn'
            omega
          have hTcons : hasCommonZero (F := F) T := by
            refine gamma1_sublist_consistent (F := F) (K := K) ?_
            intro g hg
            rw [hT, mem_gamma1TailFlat_iff] at hg
            rcases hg with ⟨j', ⟨hj'K, _⟩, hgj'⟩
            rw [mem_gamma1Flat_iff]
            exact ⟨j', hj'K, hgj'⟩
          have hST : hasCommonZero (F := F) (S ++ T) :=
            hasCommonZero_append_of_varsDisjoint (F := F) hSvars hTvars hAB hstage hTcons
          refine (hasCommonZero_congr (F := F) ?_).mpr hST
          intro g
          rw [List.mem_append, List.mem_append, hS, hT, List.mem_append,
            mem_gamma1Flat_split (F := F) hkbK' g]
          tauto
      · rw [if_neg hU, List.append_nil]
        exact ih K

/-! ## Global properness -/

/-- An accepted polynomial appears in every sufficiently long `acceptedList`. -/
theorem mem_acceptedList_of_accepted {g : MvPolynomial ℕ F} (h : accepted (F := F) g)
    {J : ℕ} (hJ : Encodable.encode g < J) : g ∈ acceptedList (F := F) J := by
  rw [acceptedList_eq, List.mem_filterMap]
  refine ⟨Encodable.encode g, List.mem_range.mpr hJ, ?_⟩
  have hg : acceptU (F := F) (Encodable.encode g) = true := h
  rw [rCode_encode, hg]
  rfl

theorem acceptedList_mono {J J' : ℕ} (h : J ≤ J') :
    acceptedList (F := F) J ⊆ acceptedList (F := F) J' := by
  intro g hg
  rw [acceptedList_eq, List.mem_filterMap] at hg ⊢
  rcases hg with ⟨s, hs, hopt⟩
  exact ⟨s, List.mem_range.mpr (lt_of_lt_of_le (List.mem_range.mp hs) h), hopt⟩

/-- Any finite list of accepted/`Γ₁` polynomials sits in a single stage list. -/
theorem exists_stage_bound (L : List (MvPolynomial ℕ F))
    (h : ∀ g ∈ L, accepted (F := F) g ∨ ∃ K, g ∈ gamma1Flat F K) :
    ∃ J K, L ⊆ acceptedList (F := F) J ++ gamma1Flat F K := by
  induction L with
  | nil => exact ⟨0, 0, List.nil_subset _⟩
  | cons a t ih =>
      obtain ⟨J, K, hJK⟩ := ih (fun g hg => h g (List.mem_cons_of_mem a hg))
      rcases h a (List.mem_cons_self) with ha | ⟨Ka, hKa⟩
      · refine ⟨max J (Encodable.encode a + 1), K, ?_⟩
        intro g hg
        rcases List.mem_cons.mp hg with rfl | hgt
        · exact List.mem_append_left _
            (mem_acceptedList_of_accepted (F := F) ha (by omega))
        · have := hJK hgt
          rw [List.mem_append] at this ⊢
          rcases this with hga | hgg
          · exact Or.inl (acceptedList_mono (F := F) (le_max_left _ _) hga)
          · exact Or.inr hgg
      · refine ⟨J, max K Ka, ?_⟩
        intro g hg
        rcases List.mem_cons.mp hg with rfl | hgt
        · exact List.mem_append_right _ (gamma1Flat_subset (F := F) (le_max_right _ _) hKa)
        · have := hJK hgt
          rw [List.mem_append] at this ⊢
          rcases this with hga | hgg
          · exact Or.inl hga
          · exact Or.inr (gamma1Flat_subset (F := F) (le_max_left _ _) hgg)

/-- A list of accepted/`Γ₁` polynomials has a common zero (hence is proper). -/
theorem stage_proper_list (L : List (MvPolynomial ℕ F))
    (h : ∀ g ∈ L, accepted (F := F) g ∨ ∃ K, g ∈ gamma1Flat F K) :
    hasCommonZero (F := F) L := by
  obtain ⟨J, K, hsub⟩ := exists_stage_bound (F := F) L h
  exact hasCommonZero_mono (F := F) hsub (acceptedStageConsistent (F := F) J K)

/-- The set of all `Γ₁` polynomials. -/
noncomputable def Gamma1Set : Set (MvPolynomial ℕ F) := {g | ∃ K, g ∈ gamma1Flat F K}

/-- **Global properness** (Rabin `rabin.tex`:394-400): the unit ideal is not
generated by `U` together with `Γ₁`.  This is the load-bearing fact for
ideal-closedness and maximality of `U`. -/
theorem one_not_mem_span_Uset_gamma1 :
    (1 : MvPolynomial ℕ F) ∉ Ideal.span (Uset (F := F) ∪ Gamma1Set (F := F)) := by
  intro hmem
  obtain ⟨T, hTsub, hT1⟩ := Submodule.mem_span_finite_of_mem_span hmem
  have hset : (T : Set (MvPolynomial ℕ F)) = {g | g ∈ T.toList} := by
    ext g; simp [Finset.mem_toList]
  rw [hset] at hT1
  have hproper : hasCommonZero (F := F) T.toList := by
    refine stage_proper_list (F := F) T.toList ?_
    intro g hg
    have hgset : g ∈ Uset (F := F) ∪ Gamma1Set (F := F) :=
      hTsub (Finset.mem_toList.mp hg)
    rcases hgset with hgU | hgG
    · exact Or.inl hgU
    · exact Or.inr hgG
  exact (hasCommonZero_iff_one_not_mem_span (F := F) T.toList).mp hproper hT1

end GreedyIdeal
end Semicontinuity
