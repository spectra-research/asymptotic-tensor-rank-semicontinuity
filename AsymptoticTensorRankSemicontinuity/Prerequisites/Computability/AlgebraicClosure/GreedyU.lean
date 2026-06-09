/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.AlgebraicClosure.GreedyIdeal

/-!
# Rabin's greedy regressive ideal `U`

Rabin's Theorem 7 (Rabin 1960, `rabin.tex`:388-394) defines a set `U ⊆ R = F[x₁,x₂,…]`
by a regressive condition: for each code `j`, `r_j ∈ U` iff no Bézout certificate
`1 = ∑ rᵢ·(accepted-before-j) + r·r_j + ∑ rⱼ·g⁽ᵏ⁾` exists, where the `g⁽ᵏ⁾` range over
a prefix of the Vieta system `Γ₁`.

This file defines the greedy recursion as a Boolean table and proves the
characterization lemmas the maximality argument consumes.  Following the audited
design, `acceptU` carries a **canonical-code guard** `canonicalCode j` (an addition
to Rabin's text, audit-approved): it forces every accepted code `j` to satisfy
`encode (rCode j) = j`, so that the polynomials collected in `acceptedList` are
genuinely members of `U` (this is what makes `acceptedList ⊆ U`, the load-bearing
step of ideal-closedness, true).

Decidability of `1 ∈ Ideal.span …` is taken classically here; the *computability*
of `acceptU` (Rabin's "`i_R(U)` is recursive") is a separate development.
-/

universe u

namespace Semicontinuity
namespace GreedyIdeal

variable {F : Type u} [Field F] [Primcodable F] [ComputableField F]

/-! ## The enumeration of `R` and the canonical-code guard -/

/-- The `j`-th polynomial of `R = F[x₁,x₂,…]` under the canonical coding
(`MvPolynomialNat`); junk codes map to `0`. -/
noncomputable def rCode (j : ℕ) : MvPolynomial ℕ F :=
  (Encodable.decode (α := MvPolynomial ℕ F) j).getD 0

@[simp] lemma rCode_encode (r : MvPolynomial ℕ F) :
    rCode (F := F) (Encodable.encode r) = r := by
  unfold rCode
  rw [Encodable.encodek]
  rfl

/-- A code `j` is canonical when it is the canonical code of `rCode j`. -/
noncomputable def canonicalCode (j : ℕ) : Bool :=
  decide (Encodable.encode (rCode (F := F) j) = j)

@[simp] lemma canonicalCode_encode (r : MvPolynomial ℕ F) :
    canonicalCode (F := F) (Encodable.encode r) = true := by
  unfold canonicalCode
  rw [rCode_encode]
  exact decide_eq_true rfl

lemma encode_rCode_of_canonicalCode {j : ℕ} (h : canonicalCode (F := F) j = true) :
    Encodable.encode (rCode (F := F) j) = j := of_decide_eq_true h

/-! ## The greedy recursion -/

/-- A finite variable bound for a list of polynomials. -/
noncomputable def levelMaxList (L : List (MvPolynomial ℕ F)) : ℕ :=
  (L.map (MvPolynomialNat.level (F := F))).foldr max 0

omit [Primcodable F] [ComputableField F] in
lemma level_le_levelMaxList {L : List (MvPolynomial ℕ F)} {g : MvPolynomial ℕ F}
    (hg : g ∈ L) : MvPolynomialNat.level (F := F) g ≤ levelMaxList (F := F) L := by
  unfold levelMaxList
  induction L with
  | nil => simp at hg
  | cons a t ih =>
      rcases List.mem_cons.mp hg with rfl | hgt
      · simp only [List.map_cons, List.foldr_cons]
        exact le_max_left _ _
      · simp only [List.map_cons, List.foldr_cons]
        exact le_trans (ih hgt) (le_max_right _ _)

/-- The accepted polynomials below `j`, read off a Boolean table. -/
noncomputable def acceptedListFromTable (j : ℕ) (table : List Bool) :
    List (MvPolynomial ℕ F) :=
  (List.range j).filterMap fun s =>
    if table.getD s false then some (rCode (F := F) s) else none

/-- Rabin's `k(j)`: a block count large enough that all later `Γ₁` blocks use
variables fresh for the head test set.  Coarse choice `levelMax + 1`. -/
noncomputable def kBound (head : List (MvPolynomial ℕ F)) : ℕ :=
  levelMaxList (F := F) head + 1

/-- The stage-`j` test set: accepted-before, then `r_j`, then a `Γ₁` prefix. -/
noncomputable def testSet (j : ℕ) (table : List Bool) : List (MvPolynomial ℕ F) :=
  let head := acceptedListFromTable (F := F) j table ++ [rCode (F := F) j]
  head ++ gamma1Flat F (kBound (F := F) head)

open Classical in
/-- A list of polynomials does not generate the unit ideal. -/
noncomputable def properTest (L : List (MvPolynomial ℕ F)) : Bool :=
  decide (¬ (1 : MvPolynomial ℕ F) ∈ Ideal.span {g | g ∈ L})

/-- The stage step: canonical code AND the test set is proper. -/
noncomputable def acceptStep (j : ℕ) (table : List Bool) : Bool :=
  canonicalCode (F := F) j && properTest (F := F) (testSet (F := F) j table)

/-- The Boolean table `[acceptU 0, …, acceptU (n-1)]`. -/
noncomputable def acceptTable : ℕ → List Bool
  | 0 => []
  | n + 1 => acceptTable n ++ [acceptStep (F := F) n (acceptTable n)]

/-- `r_j ∈ U` (as a Boolean of the code `j`). -/
noncomputable def acceptU (j : ℕ) : Bool :=
  acceptStep (F := F) j (acceptTable (F := F) j)

/-- The accepted polynomials below `j`. -/
noncomputable def acceptedList (j : ℕ) : List (MvPolynomial ℕ F) :=
  acceptedListFromTable (F := F) j (acceptTable (F := F) j)

/-! ## Unfolding lemmas: the table equals `acceptU` -/

lemma acceptTable_length (n : ℕ) : (acceptTable (F := F) n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [acceptTable, ih]

lemma acceptTable_succ (n : ℕ) :
    acceptTable (F := F) (n + 1) =
      acceptTable (F := F) n ++ [acceptU (F := F) n] := rfl

lemma acceptTable_getD {n s : ℕ} (h : s < n) :
    (acceptTable (F := F) n).getD s false = acceptU (F := F) s := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero s)
  | succ n ih =>
      rw [acceptTable_succ]
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | heq
      · rw [List.getD_append _ _ _ _ (by rw [acceptTable_length]; exact hlt)]
        exact ih hlt
      · subst heq
        rw [List.getD_append_right _ _ _ _ (by rw [acceptTable_length])]
        rw [acceptTable_length]
        simp

lemma acceptedList_eq (j : ℕ) :
    acceptedList (F := F) j =
      (List.range j).filterMap fun s =>
        if acceptU (F := F) s then some (rCode (F := F) s) else none := by
  unfold acceptedList acceptedListFromTable
  apply List.filterMap_congr
  intro s hs
  have hsj : s < j := List.mem_range.mp hs
  rw [acceptTable_getD hsj]

lemma acceptU_eq (j : ℕ) :
    acceptU (F := F) j =
      (canonicalCode (F := F) j &&
        properTest (F := F)
          (let head := acceptedList (F := F) j ++ [rCode (F := F) j]
           head ++ gamma1Flat F (kBound (F := F) head))) := by
  rfl

/-! ## `U` and the canonical-guard characterization -/

/-- Membership in Rabin's `U`, as a predicate on polynomials. -/
noncomputable def accepted (r : MvPolynomial ℕ F) : Prop :=
  acceptU (F := F) (Encodable.encode r) = true

/-- Rabin's ideal `U`, as a set of polynomials. -/
noncomputable def Uset : Set (MvPolynomial ℕ F) := {r | accepted (F := F) r}

lemma acceptU_imp_canonical {j : ℕ} (h : acceptU (F := F) j = true) :
    canonicalCode (F := F) j = true := by
  unfold acceptU acceptStep at h
  exact (Bool.and_eq_true _ _).mp h |>.1

/-- The key consequence of the canonical-code guard: every polynomial collected
in `acceptedList` is genuinely a member of `U`. -/
lemma mem_acceptedList_imp_accepted {j : ℕ} {r : MvPolynomial ℕ F}
    (h : r ∈ acceptedList (F := F) j) : accepted (F := F) r := by
  rw [acceptedList_eq] at h
  rw [List.mem_filterMap] at h
  obtain ⟨s, _hs, hopt⟩ := h
  by_cases hUs : acceptU (F := F) s
  · rw [if_pos hUs] at hopt
    have hrs : rCode (F := F) s = r := Option.some.inj hopt
    have hcanon : canonicalCode (F := F) s = true := acceptU_imp_canonical hUs
    have hcode : Encodable.encode (rCode (F := F) s) = s :=
      encode_rCode_of_canonicalCode hcanon
    unfold accepted
    rw [← hrs, hcode]
    exact hUs
  · rw [if_neg hUs] at hopt
    exact absurd hopt (by simp)

lemma acceptedList_subset_Uset (j : ℕ) :
    ∀ r ∈ acceptedList (F := F) j, r ∈ Uset (F := F) :=
  fun _ hr => mem_acceptedList_imp_accepted hr

open Classical in
/-- `1 ∉ U`: the unit is never accepted, because its own test set contains `1`. -/
lemma one_not_accepted : ¬ accepted (F := F) (1 : MvPolynomial ℕ F) := by
  unfold accepted
  rw [acceptU_eq]
  intro h
  have hand := (Bool.and_eq_true _ _).mp h
  have hproper := hand.2
  unfold properTest at hproper
  have hmem : (1 : MvPolynomial ℕ F) ∈
      (let head := acceptedList (F := F) (Encodable.encode (1 : MvPolynomial ℕ F)) ++
        [rCode (F := F) (Encodable.encode (1 : MvPolynomial ℕ F))]
       head ++ gamma1Flat F (kBound (F := F) head)) := by
    refine List.mem_append.mpr (Or.inl ?_)
    refine List.mem_append.mpr (Or.inr ?_)
    rw [rCode_encode]
    exact List.mem_singleton.mpr rfl
  have : (1 : MvPolynomial ℕ F) ∈ Ideal.span {g | g ∈
      (let head := acceptedList (F := F) (Encodable.encode (1 : MvPolynomial ℕ F)) ++
        [rCode (F := F) (Encodable.encode (1 : MvPolynomial ℕ F))]
       head ++ gamma1Flat F (kBound (F := F) head))} :=
    Ideal.subset_span hmem
  exact (of_decide_eq_true hproper) this

end GreedyIdeal
end Semicontinuity
