/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.ComputableField
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.ListComputable
import Mathlib.Algebra.Polynomial.CoeffList
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Data.List.GetD
import Mathlib.Data.List.DropRight

/-!
# Computable univariate polynomial arithmetic over a computable ring

A polynomial over a computable commutative ring is coded by its little-endian
coefficient list (index `i` holds the coefficient of `X^i`; no trailing
zeros; `[]` codes `0`). On this coding the ring operations, evaluation,
and the coding itself work over computable rings in Rabin's sense
(Rabin 1960, §1.6). The field-specific operations — inverses, division,
polynomial Euclidean division and gcd — are isolated in their own sections.

This is the first ingredient of the computable algebraic closure
(Rabin, Theorem 7); nothing here is specific to that application.

Contents:

* `Polynomial.instPrimcodable` — the coefficient-list coding;
* computability of `+`, `*`, `C`, `X`, `coeff`, `natDegree`,
  `leadingCoeff`, `eval`;
* **Rabin's Lemma 1** (tex:85-100): inverses are computable in a
  computable field (by unbounded search), hence so is `/` and
  polynomial Euclidean division `/ₘ`, `%ₘ`, `EuclideanDomain.gcd`.
-/

universe u v

namespace Semicontinuity

open Polynomial

variable {R : Type u} [CommRing R]

/-! ## The coefficient-list coding -/

section Coding

/-- The little-endian coefficient list of a polynomial: index `i` holds
`P.coeff i`; the length is `degree + 1` (so `0 ↦ []`); no trailing zeros.
This is the reverse of Mathlib's (big-endian) `Polynomial.coeffList`. -/
def polyCoeffs (P : Polynomial R) : List R :=
  (List.range P.degree.succ).map P.coeff

lemma polyCoeffs_eq_coeffList_reverse (P : Polynomial R) :
    polyCoeffs P = P.coeffList.reverse := by
  rw [coeffList, List.map_reverse, List.reverse_reverse]
  rfl

@[simp] lemma polyCoeffs_length (P : Polynomial R) :
    (polyCoeffs P).length = P.degree.succ := by
  simp [polyCoeffs]

@[simp] lemma polyCoeffs_zero : polyCoeffs (0 : Polynomial R) = [] := by
  simp [polyCoeffs]

lemma natDegree_eq_zero_of_polyCoeffs_length_le_one {P : Polynomial R}
    (h : (polyCoeffs P).length ≤ 1) : P.natDegree = 0 := by
  by_cases hP : P = 0
  · subst P
    simp
  · rw [polyCoeffs_length, Polynomial.withBotSucc_degree_eq_natDegree_add_one hP] at h
    omega

lemma polyCoeffs_length_le_one_of_natDegree_eq_zero {P : Polynomial R}
    (h : P.natDegree = 0) : (polyCoeffs P).length ≤ 1 := by
  by_cases hP : P = 0
  · subst P
    simp
  · rw [polyCoeffs_length, Polynomial.withBotSucc_degree_eq_natDegree_add_one hP, h]

/-- Reading the coded coefficient at any index gives the coefficient —
also beyond the list length, where both sides are `0`. -/
lemma polyCoeffs_getD (P : Polynomial R) (i : ℕ) :
    (polyCoeffs P).getD i 0 = P.coeff i := by
  rcases lt_or_ge i (polyCoeffs P).length with h | h
  · rw [List.getD_eq_getElem _ _ h]
    simp [polyCoeffs]
  · rw [List.getD_eq_default _ _ h]
    symm
    apply P.coeff_eq_zero_of_degree_lt
    rw [polyCoeffs_length] at h
    -- `degree.succ ≤ i` gives `degree < i` in `WithBot ℕ`.
    by_cases hP : P = 0
    · subst P
      simp
    · rw [Polynomial.withBotSucc_degree_eq_natDegree_add_one hP] at h
      rw [Polynomial.degree_eq_natDegree hP]
      exact_mod_cast Nat.lt_of_succ_le h

open scoped Classical in
/-- Constants are coded by the empty list exactly when the constant is zero,
and otherwise by the singleton coefficient list. -/
@[simp] lemma polyCoeffs_C (a : R) :
    polyCoeffs (C a : Polynomial R) = if a = 0 then [] else [a] := by
  by_cases ha : a = 0
  · subst a
    simp
  · simp [polyCoeffs, Polynomial.degree_C ha, ha]

/-- Over a nontrivial coefficient ring, `X` is coded by the coefficient list
`[0, 1]`. -/
@[simp] lemma polyCoeffs_X [Nontrivial R] :
    polyCoeffs (X : Polynomial R) = [0, 1] := by
  rw [polyCoeffs, Polynomial.degree_X]
  change [Polynomial.coeff (X : Polynomial R) 0,
      Polynomial.coeff (X : Polynomial R) 1] = [0, 1]
  simp

/-- Rebuild a polynomial from a (not necessarily canonical) little-endian
coefficient list. -/
noncomputable def polyOfList (l : List R) : Polynomial R :=
  ∑ i ∈ Finset.range l.length, C (l.getD i 0) * X ^ i

@[simp] lemma polyOfList_coeff (l : List R) (i : ℕ) :
    (polyOfList l).coeff i = l.getD i 0 := by
  rw [polyOfList, Polynomial.finset_sum_coeff]
  by_cases hi : i < l.length
  · rw [Finset.sum_eq_single i]
    · simp [hi, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    · intro j hj hji
      have hne : i ≠ j := by exact fun h => hji h.symm
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
    · intro hi'
      exact (hi' (Finset.mem_range.mpr hi)).elim
  · rw [List.getD_eq_default]
    · exact Finset.sum_eq_zero fun j hj => by
        have hjlt : j < l.length := Finset.mem_range.mp hj
        have hne : i ≠ j := by
          intro hji
          exact hi (hji.symm ▸ hjlt)
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
    · exact le_of_not_gt hi

@[simp] lemma polyOfList_polyCoeffs (P : Polynomial R) :
    polyOfList (polyCoeffs P) = P := by
  apply Polynomial.ext
  intro i
  rw [polyOfList_coeff, polyCoeffs_getD]

/-- The last entry of the coefficient list is the leading coefficient,
which is nonzero. -/
lemma polyCoeffs_getLast?_ne_zero (P : Polynomial R) :
    (polyCoeffs P).getLast? ≠ some 0 := by
  by_cases hP : P = 0
  · subst P
    simp
  · rw [polyCoeffs_eq_coeffList_reverse, List.getLast?_reverse]
    obtain ⟨ls, hls⟩ := Polynomial.coeffList_eq_cons_leadingCoeff hP
    rw [hls]
    simp [Polynomial.leadingCoeff_eq_zero, hP]

private lemma polyCoeffs_polyOfList_of_getLast?_ne_zero
    (l : List R) (h : l.getLast? ≠ some 0) :
    polyCoeffs (polyOfList l) = l := by
  by_cases hnil : l = []
  · subst l
    simp [polyOfList]
  · have hpos : 0 < l.length := List.length_pos_iff.mpr hnil
    let n := l.length - 1
    have hnlt : n < l.length := by
      dsimp [n]
      omega
    have hlast : l.getD n 0 ≠ 0 := by
      intro hz
      apply h
      rw [List.getLast?_eq_getLast_of_ne_nil hnil, List.getLast_eq_getElem hnil]
      rw [← List.getD_eq_getElem l 0 hnlt, hz]
    have hcoeff : (polyOfList l).coeff n ≠ 0 := by
      simpa using hlast
    have hle : (polyOfList l).natDegree ≤ n := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro m hm
      rw [polyOfList_coeff, List.getD_eq_default]
      dsimp [n] at hm ⊢
      omega
    have hnat : (polyOfList l).natDegree = n :=
      Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle hcoeff
    have hpoly_ne : polyOfList l ≠ 0 := by
      intro hp
      exact hcoeff (by simp [hp])
    have hlen : (polyCoeffs (polyOfList l)).length = l.length := by
      rw [polyCoeffs_length, Polynomial.withBotSucc_degree_eq_natDegree_add_one hpoly_ne, hnat]
      dsimp [n]
      omega
    apply List.ext_getElem hlen
    intro i hi₁ hi₂
    have hgetD :
        (polyCoeffs (polyOfList l)).getD i 0 = l.getD i 0 := by
      rw [polyCoeffs_getD, polyOfList_coeff]
    rw [List.getD_eq_getElem _ _ hi₁, List.getD_eq_getElem _ _ hi₂] at hgetD
    exact hgetD

/-- A polynomial is exactly a little-endian coefficient list with no
trailing zero. -/
noncomputable def polyEquivList :
    Polynomial R ≃ {l : List R // l.getLast? ≠ some 0} where
  toFun P := ⟨polyCoeffs P, polyCoeffs_getLast?_ne_zero P⟩
  invFun l := polyOfList l
  left_inv P := polyOfList_polyCoeffs P
  right_inv l := by
    apply Subtype.ext
    exact polyCoeffs_polyOfList_of_getLast?_ne_zero l.1 l.2

variable [Primcodable R]

private lemma primrecPred_no_trailing_zero :
    PrimrecPred fun l : List R => l.getLast? ≠ some 0 := by
  have hlast : Primrec fun l : List R => l.getLast? :=
    (Primrec.list_head?.comp Primrec.list_reverse).of_eq fun l => by
      rw [List.getLast?_eq_head?_reverse]
  exact PrimrecPred.not (Primrec.eq.comp hlast (Primrec.const (some 0)))

/-- Polynomials over a coded ring are coded by their coefficient lists. -/
noncomputable instance instPrimcodablePolynomial :
    Primcodable (Polynomial R) :=
  haveI : DecidablePred fun l : List R => l.getLast? ≠ some 0 :=
    fun _ => Classical.propDecidable _
  haveI : Primcodable {l : List R // l.getLast? ≠ some 0} :=
    Primcodable.subtype primrecPred_no_trailing_zero
  Primcodable.ofEquiv _ (polyEquivList (R := R))

/-- Under the coefficient-list coding, the zero polynomial is the empty list
and hence has code `0`. -/
@[simp] theorem encode_polynomial_zero :
    Encodable.encode (0 : Polynomial R) = 0 := by
  classical
  unfold instPrimcodablePolynomial Primcodable.ofEquiv Encodable.ofEquiv
    Encodable.ofLeftInverse Encodable.ofLeftInjection Primcodable.subtype
  change Encodable.encode (show List R from []) = 0
  rfl

/-- Reading off the coefficient list is computable (it is the coding). -/
theorem computable_polyCoeffs :
    Computable (polyCoeffs : Polynomial R → List R) :=
  Computable.encode_iff.mp (Computable.encode.of_eq fun _ => rfl)

end Coding

open scoped Classical in
noncomputable def trimZeros : List R → List R
  | [] => []
  | a :: t =>
      let r := trimZeros t
      if r = [] then if a = 0 then [] else [a] else a :: r

private lemma trimZeros_getLast?_ne_zero (l : List R) :
    (trimZeros (R := R) l).getLast? ≠ some 0 := by
  classical
  induction l with
  | nil =>
      simp [trimZeros]
  | cons a t IH =>
      by_cases hr : trimZeros (R := R) t = []
      · by_cases ha : a = 0 <;> simp [trimZeros, hr, ha]
      · cases hrt : trimZeros (R := R) t with
        | nil => exact (hr hrt).elim
        | cons b r =>
            simpa [trimZeros, hrt] using IH

private lemma polyOfList_cons (a : R) (l : List R) :
    polyOfList (a :: l) = C a + X * polyOfList l := by
  apply Polynomial.ext
  intro i
  cases i with
  | zero =>
      simp [Polynomial.coeff_add, Polynomial.coeff_C]
  | succ i =>
      simp [Polynomial.coeff_add, Polynomial.coeff_X_mul]

private lemma polyOfList_trimZeros (l : List R) :
    polyOfList (trimZeros (R := R) l) = polyOfList l := by
  classical
  induction l with
  | nil =>
      simp [trimZeros, polyOfList]
  | cons a t IH =>
      by_cases hr : trimZeros (R := R) t = []
      · by_cases ha : a = 0
        · have hzero : polyOfList t = 0 := by
            rw [← IH, hr]
            simp [polyOfList]
          rw [polyOfList_cons, ha, hzero]
          simp [trimZeros, hr, polyOfList]
        · simp [trimZeros, hr, ha, polyOfList_cons, ← IH]
      · simp [trimZeros, hr, polyOfList_cons, ← IH]

private theorem computable_decide_eq {β : Type*} [Primcodable β] [DecidableEq β] :
    Computable₂ fun a b : β => decide (a = b) := by
  exact Primrec.eq.decide.to_comp

open scoped Classical in
private noncomputable def trimStep (p : R × List R) : List R :=
  if p.2 = [] then if p.1 = 0 then [] else [p.1] else p.1 :: p.2

lemma trimZeros_eq_foldr (l : List R) :
    trimZeros (R := R) l = l.foldr (fun a r => trimStep (R := R) (a, r)) [] := by
  classical
  induction l with
  | nil =>
      simp [trimZeros]
  | cons a t IH =>
      simp only [trimZeros]
      rw [IH]
      rfl

private theorem computable_trimStep [Primcodable R] :
    Computable (trimStep (R := R)) := by
  classical
  unfold trimStep
  have htail : Computable fun p : R × List R => decide (p.2 = ([] : List R)) :=
    computable_decide_eq.comp Computable.snd (Computable.const [])
  have hhead : Computable fun p : R × List R => decide (p.1 = 0) :=
    computable_decide_eq.comp Computable.fst (Computable.const 0)
  have hsingleton : Computable fun p : R × List R => [p.1] :=
    Computable.list_cons.comp Computable.fst (Computable.const [])
  have hcons : Computable fun p : R × List R => p.1 :: p.2 :=
    Computable.list_cons.comp Computable.fst Computable.snd
  exact (Computable.cond htail
    (Computable.cond hhead (Computable.const []) hsingleton) hcons).of_eq fun p => by
      by_cases ht : p.2 = []
      · by_cases hh : p.1 = 0 <;> simp [ht, hh]
      · simp [ht]

theorem computable_trimZeros [Primcodable R] :
    Computable (trimZeros (R := R)) := by
  classical
  have hstep : Computable₂ fun (_ : List R) (p : List R × R) =>
      trimStep (R := R) (p.2, p.1) := by
    have hpair : Computable fun x : List R × (List R × R) => (x.2.2, x.2.1) :=
      Computable.pair
        (Computable.snd.comp
          (Computable.snd : Computable (fun x : List R × (List R × R) => x.2)))
        (Computable.fst.comp
          (Computable.snd : Computable (fun x : List R × (List R × R) => x.2)))
    exact (computable_trimStep.comp hpair).to₂
  have hfold : Computable fun l : List R =>
      l.reverse.foldl (fun r a => trimStep (R := R) (a, r)) [] :=
    Computable.list_foldl Computable.list_reverse (Computable.const []) hstep
  exact hfold.of_eq fun l => by
    rw [trimZeros_eq_foldr]
    simp [List.foldl_reverse]

private theorem computable_list_getD {α β : Type*} [Primcodable α] [Primcodable β]
    (d : β) {fl : α → List β} {fn : α → ℕ}
    (hl : Computable fl) (hn : Computable fn) :
    Computable fun a => (fl a).getD (fn a) d := by
  rw [show (fun a => (fl a).getD (fn a) d) =
      (fun a => ((fl a)[fn a]?).getD d) by
    funext a
    simp [List.getD_eq_getElem?_getD]]
  exact Computable.option_getD
    ((@Computable.list_getElem? β _).comp hl hn) (Computable.const d)

def addCoeffs (l₁ l₂ : List R) : List R :=
  (List.range (max l₁.length l₂.length)).map fun i => l₁.getD i 0 + l₂.getD i 0

lemma polyOfList_addCoeffs (P Q : Polynomial R) :
    polyOfList (addCoeffs (polyCoeffs P) (polyCoeffs Q)) = P + Q := by
  apply Polynomial.ext
  intro i
  rw [polyOfList_coeff, Polynomial.coeff_add, ← polyCoeffs_getD P i, ← polyCoeffs_getD Q i]
  by_cases hi : i < max (polyCoeffs P).length (polyCoeffs Q).length
  · rw [List.getD_eq_getElem]
    · simp [addCoeffs]
    · simpa [addCoeffs] using hi
  · have hP : (polyCoeffs P).length ≤ i := le_trans (le_max_left _ _) (le_of_not_gt hi)
    have hQ : (polyCoeffs Q).length ≤ i := le_trans (le_max_right _ _) (le_of_not_gt hi)
    rw [List.getD_eq_default]
    · rw [List.getD_eq_default _ _ hP, List.getD_eq_default _ _ hQ]
      simp
    · simpa [addCoeffs] using le_of_not_gt hi

/-- Coefficients of a sum are obtained by pointwise zero-padded addition,
then canonical trimming. -/
lemma polyCoeffs_add (P Q : Polynomial R) :
    polyCoeffs (P + Q) =
      trimZeros (R := R) (addCoeffs (polyCoeffs P) (polyCoeffs Q)) := by
  rw [← polyOfList_addCoeffs (R := R) P Q]
  rw [← polyOfList_trimZeros (R := R) (addCoeffs (polyCoeffs P) (polyCoeffs Q))]
  exact (polyCoeffs_polyOfList_of_getLast?_ne_zero _
    (trimZeros_getLast?_ne_zero (R := R)
      (addCoeffs (polyCoeffs P) (polyCoeffs Q))))

def mulCoeffs (l₁ l₂ : List R) : List R :=
  (List.range (l₁.length + l₂.length)).map fun k =>
    ((List.range (k + 1)).map fun i => l₁.getD i 0 * l₂.getD (k - i) 0).sum

private lemma list_sum_range_eq_finset_sum {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero =>
      simp
  | succ n IH =>
      rw [List.range_succ, List.map_append, List.sum_append, IH, Finset.sum_range_succ]
      simp [add_comm]

lemma polyOfList_mulCoeffs (P Q : Polynomial R) :
    polyOfList (mulCoeffs (polyCoeffs P) (polyCoeffs Q)) = P * Q := by
  apply Polynomial.ext
  intro k
  rw [polyOfList_coeff, Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => P.coeff i * Q.coeff j) k]
  by_cases hk : k < (polyCoeffs P).length + (polyCoeffs Q).length
  · rw [List.getD_eq_getElem _ _ (by simpa [mulCoeffs] using hk)]
    simp only [mulCoeffs, List.getElem_map, List.getElem_range]
    rw [list_sum_range_eq_finset_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [polyCoeffs_getD, polyCoeffs_getD]
  · rw [List.getD_eq_default]
    · symm
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hiP : i < (polyCoeffs P).length
      · have hQ : (polyCoeffs Q).length ≤ k - i := by
          have : (polyCoeffs P).length + (polyCoeffs Q).length ≤ k := le_of_not_gt hk
          omega
        rw [← polyCoeffs_getD P i, ← polyCoeffs_getD Q (k - i),
          List.getD_eq_default _ _ hQ]
        simp
      · have hPi : P.coeff i = 0 := by
          rw [← polyCoeffs_getD P i, List.getD_eq_default]
          exact le_of_not_gt hiP
        rw [hPi]
        simp
    · simpa [mulCoeffs] using le_of_not_gt hk

/-- Coefficients of a product are obtained by convolution of zero-padded
coefficient lists, then canonical trimming. -/
lemma polyCoeffs_mul (P Q : Polynomial R) :
    polyCoeffs (P * Q) =
      trimZeros (R := R) (mulCoeffs (polyCoeffs P) (polyCoeffs Q)) := by
  rw [← polyOfList_mulCoeffs (R := R) P Q]
  rw [← polyOfList_trimZeros (R := R) (mulCoeffs (polyCoeffs P) (polyCoeffs Q))]
  exact (polyCoeffs_polyOfList_of_getLast?_ne_zero _
    (trimZeros_getLast?_ne_zero (R := R)
      (mulCoeffs (polyCoeffs P) (polyCoeffs Q))))

def evalCoeffs (a : R) (l : List R) : R :=
  l.foldr (fun c acc => c + a * acc) 0

lemma evalCoeffs_polyOfList (a : R) (l : List R) :
    evalCoeffs a l = (polyOfList l).eval a := by
  induction l with
  | nil =>
      simp [evalCoeffs, polyOfList]
  | cons c t IH =>
      change c + a * evalCoeffs a t = (polyOfList (c :: t)).eval a
      rw [polyOfList_cons, Polynomial.eval_add, Polynomial.eval_mul, IH]
      simp

/-- Rebuilding after mapping the canonical coefficient list agrees with
coefficient-wise polynomial map. -/
lemma polyOfList_map_polyCoeffs {S : Type v} [CommRing S]
    (f : R →+* S) (P : Polynomial R) :
    polyOfList ((polyCoeffs P).map f) = P.map f := by
  apply Polynomial.ext
  intro i
  rw [polyOfList_coeff, Polynomial.coeff_map, ← polyCoeffs_getD P i]
  by_cases hi : i < (polyCoeffs P).length
  · rw [List.getD_eq_getElem _ _ (by simpa [List.length_map] using hi)]
    rw [List.getD_eq_getElem _ _ hi]
    simp
  · rw [List.getD_eq_default]
    · rw [List.getD_eq_default _ _ (le_of_not_gt hi)]
      exact (f.map_zero).symm
    · simpa [List.length_map] using le_of_not_gt hi

/-- Horner evaluation of a mapped canonical coefficient list is polynomial
evaluation after coefficient-wise map. -/
lemma evalCoeffs_map {S : Type v} [CommRing S]
    (f : R →+* S) (a : S) (P : Polynomial R) :
    evalCoeffs a ((polyCoeffs P).map f) = (P.map f).eval a := by
  rw [evalCoeffs_polyOfList, polyOfList_map_polyCoeffs]

/-! ## Computable ring operations -/

section Ops

variable [Primcodable R]

/-- Building a polynomial from any coefficient list is computable (trim the
trailing zeros, then the identification is the coding). -/
theorem computable_polyOfList :
    Computable (polyOfList : List R → Polynomial R) := by
  classical
  let search : List R → ℕ → Option (Polynomial R) := fun l n =>
    (Encodable.decode (α := Polynomial R) n).bind fun P =>
      if polyCoeffs P = trimZeros (R := R) l then some P else none
  refine Computable.of_total_sound_search (f := search) ?_ ?_ ?_
  · have hdecode : Computable fun x : List R × ℕ =>
        Encodable.decode (α := Polynomial R) x.2 :=
      Computable.decode.comp Computable.snd
    have hbranch : Computable₂ fun (x : List R × ℕ) (P : Polynomial R) =>
        if polyCoeffs P = trimZeros (R := R) x.1 then some P else none := by
      have hleft : Computable fun y : (List R × ℕ) × Polynomial R => polyCoeffs y.2 :=
        computable_polyCoeffs.comp Computable.snd
      have hright : Computable fun y : (List R × ℕ) × Polynomial R =>
          trimZeros (R := R) y.1.1 :=
        computable_trimZeros.comp (Computable.fst.comp Computable.fst)
      have htest : Computable fun y : (List R × ℕ) × Polynomial R =>
          decide (polyCoeffs y.2 = trimZeros (R := R) y.1.1) :=
        computable_decide_eq.comp hleft hright
      have hsome : Computable fun y : (List R × ℕ) × Polynomial R =>
          some y.2 :=
        Computable.option_some.comp Computable.snd
      exact (Computable.cond htest hsome (Computable.const none)).to₂.of_eq fun x => by
        rcases x with ⟨y, P⟩
        by_cases h : polyCoeffs P = trimZeros (R := R) y.1
        · simp [h]
        · simp [h]
    exact (Computable.option_bind hdecode hbranch).to₂.of_eq fun x => by
      rcases x with ⟨l, n⟩
      rfl
  · intro l n b hb
    rcases hdec : Encodable.decode (α := Polynomial R) n with _ | P
    · simp [search, hdec] at hb
    · by_cases hcoeff : polyCoeffs P = trimZeros (R := R) l
      · have hbP : b = P := by
          simpa [search, hdec, hcoeff] using hb.symm
        subst b
        calc
          P = polyOfList (polyCoeffs P) := (polyOfList_polyCoeffs P).symm
          _ = polyOfList (trimZeros (R := R) l) := by rw [hcoeff]
          _ = polyOfList l := polyOfList_trimZeros l
      · simp [search, hdec, hcoeff] at hb
  · intro l
    refine ⟨Encodable.encode (polyOfList l), polyOfList l, ?_⟩
    have hcoeff : polyCoeffs (polyOfList l) = trimZeros (R := R) l := by
      rw [← polyOfList_trimZeros (R := R) l]
      exact polyCoeffs_polyOfList_of_getLast?_ne_zero _
        (trimZeros_getLast?_ne_zero (R := R) l)
    simp [search, Encodable.encodek, hcoeff]

theorem computable₂_poly_coeff :
    Computable₂ fun (P : Polynomial R) (i : ℕ) => P.coeff i := by
  have h : Computable fun x : Polynomial R × ℕ => (polyCoeffs x.1).getD x.2 0 :=
    (Primrec.list_getD 0).to_comp.comp
      (computable_polyCoeffs.comp Computable.fst) Computable.snd
  exact h.to₂.of_eq fun x => by
    exact polyCoeffs_getD x.1 x.2

theorem computable_poly_natDegree :
    Computable (natDegree : Polynomial R → ℕ) := by
  have h : Computable fun P : Polynomial R => (polyCoeffs P).length - 1 :=
    Primrec.nat_sub.to_comp.comp
      (Computable.list_length.comp computable_polyCoeffs) (Computable.const 1)
  exact h.of_eq fun P => by
    by_cases hP : P = 0
    · subst P
      simp
    · rw [polyCoeffs_length, Polynomial.withBotSucc_degree_eq_natDegree_add_one hP]
      omega

theorem computable_poly_leadingCoeff :
    Computable (leadingCoeff : Polynomial R → R) := by
  have hlast : Computable fun l : List R => l.getLast? :=
    (Primrec.list_head?.to_comp.comp Computable.list_reverse).of_eq fun l => by
      rw [List.getLast?_eq_head?_reverse]
  have h : Computable fun P : Polynomial R => (polyCoeffs P).getLast?.getD 0 :=
    Computable.option_getD (hlast.comp computable_polyCoeffs) (Computable.const 0)
  exact h.of_eq fun P => by
    by_cases hP : P = 0
    · subst P
      simp
    · rw [polyCoeffs_eq_coeffList_reverse, List.getLast?_reverse]
      obtain ⟨ls, hls⟩ := Polynomial.coeffList_eq_cons_leadingCoeff hP
      rw [hls]
      simp

theorem computable_poly_C : Computable (C : R →+* Polynomial R) := by
  have hlist : Computable fun a : R => [a] :=
    Computable.list_cons.comp Computable.id (Computable.const [])
  exact (computable_polyOfList.comp hlist).of_eq fun a => by
    apply Polynomial.ext
    intro i
    cases i <;> simp [polyOfList, Polynomial.coeff_C]

variable [ComputableRing R]

theorem computable₂_poly_add :
    Computable₂ ((· + ·) : Polynomial R → Polynomial R → Polynomial R) := by
  have hlist : Computable fun x : Polynomial R × Polynomial R =>
      addCoeffs (polyCoeffs x.1) (polyCoeffs x.2) := by
    have hlen : Computable fun x : Polynomial R × Polynomial R =>
        max (polyCoeffs x.1).length (polyCoeffs x.2).length :=
      Primrec.nat_max.to_comp.comp
        (Computable.list_length.comp (computable_polyCoeffs.comp Computable.fst))
        (Computable.list_length.comp (computable_polyCoeffs.comp Computable.snd))
    have hterm : Computable₂ fun (x : Polynomial R × Polynomial R) (i : ℕ) =>
        (polyCoeffs x.1).getD i 0 + (polyCoeffs x.2).getD i 0 := by
      have h₁ : Computable fun y : (Polynomial R × Polynomial R) × ℕ =>
          (polyCoeffs y.1.1).getD y.2 0 :=
        computable_list_getD 0
          (computable_polyCoeffs.comp (Computable.fst.comp Computable.fst))
          Computable.snd
      have h₂ : Computable fun y : (Polynomial R × Polynomial R) × ℕ =>
          (polyCoeffs y.1.2).getD y.2 0 :=
        computable_list_getD 0
          (computable_polyCoeffs.comp (Computable.snd.comp Computable.fst))
          Computable.snd
      exact (ComputableRing.computable_add.comp h₁ h₂).to₂
    exact (Computable.list_map (Primrec.list_range.to_comp.comp hlen) hterm).of_eq fun x => by
      rfl
  exact (computable_polyOfList.comp hlist).to₂.of_eq fun x => by
    rcases x with ⟨P, Q⟩
    exact polyOfList_addCoeffs P Q

theorem computable₂_poly_mul :
    Computable₂ ((· * ·) : Polynomial R → Polynomial R → Polynomial R) := by
  have hlist : Computable fun x : Polynomial R × Polynomial R =>
      mulCoeffs (polyCoeffs x.1) (polyCoeffs x.2) := by
    have hlen : Computable fun x : Polynomial R × Polynomial R =>
        (polyCoeffs x.1).length + (polyCoeffs x.2).length :=
      Primrec.nat_add.to_comp.comp
        (Computable.list_length.comp (computable_polyCoeffs.comp Computable.fst))
        (Computable.list_length.comp (computable_polyCoeffs.comp Computable.snd))
    have hterm : Computable₂ fun (x : Polynomial R × Polynomial R) (k : ℕ) =>
        ((List.range (k + 1)).map fun i =>
          (polyCoeffs x.1).getD i 0 * (polyCoeffs x.2).getD (k - i) 0).sum := by
      have hinner : Computable fun y : (Polynomial R × Polynomial R) × ℕ =>
          ((List.range (y.2 + 1)).map fun i =>
            (polyCoeffs y.1.1).getD i 0 * (polyCoeffs y.1.2).getD (y.2 - i) 0).sum := by
        have hN : Computable fun y : (Polynomial R × Polynomial R) × ℕ => y.2 + 1 :=
          Primrec.nat_add.to_comp.comp Computable.snd (Computable.const 1)
        have hmulTerm : Computable₂ fun (y : (Polynomial R × Polynomial R) × ℕ) (i : ℕ) =>
            (polyCoeffs y.1.1).getD i 0 * (polyCoeffs y.1.2).getD (y.2 - i) 0 := by
          have hleft : Computable fun z : ((Polynomial R × Polynomial R) × ℕ) × ℕ =>
              (polyCoeffs z.1.1.1).getD z.2 0 :=
            computable_list_getD 0
              (computable_polyCoeffs.comp
                (Computable.fst.comp (Computable.fst.comp Computable.fst)))
              Computable.snd
          have hidx : Computable fun z : ((Polynomial R × Polynomial R) × ℕ) × ℕ =>
              z.1.2 - z.2 :=
            Primrec.nat_sub.to_comp.comp
              (Computable.snd.comp Computable.fst) Computable.snd
          have hright : Computable fun z : ((Polynomial R × Polynomial R) × ℕ) × ℕ =>
              (polyCoeffs z.1.1.2).getD (z.1.2 - z.2) 0 :=
            computable_list_getD 0
              (computable_polyCoeffs.comp
                (Computable.snd.comp (Computable.fst.comp Computable.fst)))
              hidx
          exact (ComputableRing.computable_mul.comp hleft hright).to₂
        exact Computable.list_sum ComputableRing.computable_add
          (Computable.list_map (Primrec.list_range.to_comp.comp hN) hmulTerm)
      exact hinner.to₂
    exact (Computable.list_map (Primrec.list_range.to_comp.comp hlen) hterm).of_eq fun x => by
      rfl
  exact (computable_polyOfList.comp hlist).to₂.of_eq fun x => by
    rcases x with ⟨P, Q⟩
    exact polyOfList_mulCoeffs P Q

theorem computable₂_poly_eval :
    Computable₂ fun (a : R) (P : Polynomial R) => P.eval a := by
  have h : Computable fun x : R × Polynomial R =>
      (polyCoeffs x.2).reverse.foldl (fun acc c => c + x.1 * acc) 0 := by
    have hstep : Computable₂ fun (x : R × Polynomial R) (p : R × R) =>
        p.2 + x.1 * p.1 := by
      have hmul : Computable fun y : (R × Polynomial R) × (R × R) => y.1.1 * y.2.1 :=
        ComputableRing.computable_mul.comp
          (Computable.fst.comp Computable.fst)
          (Computable.fst.comp Computable.snd)
      exact (ComputableRing.computable_add.comp
        (Computable.snd.comp Computable.snd) hmul).to₂
    exact Computable.list_foldl
      (Computable.list_reverse.comp (computable_polyCoeffs.comp Computable.snd))
      (Computable.const 0) hstep
  exact h.to₂.of_eq fun x => by
    rcases x with ⟨a, P⟩
    change (polyCoeffs P).reverse.foldl (fun acc c => c + a * acc) 0 = P.eval a
    rw [List.foldl_reverse]
    change evalCoeffs a (polyCoeffs P) = P.eval a
    rw [evalCoeffs_polyOfList, polyOfList_polyCoeffs]

/-- Finite list sums in a computable ring are computable.  This is part of the
ring-operation infrastructure implicit in Rabin's admissible indexing
(Rabin 1960, §1.6, tex:264). -/
theorem computable_list_sum :
    Computable fun l : List R => l.sum :=
  Computable.list_sum ComputableRing.computable_add Computable.id

/-- Finite list products in a computable ring are computable.  This is part of
the ring-operation infrastructure implicit in Rabin's admissible indexing
(Rabin 1960, §1.6, tex:264). -/
theorem computable_list_prod :
    Computable fun l : List R => l.prod :=
  Computable.list_prod ComputableRing.computable_mul Computable.id

/-- Natural powers in a computable ring are computable by bounded iteration.
This is part of the ring-operation infrastructure implicit in Rabin's
admissible indexing (Rabin 1960, §1.6, tex:264). -/
theorem computable₂_pow :
    Computable₂ fun (a : R) (k : ℕ) => a ^ k := by
  have hstep : Computable₂ fun (x : R × ℕ) (p : ℕ × R) => x.1 * p.2 := by
    exact (ComputableRing.computable_mul.comp
      (Computable.fst.comp Computable.fst)
      (Computable.snd.comp Computable.snd)).to₂
  have hrec : Computable fun x : R × ℕ =>
      Nat.rec (motive := fun _ => R) 1 (fun _ acc => x.1 * acc) x.2 :=
    Computable.nat_rec Computable.snd (Computable.const 1) hstep
  have hpow : Computable fun x : R × ℕ => x.1 ^ x.2 := hrec.of_eq fun x => by
    rcases x with ⟨a, k⟩
    induction k with
    | zero =>
        simp
    | succ k IH =>
        simp [IH, pow_succ, mul_comm]
  exact hpow.to₂

omit [ComputableRing R] in
/-- Applying a computable ring homomorphism to the coefficients of a univariate
polynomial is computable uniformly in a parameter.  The implementation maps the
little-endian coefficient list and rebuilds via `polyOfList`, so leading
coefficients killed by a non-injective homomorphism are re-canonicalized.  This
is part of the ring-operation infrastructure implicit in Rabin's admissible
indexing (Rabin 1960, §1.6, tex:264). -/
theorem computable₂_poly_map_param {Γ : Type v} {S : Type u} [Primcodable Γ] [CommRing S]
    [Primcodable S] (f : Γ → R →+* S)
    (hf : Computable₂ fun γ r => f γ r) :
    Computable₂ fun γ (P : Polynomial R) => P.map (f γ) := by
  have hlist : Computable fun x : Γ × Polynomial R => (polyCoeffs x.2).map (f x.1) :=
    Computable.list_map (computable_polyCoeffs.comp Computable.snd)
      (hf.comp
        (Computable.fst.comp Computable.fst)
        Computable.snd)
  have hpoly : Computable fun x : Γ × Polynomial R => (x.2.map (f x.1) : Polynomial S) :=
    (computable_polyOfList.comp hlist).of_eq fun x => by
    rcases x with ⟨γ, P⟩
    apply Polynomial.ext
    intro i
    rw [polyOfList_coeff, coeff_map, ← polyCoeffs_getD P i]
    by_cases hi : i < (polyCoeffs P).length
    · rw [List.getD_eq_getElem _ _ (by simpa using hi)]
      rw [List.getD_eq_getElem _ _ hi]
      simp
    · rw [List.getD_eq_default]
      · rw [List.getD_eq_default _ _ (le_of_not_gt hi)]
        exact (f γ).map_zero.symm
      · simpa using le_of_not_gt hi
  exact hpoly.to₂

omit [ComputableRing R] in
/-- Applying a computable ring homomorphism to the coefficients of a univariate
polynomial is computable.  The implementation maps the little-endian
coefficient list and rebuilds via `polyOfList`, so leading coefficients killed
by a non-injective homomorphism are re-canonicalized.  This is part of the
ring-operation infrastructure implicit in Rabin's admissible indexing
(Rabin 1960, §1.6, tex:264). -/
theorem computable_poly_map {S : Type u} [CommRing S] [Primcodable S]
    [ComputableRing S] (f : R →+* S) (hf : Computable f) :
    Computable fun P : Polynomial R => P.map f := by
  simpa using
    (computable₂_poly_map_param (R := R) (Γ := Unit) (S := S)
      (fun _ => f) ((hf.comp Computable.snd).to₂)).comp (Computable.const ()) Computable.id

theorem computable_poly_neg :
    Computable (Neg.neg : Polynomial R → Polynomial R) := by
  exact (computable₂_poly_mul.comp (computable_poly_C.comp (Computable.const (-1 : R)))
    Computable.id).of_eq fun P => by
      change C (-1 : R) * P = -P
      simp

theorem computable₂_poly_sub :
    Computable₂ ((· - ·) : Polynomial R → Polynomial R → Polynomial R) := by
  have h : Computable fun x : Polynomial R × Polynomial R => x.1 + (-x.2) :=
    computable₂_poly_add.comp Computable.fst (computable_poly_neg.comp Computable.snd)
  exact h.to₂.of_eq fun x => by
    rcases x with ⟨P, Q⟩
    rfl

instance instComputableRingPolynomial :
    ComputableRing (Polynomial R) := ⟨computable₂_poly_add, computable₂_poly_mul⟩

end Ops

/-! ## Rabin's Lemma 1: inverses and division -/

variable {F : Type u} [Field F]

section Inverses

variable [Primcodable F] [ComputableField F]

/-- **Rabin's Lemma 1** (tex:85-100): in a computable field the inverse is
computable, by unbounded search for the `b` with `a * b = 1` (with
`0⁻¹ = 0` by convention). -/
theorem ComputableField.computable_inv :
    Computable (Inv.inv : F → F) := by
  classical
  let search : F → ℕ → Option F := fun a n =>
    if a = 0 then some 0 else
      (Encodable.decode (α := F) n).bind fun b =>
        if a * b = 1 then some b else none
  refine Computable.of_total_sound_search (f := search) ?_ ?_ ?_
  · have hzero : Computable fun x : F × ℕ => decide (x.1 = 0) :=
      computable_decide_eq.comp Computable.fst (Computable.const 0)
    have hdecode : Computable fun x : F × ℕ => Encodable.decode (α := F) x.2 :=
      Computable.decode.comp Computable.snd
    have hbranch : Computable₂ fun (x : F × ℕ) (b : F) =>
        if x.1 * b = 1 then some b else none := by
      have hmul : Computable fun y : (F × ℕ) × F => y.1.1 * y.2 :=
        ComputableField.computable_mul.comp
          (Computable.fst.comp Computable.fst) Computable.snd
      have htest : Computable fun y : (F × ℕ) × F => decide (y.1.1 * y.2 = 1) :=
        computable_decide_eq.comp hmul (Computable.const 1)
      have hsome : Computable fun y : (F × ℕ) × F => some y.2 :=
        Computable.option_some.comp Computable.snd
      exact (Computable.cond htest hsome (Computable.const none)).to₂.of_eq fun y => by
        rcases y with ⟨x, b⟩
        by_cases h : x.1 * b = 1 <;> simp [h]
    have hnonzero : Computable fun x : F × ℕ =>
        (Encodable.decode (α := F) x.2).bind fun b =>
          if x.1 * b = 1 then some b else none :=
      Computable.option_bind hdecode hbranch
    exact (Computable.cond hzero (Computable.const (some 0)) hnonzero).to₂.of_eq fun x => by
      rcases x with ⟨a, n⟩
      by_cases h : a = 0 <;> simp [search, h]
  · intro a n b hb
    by_cases ha : a = 0
    · simp [search, ha] at hb
      subst b
      simp [ha]
    · rcases hdec : Encodable.decode (α := F) n with _ | c
      · simp [search, ha, hdec] at hb
      · by_cases hmul : a * c = 1
        · have hbc : b = c := by
            simpa [search, ha, hdec, hmul] using hb.symm
          subst b
          exact eq_inv_of_mul_eq_one_right hmul
        · simp [search, ha, hdec, hmul] at hb
  · intro a
    by_cases ha : a = 0
    · refine ⟨0, 0, ?_⟩
      simp [search, ha]
    · refine ⟨Encodable.encode a⁻¹, a⁻¹, ?_⟩
      simp [search, ha, Encodable.encodek]

theorem ComputableField.computable₂_div :
    Computable₂ ((· / ·) : F → F → F) := by
  have h : Computable fun x : F × F => x.1 * x.2⁻¹ :=
    ComputableField.computable_mul.comp Computable.fst
      (ComputableField.computable_inv.comp Computable.snd)
  exact h.to₂.of_eq fun x => by
    rcases x with ⟨a, b⟩
    change a * b⁻¹ = a / b
    rw [div_eq_mul_inv]

end Inverses

/-! ## Euclidean division and gcd -/

section Division

private lemma degree_lt_degree_iff_natDegree {r q : Polynomial F} (hq : q ≠ 0) :
    r.degree < q.degree ↔ r = 0 ∨ r.natDegree < q.natDegree ∧ r ≠ 0 := by
  constructor
  · intro h
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      rw [Polynomial.degree_eq_natDegree hr, Polynomial.degree_eq_natDegree hq] at h
      exact ⟨WithBot.coe_lt_coe.mp h, hr⟩
  · intro h
    rcases h with rfl | ⟨hdeg, hr⟩
    · rw [Polynomial.degree_zero, Polynomial.degree_eq_natDegree hq]
      exact WithBot.bot_lt_coe _
    · rw [Polynomial.degree_eq_natDegree hr, Polynomial.degree_eq_natDegree hq]
      exact WithBot.coe_lt_coe.mpr hdeg

private lemma div_mod_unique {p q c r : Polynomial F} (hq : q ≠ 0)
    (heq : p = q * c + r) (hdeg : r.degree < q.degree) : c = p / q ∧ r = p % q := by
  have hmoddeg : (p % q).degree < q.degree := Polynomial.degree_mod_lt p hq
  have hc : c = p / q := by
    by_contra hc
    have hdiff : c - p / q ≠ 0 := sub_ne_zero.mpr hc
    have hqr : q * (c - p / q) = p % q - r := by
      have hdiv : p = q * (p / q) + p % q := (EuclideanDomain.div_add_mod p q).symm
      calc
        q * (c - p / q) =
            (q * c + r) - (q * (p / q) + p % q) + (p % q - r) := by ring_nf
        _ = p - p + (p % q - r) := by rw [← heq, ← hdiv]
        _ = p % q - r := by ring_nf
    have hsmall : (p % q - r).degree < q.degree := by
      calc
        (p % q - r).degree ≤ max (p % q).degree r.degree := Polynomial.degree_sub_le _ _
        _ < q.degree := max_lt_iff.2 ⟨hmoddeg, hdeg⟩
    have hlarge : q.degree ≤ (q * (c - p / q)).degree := by
      rw [Polynomial.degree_mul, Polynomial.degree_eq_natDegree hq,
        Polynomial.degree_eq_natDegree hdiff]
      exact WithBot.coe_le_coe.2 (Nat.le_add_right _ _)
    exact not_lt_of_ge (hqr ▸ hlarge) hsmall
  have hr : r = p % q := by
    have hdecomp : q * c + p % q = p := by
      rw [hc]
      exact EuclideanDomain.div_add_mod p q
    have hsum : q * c + r = q * c + p % q := by
      rw [← heq, hdecomp]
    exact add_left_cancel hsum
  exact ⟨hc, hr⟩

variable [Primcodable F] [ComputableField F]

private theorem computable_poly_divMod :
    Computable fun x : Polynomial F × Polynomial F => (x.1 / x.2, x.1 % x.2) := by
  classical
  let search : (Polynomial F × Polynomial F) → ℕ → Option (Polynomial F × Polynomial F) :=
    fun x n =>
      (Encodable.decode (α := Polynomial F × Polynomial F) n).bind fun y =>
        if x.2 = 0 then
          if y.1 = 0 ∧ y.2 = x.1 then some y else none
        else
          if x.1 = x.2 * y.1 + y.2 ∧
              (y.2 = 0 ∨ y.2.natDegree < x.2.natDegree ∧ y.2 ≠ 0) then some y else none
  refine Computable.of_total_sound_search (f := search) ?_ ?_ ?_
  · have hdecode : Computable fun x : (Polynomial F × Polynomial F) × ℕ =>
        Encodable.decode (α := Polynomial F × Polynomial F) x.2 :=
      Computable.decode.comp Computable.snd
    have hbranch : Computable₂ fun (x : (Polynomial F × Polynomial F) × ℕ)
        (y : Polynomial F × Polynomial F) =>
        if x.1.2 = 0 then
          if y.1 = 0 ∧ y.2 = x.1.1 then some y else none
        else
          if x.1.1 = x.1.2 * y.1 + y.2 ∧
              (y.2 = 0 ∨ y.2.natDegree < x.1.2.natDegree ∧ y.2 ≠ 0) then
            some y
          else none := by
      let Z := ((Polynomial F × Polynomial F) × ℕ) × (Polynomial F × Polynomial F)
      have hp : Computable fun z : Z => z.1.1.1 :=
        Computable.fst.comp (Computable.fst.comp Computable.fst)
      have hq : Computable fun z : Z => z.1.1.2 :=
        Computable.snd.comp (Computable.fst.comp Computable.fst)
      have hc : Computable fun z : Z => z.2.1 :=
        Computable.fst.comp Computable.snd
      have hr : Computable fun z : Z => z.2.2 :=
        Computable.snd.comp Computable.snd
      have hsome : Computable fun z : Z => some z.2 :=
        Computable.option_some.comp Computable.snd
      have hnone : Computable fun _ : Z => (none : Option (Polynomial F × Polynomial F)) :=
        Computable.const none
      have hqZero : Computable fun z : Z => decide (z.1.1.2 = 0) :=
        computable_decide_eq.comp hq (Computable.const 0)
      have hcZero : Computable fun z : Z => decide (z.2.1 = 0) :=
        computable_decide_eq.comp hc (Computable.const 0)
      have hrEqP : Computable fun z : Z => decide (z.2.2 = z.1.1.1) :=
        computable_decide_eq.comp hr hp
      have hzeroGood : Computable fun z : Z => decide (z.2.1 = 0 ∧ z.2.2 = z.1.1.1) :=
        (Primrec.and.to_comp.comp hcZero hrEqP).of_eq fun z => by
          by_cases h₁ : z.2.1 = 0 <;> by_cases h₂ : z.2.2 = z.1.1.1 <;> simp [h₁, h₂]
      have hzeroBranch : Computable fun z : Z =>
          if z.2.1 = 0 ∧ z.2.2 = z.1.1.1 then some z.2 else none :=
        (Computable.cond hzeroGood hsome hnone).of_eq fun z => by
          by_cases h : z.2.1 = 0 ∧ z.2.2 = z.1.1.1 <;> simp [h]
      have hmul : Computable fun z : Z => z.1.1.2 * z.2.1 :=
        computable₂_poly_mul.comp hq hc
      have hadd : Computable fun z : Z => z.1.1.2 * z.2.1 + z.2.2 :=
        computable₂_poly_add.comp hmul hr
      have heq : Computable fun z : Z => decide (z.1.1.1 = z.1.1.2 * z.2.1 + z.2.2) :=
        computable_decide_eq.comp hp hadd
      have hrZero : Computable fun z : Z => decide (z.2.2 = 0) :=
        computable_decide_eq.comp hr (Computable.const 0)
      have hrNeZero : Computable fun z : Z => decide (z.2.2 ≠ 0) :=
        (Primrec.not.to_comp.comp hrZero).of_eq fun z => by
          by_cases h : z.2.2 = 0 <;> simp [h]
      have hdegLt : Computable fun z : Z => decide (z.2.2.natDegree < z.1.1.2.natDegree) :=
        Primrec.nat_lt.decide.to_comp.comp
          (computable_poly_natDegree.comp hr) (computable_poly_natDegree.comp hq)
      have hdegAndNe : Computable fun z : Z =>
          decide (z.2.2.natDegree < z.1.1.2.natDegree ∧ z.2.2 ≠ 0) :=
        (Primrec.and.to_comp.comp hdegLt hrNeZero).of_eq fun z => by
          by_cases h₁ : z.2.2.natDegree < z.1.1.2.natDegree <;>
            by_cases h₂ : z.2.2 ≠ 0 <;> simp [h₁, h₂]
      have hdegCond : Computable fun z : Z =>
          decide (z.2.2 = 0 ∨ z.2.2.natDegree < z.1.1.2.natDegree ∧ z.2.2 ≠ 0) :=
        (Primrec.or.to_comp.comp hrZero hdegAndNe).of_eq fun z => by
          by_cases h₁ : z.2.2 = 0 <;>
            by_cases h₂ : z.2.2.natDegree < z.1.1.2.natDegree ∧ z.2.2 ≠ 0 <;>
              simp [h₁, h₂]
      have hnonzeroGood : Computable fun z : Z =>
          decide (z.1.1.1 = z.1.1.2 * z.2.1 + z.2.2 ∧
            (z.2.2 = 0 ∨ z.2.2.natDegree < z.1.1.2.natDegree ∧ z.2.2 ≠ 0)) :=
        (Primrec.and.to_comp.comp heq hdegCond).of_eq fun z => by
          by_cases h₁ : z.1.1.1 = z.1.1.2 * z.2.1 + z.2.2 <;>
            by_cases h₂ :
              z.2.2 = 0 ∨ z.2.2.natDegree < z.1.1.2.natDegree ∧ z.2.2 ≠ 0 <;>
              simp [h₁, h₂]
      have hnonzeroBranch : Computable fun z : Z =>
          if z.1.1.1 = z.1.1.2 * z.2.1 + z.2.2 ∧
              (z.2.2 = 0 ∨ z.2.2.natDegree < z.1.1.2.natDegree ∧ z.2.2 ≠ 0) then
            some z.2
          else none :=
        (Computable.cond hnonzeroGood hsome hnone).of_eq fun z => by
          by_cases h : z.1.1.1 = z.1.1.2 * z.2.1 + z.2.2 ∧
              (z.2.2 = 0 ∨ z.2.2.natDegree < z.1.1.2.natDegree ∧ z.2.2 ≠ 0) <;>
            simp [h]
      exact (Computable.cond hqZero hzeroBranch hnonzeroBranch).to₂.of_eq fun z => by
        rcases z with ⟨x, y⟩
        by_cases hq0 : x.1.2 = 0
        · simp [hq0]
        · simp [hq0]
    exact (Computable.option_bind hdecode hbranch).to₂.of_eq fun x => by
      rcases x with ⟨⟨p, q⟩, n⟩
      rfl
  · intro x n b hb
    rcases x with ⟨p, q⟩
    change ((Encodable.decode (α := Polynomial F × Polynomial F) n).bind fun y =>
        if q = 0 then
          if y.1 = 0 ∧ y.2 = p then some y else none
        else
          if p = q * y.1 + y.2 ∧
              (y.2 = 0 ∨ y.2.natDegree < q.natDegree ∧ y.2 ≠ 0) then some y else none) =
        some b at hb
    rcases hdec : Encodable.decode (α := Polynomial F × Polynomial F) n with _ | y
    · rw [hdec] at hb
      cases hb
    · rcases y with ⟨c, r⟩
      rw [hdec] at hb
      change (if q = 0 then
          if c = 0 ∧ r = p then some (c, r) else none
        else
          if p = q * c + r ∧ (r = 0 ∨ r.natDegree < q.natDegree ∧ r ≠ 0) then
            some (c, r)
          else none) = some b at hb
      by_cases hq : q = 0
      · by_cases hgood : c = 0 ∧ r = p
        · rw [if_pos hq, if_pos hgood] at hb
          rcases hgood with ⟨hc, hr⟩
          cases hb
          ext <;> simp [hq, hc, hr]
        · rw [if_pos hq, if_neg hgood] at hb
          cases hb
      · by_cases hgood :
          p = q * c + r ∧ (r = 0 ∨ r.natDegree < q.natDegree ∧ r ≠ 0)
        · rw [if_neg hq, if_pos hgood] at hb
          cases hb
          have huniq := div_mod_unique (F := F) hq hgood.1
            ((degree_lt_degree_iff_natDegree (F := F) hq).2 hgood.2)
          exact Prod.ext huniq.1 huniq.2
        · rw [if_neg hq, if_neg hgood] at hb
          cases hb
  · intro x
    rcases x with ⟨p, q⟩
    by_cases hq : q = 0
    · refine ⟨Encodable.encode (0, p), (0, p), ?_⟩
      change ((Encodable.decode (α := Polynomial F × Polynomial F)
          (Encodable.encode (α := Polynomial F × Polynomial F) (0, p))).bind fun y =>
          if q = 0 then
            if y.1 = 0 ∧ y.2 = p then some y else none
          else
            if p = q * y.1 + y.2 ∧
                (y.2 = 0 ∨ y.2.natDegree < q.natDegree ∧ y.2 ≠ 0) then some y else none) =
          some (0, p)
      rw [show Encodable.decode (α := Polynomial F × Polynomial F)
          (Encodable.encode (α := Polynomial F × Polynomial F) (0, p)) = some (0, p) by
        exact Encodable.encodek (0, p)]
      change (if q = 0 then
          if (0 : Polynomial F) = 0 ∧ p = p then some (0, p) else none
        else
          if p = q * (0 : Polynomial F) + p ∧
              (p = 0 ∨ p.natDegree < q.natDegree ∧ p ≠ 0) then some (0, p) else none) =
        some (0, p)
      rw [if_pos hq, if_pos (show (0 : Polynomial F) = 0 ∧ p = p from ⟨rfl, rfl⟩)]
    · refine ⟨Encodable.encode (p / q, p % q), (p / q, p % q), ?_⟩
      have hdiv : p = q * (p / q) + p % q := (EuclideanDomain.div_add_mod p q).symm
      have hdeg : p % q = 0 ∨ (p % q).natDegree < q.natDegree ∧ p % q ≠ 0 :=
        (degree_lt_degree_iff_natDegree (F := F) hq).1 (Polynomial.degree_mod_lt p hq)
      change ((Encodable.decode (α := Polynomial F × Polynomial F)
          (Encodable.encode (α := Polynomial F × Polynomial F) (p / q, p % q))).bind fun y =>
          if q = 0 then
            if y.1 = 0 ∧ y.2 = p then some y else none
          else
            if p = q * y.1 + y.2 ∧
                (y.2 = 0 ∨ y.2.natDegree < q.natDegree ∧ y.2 ≠ 0) then some y else none) =
          some (p / q, p % q)
      rw [show Encodable.decode (α := Polynomial F × Polynomial F)
          (Encodable.encode (α := Polynomial F × Polynomial F) (p / q, p % q)) =
            some (p / q, p % q) by
        exact Encodable.encodek (p / q, p % q)]
      change (if q = 0 then
          if p / q = 0 ∧ p % q = p then some (p / q, p % q) else none
        else
          if p = q * (p / q) + p % q ∧
              (p % q = 0 ∨ (p % q).natDegree < q.natDegree ∧ p % q ≠ 0) then
            some (p / q, p % q)
          else none) = some (p / q, p % q)
      rw [if_neg hq, if_pos ⟨hdiv, hdeg⟩]

theorem computable₂_poly_div :
    Computable₂ ((· / ·) : Polynomial F → Polynomial F → Polynomial F) := by
  exact (Computable.fst.comp computable_poly_divMod).to₂

theorem computable₂_poly_mod :
    Computable₂ ((· % ·) : Polynomial F → Polynomial F → Polynomial F) := by
  exact (Computable.snd.comp computable_poly_divMod).to₂

open scoped Classical in
private noncomputable def polyGcdStep (x : Polynomial F × Polynomial F) :
    Polynomial F × Polynomial F :=
  if x.1 = 0 then x else (x.2 % x.1, x.1)

open scoped Classical in
omit [Primcodable F] [ComputableField F] in
private lemma polyGcdStep_iter_zero (fuel : ℕ) (b : Polynomial F) :
    (((polyGcdStep (F := F))^[fuel]) (0, b)).2 = b := by
  induction fuel with
  | zero =>
      rfl
  | succ fuel IH =>
      rw [Function.iterate_succ_apply]
      change (((polyGcdStep (F := F))^[fuel])
          (if (0 : Polynomial F) = 0 then (0, b) else (b % 0, 0))).2 = b
      rw [if_pos rfl]
      exact IH

private lemma nat_rec_step_eq_iterate {α : Type*} (f : α → α) :
    ∀ n x, Nat.rec (motive := fun _ => α) x (fun _ y => f y) n = f^[n] x := by
  intro n
  induction n with
  | zero =>
      intro x
      rfl
  | succ n IH =>
      intro x
      simp [IH, Function.iterate_succ_apply']

private theorem computable_nat_iterate {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → ℕ} {g : α → β} {h : α → β → β}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable fun a => (h a)^[f a] (g a) := by
  have hstep : Computable₂ fun a (p : ℕ × β) => h a p.2 := by
    exact (hh.comp Computable.fst (Computable.snd.comp Computable.snd)).to₂
  have hrec : Computable fun a =>
      Nat.rec (motive := fun _ => β) (g a) (fun _ y => h a y) (f a) :=
    Computable.nat_rec hf hg hstep
  exact hrec.of_eq fun a => by
    induction f a with
    | zero =>
        rfl
    | succ n IH =>
        simp [IH, Function.iterate_succ_apply']

open scoped Classical in
omit [Primcodable F] [ComputableField F] in
private lemma polyGcdStep_iter_snd_eq_gcd :
    haveI : DecidableEq (Polynomial F) := Classical.decEq _
    ∀ fuel (a b : Polynomial F),
      a = 0 ∨ a.natDegree + 2 ≤ fuel + 1 →
      (((polyGcdStep (F := F))^[fuel]) (a, b)).2 = EuclideanDomain.gcd a b := by
  letI : DecidableEq (Polynomial F) := Classical.decEq _
  intro fuel
  induction fuel with
  | zero =>
      intro a b hfuel
      rcases hfuel with hzero | hle
      · subst a
        rw [EuclideanDomain.gcd_zero_left]
        rfl
      · have htwo : 2 ≤ a.natDegree + 2 := Nat.le_add_left 2 a.natDegree
        exact (Nat.not_succ_le_self 1 (le_trans htwo hle)).elim
  | succ fuel IH =>
      intro a b hfuel
      by_cases ha : a = 0
      · subst a
        rw [EuclideanDomain.gcd_zero_left]
        exact polyGcdStep_iter_zero (F := F) (fuel + 1) b
      · rcases hfuel with hzero | hle
        · exact (ha hzero).elim
        · rw [Function.iterate_succ_apply]
          change (((polyGcdStep (F := F))^[fuel])
              (polyGcdStep (F := F) (a, b))).2 = EuclideanDomain.gcd a b
          rw [show polyGcdStep (F := F) (a, b) = (b % a, a) by
            rw [polyGcdStep, if_neg ha]]
          rw [EuclideanDomain.gcd_val]
          by_cases hr : b % a = 0
          · exact IH (b % a) a (Or.inl hr)
          · have hmoddeg : (b % a).natDegree < a.natDegree := by
              have hdegree : (b % a).degree < a.degree := Polynomial.degree_mod_lt b ha
              rw [Polynomial.degree_eq_natDegree hr, Polynomial.degree_eq_natDegree ha] at hdegree
              exact WithBot.coe_lt_coe.mp hdegree
            have hfuel' : (b % a).natDegree + 2 ≤ fuel + 1 := by
              have hr1 : (b % a).natDegree + 1 ≤ a.natDegree :=
                Nat.succ_le_iff.mpr hmoddeg
              have hr2 : (b % a).natDegree + 2 ≤ a.natDegree + 1 := by
                simpa [Nat.add_assoc] using Nat.add_le_add_right hr1 1
              have hle' : (a.natDegree + 1).succ ≤ (fuel + 1).succ := by
                simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hle
              exact le_trans hr2 (Nat.succ_le_succ_iff.mp hle')
            exact IH (b % a) a (Or.inr hfuel')

private theorem computable_polyGcdStep :
    Computable (polyGcdStep (F := F)) := by
  classical
  have hzero : Computable fun x : Polynomial F × Polynomial F => decide (x.1 = 0) :=
    computable_decide_eq.comp Computable.fst (Computable.const 0)
  have hnext : Computable fun x : Polynomial F × Polynomial F => (x.2 % x.1, x.1) :=
    Computable.pair (computable₂_poly_mod.comp Computable.snd Computable.fst) Computable.fst
  exact (Computable.cond hzero Computable.id hnext).of_eq fun x => by
    by_cases hx : x.1 = 0
    · rw [polyGcdStep, if_pos hx]
      simp [hx]
    · rw [polyGcdStep, if_neg hx]
      simp [hx]

private theorem computable_polyGcdIter :
    Computable fun x : Polynomial F × Polynomial F =>
      ((polyGcdStep (F := F))^[x.1.natDegree + 2]) x := by
  classical
  have hfuel : Computable fun x : Polynomial F × Polynomial F => x.1.natDegree + 2 :=
    Primrec.nat_add.to_comp.comp
      (computable_poly_natDegree.comp Computable.fst) (Computable.const 2)
  have hstep : Computable₂ fun (_ : Polynomial F × Polynomial F)
      (x : Polynomial F × Polynomial F) => polyGcdStep (F := F) x := by
    exact ((computable_polyGcdStep (F := F)).comp Computable.snd).to₂
  exact computable_nat_iterate hfuel Computable.id hstep

theorem computable₂_poly_gcd :
    haveI : DecidableEq (Polynomial F) := Classical.decEq _
    Computable₂ (EuclideanDomain.gcd :
      Polynomial F → Polynomial F → Polynomial F) := by
  classical
  exact (Computable.snd.comp (computable_polyGcdIter (F := F))).to₂.of_eq fun x => by
    rcases x with ⟨a, b⟩
    exact polyGcdStep_iter_snd_eq_gcd (F := F) (a.natDegree + 2) a b
      (Or.inr (Nat.le_add_right (a.natDegree + 2) 1))

end Division

end Semicontinuity
