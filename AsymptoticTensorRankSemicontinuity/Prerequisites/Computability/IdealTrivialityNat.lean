/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.IdealTriviality
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.MvPolynomialNatComputable
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.CheckerComputable

/-!
# Countable-variable ideal triviality via finite levels

Rabin's Lemma 5 is stated for the full polynomial ring `F[x₁, x₂, ...]`, but
at `rabin.tex`:357 he immediately restricts to the finitely many variables
appearing in the input polynomials.  This file formalizes that pure algebraic
restriction: for polynomials in `MvPolynomial ℕ F` whose variables all lie
below a fixed level `m`, Bezout certificates and ideal triviality transfer
equivalently to `MvPolynomial (Fin m) F`.

No computability content is used here.
-/

noncomputable section

universe u

namespace Semicontinuity

open scoped BigOperators

open MvPolynomial

variable {F : Type u} [Field F]

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

private theorem span_list_set_eq_range_get {R : Type*} (fs : List R) :
    ({g | g ∈ fs} : Set R) = Set.range fs.get := by
  rw [Set.range_list_get]

theorem one_mem_span_iff_list_certificate {R : Type*} [CommSemiring R]
    (fs : List R) :
    (1 : R) ∈ Ideal.span {g | g ∈ fs} ↔
      ∃ rs : List R, rs.length = fs.length ∧
        (List.zipWith (· * ·) rs fs).sum = 1 := by
  rw [span_list_set_eq_range_get fs]
  change (1 : R) ∈ Ideal.span (Set.range fun i : Fin fs.length => fs[i]) ↔
    ∃ rs : List R, rs.length = fs.length ∧
      (List.zipWith (· * ·) rs fs).sum = 1
  rw [Ideal.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨List.ofFn r, by simp, ?_⟩
    rw [zipWith_mul_sum_eq_finset_sum_get (List.ofFn r) fs (by simp)]
    simpa using hr
  · rintro ⟨rs, hrs, hsum⟩
    refine ⟨fun i : Fin fs.length => rs[i.val]'(by rw [hrs]; exact i.isLt), ?_⟩
    rw [← hsum]
    exact (zipWith_mul_sum_eq_finset_sum_get rs fs hrs).symm

private theorem AlgHom.map_zipWith_mul_sum {R S : Type*} [CommSemiring R] [CommSemiring S]
    (g : R →+* S) :
    ∀ (rs fs : List R),
      g ((List.zipWith (· * ·) rs fs).sum) =
        (List.zipWith (· * ·) (rs.map g) (fs.map g)).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | r :: rs, f :: fs => by
      simp [AlgHom.map_zipWith_mul_sum g rs fs, map_add, map_mul]

private theorem map_incl_restrictLevel_eq_self {m : ℕ} (fs : List (MvPolynomial ℕ F))
    (hlvl : ∀ f ∈ fs, MvPolynomialNat.level (F := F) f ≤ m) :
    (fs.map (MvPolynomialNat.restrictLevel (F := F) m)).map
        (MvPolynomialNat.inclLevel (F := F) m) = fs := by
  rw [List.map_map]
  simpa using List.map_congr_left (l := fs) fun f hf =>
    MvPolynomialNat.incl_restrictLevel_of_level_le (F := F) (n := m) (p := f) (hlvl f hf)

/-- Rabin `rabin.tex`:357 variable restriction, certificate form.

If every input polynomial in `MvPolynomial ℕ F` has level at most `m`, then a
Bezout certificate exists in the countable-variable ring if and only if a
Bezout certificate exists after restricting the inputs to `MvPolynomial (Fin m) F`. -/
theorem one_mem_span_nat_iff_fin {m : ℕ} (fs : List (MvPolynomial ℕ F))
    (hlvl : ∀ f ∈ fs, MvPolynomialNat.level (F := F) f ≤ m) :
    (∃ rs : List (MvPolynomial ℕ F), rs.length = fs.length ∧
        (List.zipWith (· * ·) rs fs).sum = 1) ↔
      (∃ rs' : List (MvPolynomial (Fin m) F), rs'.length = fs.length ∧
        (List.zipWith (· * ·) rs'
          (fs.map (MvPolynomialNat.restrictLevel (F := F) m))).sum = 1) := by
  constructor
  · rintro ⟨rs, hrs, hsum⟩
    refine ⟨rs.map (MvPolynomialNat.restrictLevel (F := F) m), by simpa using hrs, ?_⟩
    have hmap := congrArg (MvPolynomialNat.restrictLevel (F := F) m) hsum
    change (List.zipWith (· * ·)
        (rs.map (MvPolynomialNat.restrictLevel (F := F) m).toRingHom)
        (fs.map (MvPolynomialNat.restrictLevel (F := F) m).toRingHom)).sum = 1
    rw [← AlgHom.map_zipWith_mul_sum (MvPolynomialNat.restrictLevel (F := F) m).toRingHom rs fs]
    simpa using hmap
  · rintro ⟨rs', hrs', hsum⟩
    refine ⟨rs'.map (MvPolynomialNat.inclLevel (F := F) m), by simpa using hrs', ?_⟩
    have hmap := congrArg (MvPolynomialNat.inclLevel (F := F) m) hsum
    have hcert :
        (List.zipWith (· * ·) (rs'.map (MvPolynomialNat.inclLevel (F := F) m))
            ((fs.map (MvPolynomialNat.restrictLevel (F := F) m)).map
              (MvPolynomialNat.inclLevel (F := F) m))).sum = 1 := by
      change (List.zipWith (· * ·)
          (rs'.map (MvPolynomialNat.inclLevel (F := F) m).toRingHom)
          ((fs.map (MvPolynomialNat.restrictLevel (F := F) m)).map
            (MvPolynomialNat.inclLevel (F := F) m).toRingHom)).sum = 1
      rw [← AlgHom.map_zipWith_mul_sum (MvPolynomialNat.inclLevel (F := F) m).toRingHom
        rs' (fs.map (MvPolynomialNat.restrictLevel (F := F) m))]
      simpa using hmap
    simpa [map_incl_restrictLevel_eq_self (F := F) fs hlvl] using hcert

/-- Rabin `rabin.tex`:357 variable restriction, Nullstellensatz headline.

For countable-variable inputs whose variables all lie below level `m`, ideal
triviality is equivalent to absence of a common zero for the restricted
`Fin m`-variable inputs over the algebraic closure. -/
theorem one_mem_span_nat_iff_no_common_zero {m : ℕ} (fs : List (MvPolynomial ℕ F))
    (hlvl : ∀ f ∈ fs, MvPolynomialNat.level (F := F) f ≤ m) :
    (∃ rs : List (MvPolynomial ℕ F), rs.length = fs.length ∧
        (List.zipWith (· * ·) rs fs).sum = 1) ↔
      ¬ ∃ ξ : Fin m → AlgebraicClosure F,
        ∀ g ∈ fs.map (MvPolynomialNat.restrictLevel (F := F) m), MvPolynomial.aeval ξ g = 0 :=
  by
    let fs' := fs.map (MvPolynomialNat.restrictLevel (F := F) m)
    have hlen : fs'.length = fs.length := by simp [fs']
    have hnorm :
        (∃ rs' : List (MvPolynomial (Fin m) F), rs'.length = fs.length ∧
            (List.zipWith (· * ·) rs' fs').sum = 1) ↔
          (∃ rs' : List (MvPolynomial (Fin m) F), rs'.length = fs'.length ∧
            (List.zipWith (· * ·) rs' fs').sum = 1) := by
      constructor
      · rintro ⟨rs', hrs', hsum⟩
        exact ⟨rs', by simpa [hlen] using hrs', hsum⟩
      · rintro ⟨rs', hrs', hsum⟩
        exact ⟨rs', by simpa [hlen] using hrs', hsum⟩
    exact (one_mem_span_nat_iff_fin (F := F) fs hlvl).trans
      (hnorm.trans (exists_certificate_list_iff (F := F) fs'))

/-- Rabin `rabin.tex`:357 variable restriction, ideal-span form.

For level-`m` countable-variable inputs, `1` belongs to their generated ideal in
`MvPolynomial ℕ F` exactly when `1` belongs to the generated ideal of their
restrictions in `MvPolynomial (Fin m) F`. -/
theorem one_mem_span_nat_iff_span_fin {m : ℕ} (fs : List (MvPolynomial ℕ F))
    (hlvl : ∀ f ∈ fs, MvPolynomialNat.level (F := F) f ≤ m) :
    (1 : MvPolynomial ℕ F) ∈ Ideal.span {g | g ∈ fs} ↔
      (1 : MvPolynomial (Fin m) F) ∈
        Ideal.span {g | g ∈ fs.map (MvPolynomialNat.restrictLevel (F := F) m)} := by
  rw [one_mem_span_iff_list_certificate (fs := fs),
    one_mem_span_iff_list_certificate (fs := fs.map (MvPolynomialNat.restrictLevel (F := F) m))]
  simpa using one_mem_span_nat_iff_fin (F := F) fs hlvl

/-! ## Uniform computable ideal triviality over the countable-variable ring -/

open Polynomial

private abbrev RabinWitnessNat (F : Type u) [Field F] :=
  List (MvPolynomial ℕ F) ⊕ (Polynomial F × List (Polynomial F))

private def certificatePredNat (fs rs : List (MvPolynomial ℕ F)) : Prop :=
  rs.length = fs.length ∧ (List.zipWith (· * ·) rs fs).sum = 1

private def candidatePredNat (fs : List (MvPolynomial ℕ F))
    (w : Polynomial F × List (Polynomial F)) : Prop :=
  w.1.leadingCoeff = 1 ∧ 1 ≤ w.1.natDegree ∧
    ∀ h ∈ fs,
      (MvPolynomial.eval₂ Polynomial.C (fun i : ℕ => w.2.getD i 0) h) % w.1 = 0

open Classical in
private def rabinCheckNat (fs : List (MvPolynomial ℕ F))
    (w : RabinWitnessNat F) : Option Bool :=
  Sum.elim
    (fun rs =>
      if certificatePredNat fs rs then some true else none)
    (fun z =>
      if candidatePredNat fs z then some false else none) w

private def levelMax (fs : List (MvPolynomial ℕ F)) : ℕ :=
  fs.foldl (fun n f => max n (MvPolynomialNat.level (F := F) f)) 0

private theorem foldl_levelMax_acc_le (fs : List (MvPolynomial ℕ F)) (n : ℕ) :
    n ≤ fs.foldl (fun k f => max k (MvPolynomialNat.level (F := F) f)) n := by
  induction fs generalizing n with
  | nil => simp
  | cons f fs ih =>
      exact le_trans (Nat.le_max_left n (MvPolynomialNat.level (F := F) f)) (ih _)

private theorem level_le_foldl_levelMax_of_mem {fs : List (MvPolynomial ℕ F)}
    {f : MvPolynomial ℕ F} (hf : f ∈ fs) (n : ℕ) :
    MvPolynomialNat.level (F := F) f ≤
      fs.foldl (fun k h => max k (MvPolynomialNat.level (F := F) h)) n := by
  induction fs generalizing n with
  | nil => cases hf
  | cons h fs ih =>
      rw [List.mem_cons] at hf
      rcases hf with rfl | hf
      · exact le_trans (Nat.le_max_right n (MvPolynomialNat.level (F := F) f))
          (foldl_levelMax_acc_le (F := F) fs _)
      · exact ih hf _

private theorem level_le_levelMax_of_mem {fs : List (MvPolynomial ℕ F)}
    {f : MvPolynomial ℕ F} (hf : f ∈ fs) :
    MvPolynomialNat.level (F := F) f ≤ levelMax (F := F) fs :=
  level_le_foldl_levelMax_of_mem (F := F) hf 0

section NatComputability

variable [Primcodable F] [ComputableField F]

private theorem computable_decide_nat_le_nat :
    Computable₂ fun a b : ℕ => decide (a ≤ b) := by
  exact Primrec.nat_le.decide.to_comp

private theorem computable_levelMax :
    Computable fun fs : List (MvPolynomial ℕ F) => levelMax (F := F) fs := by
  have hstep : Computable₂ fun (_ : List (MvPolynomial ℕ F)) =>
      fun p : ℕ × MvPolynomial ℕ F =>
        max p.1 (MvPolynomialNat.level (F := F) p.2) := by
    exact (Primrec.nat_max.to_comp.comp
      (Computable.fst.comp Computable.snd)
      (MvPolynomialNat.computable_level (F := F).comp
        (Computable.snd.comp Computable.snd))).to₂
  exact (Computable.list_foldl Computable.id (Computable.const 0) hstep).of_eq fun fs => by
    rfl

set_option linter.flexible false in
open Classical in
private theorem computable_certificatePredNat :
    Computable₂ fun fs rs : List (MvPolynomial ℕ F) =>
      decide (certificatePredNat fs rs) := by
  let P := MvPolynomial ℕ F
  have hlen : Computable fun x : List P × List P => decide (x.2.length = x.1.length) :=
    computable_decide_eq.comp (Computable.list_length.comp Computable.snd)
      (Computable.list_length.comp Computable.fst)
  have hmul : Computable fun x : (List P × List P) × P × P => x.2.1 * x.2.2 :=
    ComputableRing.computable_mul.comp (Computable.fst.comp Computable.snd)
      (Computable.snd.comp Computable.snd)
  have hzip : Computable fun x : List P × List P =>
      List.zipWith (· * ·) x.2 x.1 :=
    Computable.list_zipWith (0 : P) (0 : P) Computable.snd Computable.fst hmul
  have hsum : Computable fun x : List P × List P =>
      (List.zipWith (· * ·) x.2 x.1).sum :=
    Computable.list_sum ComputableRing.computable_add hzip
  have heq : Computable fun x : List P × List P =>
      decide ((List.zipWith (· * ·) x.2 x.1).sum = (1 : P)) :=
    computable_decide_eq.comp hsum (Computable.const 1)
  have hand : Computable fun x : List P × List P =>
      decide (x.2.length = x.1.length) &&
        decide ((List.zipWith (· * ·) x.2 x.1).sum = (1 : P)) :=
    Primrec.and.to_comp.comp hlen heq
  exact hand.to₂.of_eq fun x => by
    rcases x with ⟨fs, rs⟩
    by_cases h₁ : rs.length = fs.length
    · by_cases h₂ : (List.zipWith (· * ·) rs fs).sum = (1 : P)
      · simp [certificatePredNat, h₁, h₂]
        exact h₂
      · simp [certificatePredNat, h₁, h₂]
        exact h₂
    · simp [certificatePredNat, h₁]

set_option linter.flexible false in
open Classical in
private theorem computable_candidatePredNat :
    Computable₂ fun fs : List (MvPolynomial ℕ F) =>
      fun w : Polynomial F × List (Polynomial F) => decide (candidatePredNat fs w) := by
  let P := MvPolynomial ℕ F
  let Q := Polynomial F
  have hlead : Computable fun x : List P × (Q × List Q) =>
      decide (x.2.1.leadingCoeff = (1 : F)) :=
    computable_decide_eq.comp (computable_poly_leadingCoeff.comp
      (Computable.fst.comp Computable.snd)) (Computable.const 1)
  have hdeg : Computable fun x : List P × (Q × List Q) =>
      decide (1 ≤ x.2.1.natDegree) :=
    computable_decide_nat_le_nat.comp (Computable.const 1)
      (computable_poly_natDegree.comp (Computable.fst.comp Computable.snd))
  have heval : Computable fun y : (List P × (Q × List Q)) × P =>
      MvPolynomial.eval₂ Polynomial.C
        (fun i : ℕ => y.1.2.2.getD i 0) y.2 :=
    (MvPolynomialNat.computable₂_mvPolynomialNat_eval (F := F) (Q := Q)
      Polynomial.C computable_poly_C).comp
        (Computable.snd.comp (Computable.snd.comp Computable.fst))
        Computable.snd
  have hmod : Computable fun y : (List P × (Q × List Q)) × P =>
      (MvPolynomial.eval₂ Polynomial.C
        (fun i : ℕ => y.1.2.2.getD i 0) y.2) % y.1.2.1 :=
    computable₂_poly_mod.comp heval (Computable.fst.comp (Computable.snd.comp Computable.fst))
  have hzero : Computable₂ fun x : List P × (Q × List Q) => fun h : P =>
      decide (((MvPolynomial.eval₂ Polynomial.C
        (fun i : ℕ => x.2.2.getD i 0) h) % x.2.1) = (0 : Q)) :=
    (computable_decide_eq.comp hmod (Computable.const 0)).to₂
  have hall : Computable fun x : List P × (Q × List Q) =>
      x.1.all fun h =>
        decide (((MvPolynomial.eval₂ Polynomial.C
          (fun i : ℕ => x.2.2.getD i 0) h) % x.2.1) = (0 : Q)) :=
    Computable.list_all Computable.fst hzero
  have hcond : Computable fun x : List P × (Q × List Q) =>
      (decide (x.2.1.leadingCoeff = (1 : F)) &&
        decide (1 ≤ x.2.1.natDegree)) && x.1.all fun h =>
          decide (((MvPolynomial.eval₂ Polynomial.C
            (fun i : ℕ => x.2.2.getD i 0) h) % x.2.1) = (0 : Q)) :=
    Primrec.and.to_comp.comp (Primrec.and.to_comp.comp hlead hdeg) hall
  exact hcond.to₂.of_eq fun x => by
    rcases x with ⟨fs, p, gs⟩
    dsimp
    by_cases h₁ : p.leadingCoeff = (1 : F)
    · by_cases h₂ : 1 ≤ p.natDegree
      · simp [candidatePredNat, h₁, h₂]
        by_cases h₃ : ∀ h ∈ fs,
            p ∣ MvPolynomial.eval₂ Polynomial.C (fun i : ℕ => gs[i]?.getD 0) h
        · rw [decide_eq_true h₃]
          rw [List.all_eq_true]
          intro h hh
          exact decide_eq_true (h₃ h hh)
        · rw [decide_eq_false h₃]
          rw [List.all_eq_false]
          rw [not_forall] at h₃
          obtain ⟨h, hh⟩ := h₃
          rw [not_forall] at hh
          obtain ⟨hm, hhm⟩ := hh
          exact ⟨h, hm, by rw [decide_eq_false hhm]; simp⟩
      · simp [candidatePredNat, h₁, h₂]
    · simp [candidatePredNat, h₁]

open Classical in
private theorem computable_rabinCheckNat :
    Computable₂ (rabinCheckNat (F := F)) := by
  let P := MvPolynomial ℕ F
  let W := RabinWitnessNat F
  let WR := Polynomial F × List (Polynomial F)
  have hleft : Computable₂ fun p : List P × W => fun rs : List P =>
      if certificatePredNat p.1 rs then some true else none := by
    have hcond : Computable fun q : (List P × W) × List P =>
        decide (certificatePredNat q.1.1 q.2) :=
      computable_certificatePredNat (F := F).comp (Computable.fst.comp Computable.fst)
        Computable.snd
    exact ((Computable.cond hcond (Computable.const (some true))
      (Computable.const Option.none)).to₂).of_eq fun q => by
        rcases q with ⟨p, rs⟩
        by_cases h : certificatePredNat p.1 rs <;> simp [h]
  have hright : Computable₂ fun p : List P × W => fun z : WR =>
      if candidatePredNat p.1 z then some false else none := by
    have hcond : Computable fun q : (List P × W) × WR =>
        decide (candidatePredNat q.1.1 q.2) :=
      computable_candidatePredNat (F := F).comp (Computable.fst.comp Computable.fst)
        Computable.snd
    exact ((Computable.cond hcond (Computable.const (some false))
      (Computable.const Option.none)).to₂).of_eq fun q => by
        rcases q with ⟨p, z⟩
        by_cases h : candidatePredNat p.1 z <;> simp [h]
  have hcases :=
    Computable.sumCasesOn (Computable.snd : Computable (fun p : List P × W => p.2))
      hleft hright
  exact hcases.to₂.of_eq fun xw => by
    rcases xw with ⟨fs, w⟩
    cases w <;> rfl

end NatComputability

section NatMath

private theorem aeval_eq_eval₂_C {m : ℕ} (g : Fin m → Polynomial F)
    (h : MvPolynomial (Fin m) F) :
    MvPolynomial.aeval g h = MvPolynomial.eval₂ Polynomial.C g h := by
  rw [MvPolynomial.aeval_def]
  rw [Polynomial.algebraMap_eq]

private theorem eval₂_nat_restrictLevel_eq_aeval {m : ℕ}
    (h : MvPolynomial ℕ F) (hh : MvPolynomialNat.level (F := F) h ≤ m)
    (gs : List (Polynomial F)) :
    MvPolynomial.eval₂ Polynomial.C (fun i : ℕ => gs.getD i 0) h =
      MvPolynomial.aeval (fun j : Fin m => gs.getD j 0)
        (MvPolynomialNat.restrictLevel (F := F) m h) := by
  calc
    MvPolynomial.eval₂ Polynomial.C (fun i : ℕ => gs.getD i 0) h
        = MvPolynomial.eval₂ Polynomial.C (fun i : ℕ => gs.getD i 0)
            (MvPolynomialNat.inclLevel (F := F) m
              (MvPolynomialNat.restrictLevel (F := F) m h)) := by
          rw [MvPolynomialNat.incl_restrictLevel_of_level_le (F := F) (n := m) (p := h) hh]
    _ = MvPolynomial.eval₂ Polynomial.C (fun j : Fin m => gs.getD j 0)
            (MvPolynomialNat.restrictLevel (F := F) m h) := by
          rw [MvPolynomialNat.inclLevel, MvPolynomial.eval₂_rename]
          rfl
    _ = MvPolynomial.aeval (fun j : Fin m => gs.getD j 0)
            (MvPolynomialNat.restrictLevel (F := F) m h) := by
          rw [aeval_eq_eval₂_C]

private theorem dvd_iff_mod_eq_zero_nat (p h : Polynomial F) :
    p ∣ h ↔ h % p = 0 := by
  rw [EuclideanDomain.mod_eq_zero]

private theorem candidatePredNat_common_zero (fs : List (MvPolynomial ℕ F))
    {p : Polynomial F} {gs : List (Polynomial F)} (hw : candidatePredNat fs (p, gs)) :
    ∃ ξ : Fin (levelMax (F := F) fs) → AlgebraicClosure F,
      ∀ h ∈ fs.map (MvPolynomialNat.restrictLevel (F := F) (levelMax (F := F) fs)),
        MvPolynomial.aeval ξ h = 0 := by
  let m := levelMax (F := F) fs
  let fsR := fs.map (MvPolynomialNat.restrictLevel (F := F) m)
  let f : Fin fsR.length → MvPolynomial (Fin m) F := fun i => fsR[i]
  have hdiv : ∀ i, p ∣ MvPolynomial.aeval (fun j : Fin m => gs.getD j 0) (f i) := by
    intro i
    have hi : f i ∈ fsR := List.getElem_mem i.isLt
    rw [List.mem_map] at hi
    obtain ⟨h, hh, hres⟩ := hi
    rw [← hres]
    rw [← eval₂_nat_restrictLevel_eq_aeval (F := F) h
      (level_le_levelMax_of_mem (F := F) hh) gs]
    rw [dvd_iff_mod_eq_zero_nat]
    exact hw.2.2 h hh
  obtain ⟨ξ, hξ⟩ :=
    common_zero_of_candidate f p hw.1 hw.2.1 (fun j : Fin m => gs.getD j 0) hdiv
  refine ⟨ξ, ?_⟩
  intro h hh
  rw [List.mem_iff_get] at hh
  obtain ⟨i, rfl⟩ := hh
  exact hξ i

private theorem candidatePredNat_of_candidate (fs : List (MvPolynomial ℕ F))
    {p : Polynomial F} {g : Fin (levelMax (F := F) fs) → Polynomial F}
    (hmonic : p.Monic) (hdeg : 1 ≤ p.natDegree)
    (hdiv : ∀ i : Fin (fs.map
        (MvPolynomialNat.restrictLevel (F := F) (levelMax (F := F) fs))).length,
        p ∣ MvPolynomial.aeval g
          ((fs.map (MvPolynomialNat.restrictLevel (F := F) (levelMax (F := F) fs)))[i])) :
    candidatePredNat fs (p, List.ofFn g) := by
  let m := levelMax (F := F) fs
  refine ⟨hmonic, hdeg, ?_⟩
  intro h hh
  rw [← dvd_iff_mod_eq_zero_nat]
  rw [eval₂_nat_restrictLevel_eq_aeval (F := F) h
    (level_le_levelMax_of_mem (F := F) hh) (List.ofFn g)]
  rw [List.mem_iff_get] at hh
  obtain ⟨i, rfl⟩ := hh
  let iR : Fin (fs.map
      (MvPolynomialNat.restrictLevel (F := F) (levelMax (F := F) fs))).length :=
    ⟨i, by simp⟩
  have hd := hdiv iR
  have hiR :
      (fs.map (MvPolynomialNat.restrictLevel (F := F) (levelMax (F := F) fs)))[iR] =
        MvPolynomialNat.restrictLevel (F := F) (levelMax (F := F) fs) fs[i] := by
    simp [iR]
  rw [hiR] at hd
  convert hd using 2
  ext j
  simp

end NatMath

section NatSearch

variable [Primcodable F] [ComputableField F] [PerfectField F]

set_option linter.unusedSectionVars false

private theorem computablePred_of_rabinCheckNat
    {p : List (MvPolynomial ℕ F) → Prop}
    (hsound : ∀ (fs : List (MvPolynomial ℕ F)) (w : RabinWitnessNat F) (b : Bool),
      rabinCheckNat fs w = some b → (b = true ↔ p fs))
    (htotal : ∀ fs : List (MvPolynomial ℕ F), ∃ (w : RabinWitnessNat F) (b : Bool),
      rabinCheckNat fs w = some b) :
    ComputablePred p := by
  classical
  refine ⟨fun _ => Classical.propDecidable _, ?_⟩
  have hval : ∀ (fs : List (MvPolynomial ℕ F)) (w : RabinWitnessNat F) (b : Bool),
      rabinCheckNat fs w = some b → b = decide (p fs) := by
    intro fs w b hw
    have h := hsound fs w b hw
    rcases Bool.eq_false_or_eq_true b with hb | hb
    · subst hb
      symm
      rw [decide_eq_true_eq]
      exact h.mp rfl
    · subst hb
      symm
      rw [decide_eq_false_iff_not]
      intro hp
      exact Bool.noConfusion (h.mpr hp)
  have hstep :=
    Computable.bind_decode_iff.mpr (computable_rabinCheckNat (F := F))
  have hpart := Partrec.rfindOpt hstep
  refine hpart.of_eq_tot fun fs => ?_
  refine mem_rfindOpt_of_sound (fun n b hn => ?_) ?_
  · obtain ⟨w, _, hw⟩ := Option.bind_eq_some_iff.mp hn
    exact hval fs w b hw
  · obtain ⟨w, b, hw⟩ := htotal fs
    refine ⟨@Encodable.encode _ Primcodable.toEncodable w, b, ?_⟩
    rw [@Encodable.encodek _ Primcodable.toEncodable w]
    simpa using hw

/-- Rabin Lemma 5 (`rabin.tex`:336-343), countable-variable computable form.
Finite input lists in the full ring `F[x₀,x₁,…]` admitting a Bezout
certificate form a computable predicate.  The proof uniformly computes a
finite level containing the input variables, then uses the same audited
positive-certificate/negative-candidate search as the finite-variable theorem. -/
theorem computablePred_exists_certificate_nat
    [Field F] [Primcodable F] [ComputableField F] [PerfectField F] :
    ComputablePred fun fs : List (MvPolynomial ℕ F) =>
      ∃ rs : List (MvPolynomial ℕ F), rs.length = fs.length ∧
        (List.zipWith (· * ·) rs fs).sum = 1 := by
  classical
  refine computablePred_of_rabinCheckNat (F := F) ?_ ?_
  · rintro fs (rs | ⟨p, gs⟩) b hw
    · simp only [rabinCheckNat, Sum.elim_inl, Option.ite_none_right_eq_some,
        Option.some.injEq] at hw
      obtain ⟨hrs, hb⟩ := hw
      subst hb
      exact ⟨fun _ => ⟨rs, hrs⟩, fun _ => rfl⟩
    · simp only [rabinCheckNat, Sum.elim_inr, Option.ite_none_right_eq_some,
        Option.some.injEq] at hw
      obtain ⟨hcand, hb⟩ := hw
      subst hb
      constructor
      · intro hfalse
        cases hfalse
      · intro hcert
        have hno :=
          (one_mem_span_nat_iff_no_common_zero (F := F) fs
            (fun h hh => level_le_levelMax_of_mem (F := F) hh)).mp hcert
        exfalso
        exact hno (candidatePredNat_common_zero (F := F) fs hcand)
  · intro fs
    by_cases hcert :
      ∃ rs : List (MvPolynomial ℕ F), rs.length = fs.length ∧
        (List.zipWith (· * ·) rs fs).sum = 1
    · obtain ⟨rs, hrs⟩ := hcert
      refine ⟨Sum.inl rs, true, ?_⟩
      simp [rabinCheckNat, certificatePredNat, hrs]
    · let m := levelMax (F := F) fs
      let fsR := fs.map (MvPolynomialNat.restrictLevel (F := F) m)
      have hzero :
          ∃ ξ : Fin m → AlgebraicClosure F,
            ∀ h ∈ fsR, MvPolynomial.aeval ξ h = 0 := by
        exact not_not.mp (mt
          (one_mem_span_nat_iff_no_common_zero (F := F) fs
            (fun h hh => level_le_levelMax_of_mem (F := F) hh)).mpr hcert)
      let f : Fin fsR.length → MvPolynomial (Fin m) F := fun i => fsR[i]
      have hzeroFin :
          ∃ ξ : Fin m → AlgebraicClosure F, ∀ i, MvPolynomial.aeval ξ (f i) = 0 := by
        obtain ⟨ξ, hξ⟩ := hzero
        exact ⟨ξ, fun i => hξ (f i) (List.getElem_mem i.isLt)⟩
      obtain ⟨p, g, hmonic, hdeg, hdiv⟩ := candidate_of_common_zero f hzeroFin
      refine ⟨Sum.inr (p, List.ofFn g), false, ?_⟩
      have hcand : candidatePredNat fs (p, List.ofFn g) := by
        exact candidatePredNat_of_candidate (F := F) fs hmonic hdeg hdiv
      simp [rabinCheckNat, hcand]

/-- Rabin Lemma 5 (`rabin.tex`:336-343), countable-variable ideal-span form. -/
theorem computablePred_one_mem_span_nat
    [Field F] [Primcodable F] [ComputableField F] [PerfectField F] :
    ComputablePred fun fs : List (MvPolynomial ℕ F) =>
      (1 : MvPolynomial ℕ F) ∈ Ideal.span {g | g ∈ fs} := by
  classical
  exact (computablePred_exists_certificate_nat (F := F)).of_eq fun fs =>
    (one_mem_span_iff_list_certificate (fs := fs)).symm

example :
    ComputablePred fun fs : List (MvPolynomial ℕ ℚ) =>
      ∃ rs : List (MvPolynomial ℕ ℚ), rs.length = fs.length ∧
        (List.zipWith (· * ·) rs fs).sum = 1 :=
  computablePred_exists_certificate_nat (F := ℚ)

example :
    ComputablePred fun fs : List (MvPolynomial ℕ ℚ) =>
      (1 : MvPolynomial ℕ ℚ) ∈ Ideal.span {g | g ∈ fs} :=
  computablePred_one_mem_span_nat (F := ℚ)

end NatSearch

end Semicontinuity
