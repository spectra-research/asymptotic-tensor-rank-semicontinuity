/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.IdealTriviality
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.MvPolynomialComputable
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.CheckerComputable
import Mathlib.Data.Set.List

/-!
# Rabin Lemma 5: computable ideal triviality

Rabin Lemma 5 (Rabin 1960, `rabin.tex`:336-343) states:
"The set `U` of all finite sequences `(f₁,…,fₙ)`, `fᵢ ∈ R`, for which there
exists a solution `r₁ ∈ R,…,rₙ ∈ R` of the equation
`r₁f₁+⋯+rₙfₙ=1` is a recursive set (with respect to `i`)."

This file proves the finite-`m`-variables version.  This is the audited
deviation D1: the decision procedure is a sound total parallel search over
positive Bezout certificates and negative Rabin candidates, rather than
Rabin's elimination-theoretic search.  Soundness of the negative branch is
`common_zero_of_candidate`; completeness is Nullstellensatz C1 plus
`candidate_of_common_zero`, under `[PerfectField F]`.  Rabin's characteristic
zero/explicit-elimination setting is thereby generalized to perfect computable
fields.  The full ring `F[x₁,x₂,…]` is reserved for Phase D's fresh-variables
reduction.
-/

noncomputable section

universe u

namespace Semicontinuity

open Polynomial

variable {F : Type u} [Field F]

private abbrev RabinWitness (m : ℕ) (F : Type u) [Field F] :=
  List (MvPolynomial (Fin m) F) ⊕ (Polynomial F × List (Polynomial F))

private def certificatePred {m : ℕ} (fs rs : List (MvPolynomial (Fin m) F)) : Prop :=
  rs.length = fs.length ∧ (List.zipWith (· * ·) rs fs).sum = 1

private def candidatePred {m : ℕ} (fs : List (MvPolynomial (Fin m) F))
    (w : Polynomial F × List (Polynomial F)) : Prop :=
  w.1.leadingCoeff = 1 ∧ 1 ≤ w.1.natDegree ∧
    ∀ h ∈ fs,
      (MvPolynomial.eval (fun j : Fin m => w.2.getD j 0)
        (MvPolynomial.map Polynomial.C h)) % w.1 = 0

open Classical in
private def rabinCheck {m : ℕ} (fs : List (MvPolynomial (Fin m) F))
    (w : RabinWitness m F) : Option Bool :=
  Sum.elim
    (fun rs =>
      if certificatePred fs rs then some true else none)
    (fun z =>
      if candidatePred fs z then some false else none) w

section Computability

variable [Primcodable F] [ComputableField F]

private theorem computable_decide_nat_le :
    Computable₂ fun a b : ℕ => decide (a ≤ b) := by
  exact Primrec.nat_le.decide.to_comp

set_option linter.flexible false in
open Classical in
private theorem computable_certificatePred (m : ℕ) :
    Computable₂ fun fs rs : List (MvPolynomial (Fin m) F) =>
      decide (certificatePred fs rs) := by
  let P := MvPolynomial (Fin m) F
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
    computable_list_sum.comp hzip
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
      · simp [certificatePred, h₁, h₂]
        exact h₂
      · simp [certificatePred, h₁, h₂]
        exact h₂
    · simp [certificatePred, h₁]

set_option linter.flexible false in
open Classical in
private theorem computable_candidatePred (m : ℕ) :
    Computable₂ fun fs : List (MvPolynomial (Fin m) F) =>
      fun w : Polynomial F × List (Polynomial F) => decide (candidatePred fs w) := by
  let P := MvPolynomial (Fin m) F
  let Q := Polynomial F
  let MP := MvPolynomial (Fin m) Q
  have hlead : Computable fun x : List P × (Q × List Q) =>
      decide (x.2.1.leadingCoeff = (1 : F)) :=
    computable_decide_eq.comp (computable_poly_leadingCoeff.comp
      (Computable.fst.comp Computable.snd)) (Computable.const 1)
  have hdeg : Computable fun x : List P × (Q × List Q) =>
      decide (1 ≤ x.2.1.natDegree) :=
    computable_decide_nat_le.comp (Computable.const 1)
      (computable_poly_natDegree.comp (Computable.fst.comp Computable.snd))
  have hmapC : Computable fun h : P => (MvPolynomial.map Polynomial.C h : MP) :=
    computable_mvPolynomial_map F m Polynomial.C computable_poly_C
  have heval : Computable fun y : (List P × (Q × List Q)) × P =>
      MvPolynomial.eval (fun j : Fin m => y.1.2.2.getD j 0)
        (MvPolynomial.map Polynomial.C y.2) :=
    (computable₂_mvPolynomial_eval Q m).comp
      (Computable.snd.comp (Computable.snd.comp Computable.fst))
      (hmapC.comp Computable.snd)
  have hmod : Computable fun y : (List P × (Q × List Q)) × P =>
      (MvPolynomial.eval (fun j : Fin m => y.1.2.2.getD j 0)
        (MvPolynomial.map Polynomial.C y.2)) % y.1.2.1 :=
    computable₂_poly_mod.comp heval (Computable.fst.comp (Computable.snd.comp Computable.fst))
  have hzero : Computable₂ fun x : List P × (Q × List Q) => fun h : P =>
      decide (((MvPolynomial.eval (fun j : Fin m => x.2.2.getD j 0)
        (MvPolynomial.map Polynomial.C h)) % x.2.1) = (0 : Q)) :=
    (computable_decide_eq.comp hmod (Computable.const 0)).to₂
  have hall : Computable fun x : List P × (Q × List Q) =>
      x.1.all fun h =>
        decide (((MvPolynomial.eval (fun j : Fin m => x.2.2.getD j 0)
          (MvPolynomial.map Polynomial.C h)) % x.2.1) = (0 : Q)) :=
    Computable.list_all Computable.fst hzero
  have hcond : Computable fun x : List P × (Q × List Q) =>
      (decide (x.2.1.leadingCoeff = (1 : F)) &&
        decide (1 ≤ x.2.1.natDegree)) && x.1.all fun h =>
          decide (((MvPolynomial.eval (fun j : Fin m => x.2.2.getD j 0)
            (MvPolynomial.map Polynomial.C h)) % x.2.1) = (0 : Q)) :=
    Primrec.and.to_comp.comp (Primrec.and.to_comp.comp hlead hdeg) hall
  exact hcond.to₂.of_eq fun x => by
    rcases x with ⟨fs, p, gs⟩
    dsimp
    by_cases h₁ : p.leadingCoeff = (1 : F)
    · by_cases h₂ : 1 ≤ p.natDegree
      · have hall :
          (fs.all fun h =>
            decide (((MvPolynomial.eval (fun j : Fin m => gs.getD j 0)
              (MvPolynomial.map Polynomial.C h)) % p) = (0 : Q))) =
            decide (∀ h ∈ fs,
              ((MvPolynomial.eval (fun j : Fin m => gs.getD j 0)
                (MvPolynomial.map Polynomial.C h)) % p) = (0 : Q)) := by
          by_cases h₃ : ∀ h ∈ fs,
              ((MvPolynomial.eval (fun j : Fin m => gs.getD j 0)
                (MvPolynomial.map Polynomial.C h)) % p) = (0 : Q)
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
        simp [candidatePred, h₁, h₂]
        by_cases h₃ : ∀ h ∈ fs,
            p ∣ MvPolynomial.eval₂ Polynomial.C
              (fun j : Fin m => gs[j.val]?.getD 0) h
        · rw [decide_eq_true h₃]
          rw [List.all_eq_true]
          intro h hh
          exact decide_eq_true (by
            rw [← MvPolynomial.eval₂_eq_eval_map]
            exact h₃ h hh)
        · rw [decide_eq_false h₃]
          rw [List.all_eq_false]
          rw [not_forall] at h₃
          obtain ⟨h, hh⟩ := h₃
          rw [not_forall] at hh
          obtain ⟨hm, hhm⟩ := hh
          refine ⟨h, hm, ?_⟩
          intro htrue
          apply hhm
          rw [MvPolynomial.eval₂_eq_eval_map]
          exact of_decide_eq_true htrue
      · simp [candidatePred, h₁, h₂]
    · simp [candidatePred, h₁]

open Classical in
private theorem computable_rabinCheck (m : ℕ) :
    Computable₂ (rabinCheck (F := F) (m := m)) := by
  let P := MvPolynomial (Fin m) F
  let W := RabinWitness m F
  let WR := Polynomial F × List (Polynomial F)
  have hleft : Computable₂ fun p : List P × W => fun rs : List P =>
      if certificatePred p.1 rs then some true else none := by
    have hcond : Computable fun q : (List P × W) × List P =>
        decide (certificatePred q.1.1 q.2) :=
      (computable_certificatePred (F := F) m).comp (Computable.fst.comp Computable.fst)
        Computable.snd
    exact ((Computable.cond hcond (Computable.const (some true))
      (Computable.const Option.none)).to₂).of_eq fun q => by
        rcases q with ⟨p, rs⟩
        by_cases h : certificatePred p.1 rs <;> simp [h]
  have hright : Computable₂ fun p : List P × W => fun z : WR =>
      if candidatePred p.1 z then some false else none := by
    have hcond : Computable fun q : (List P × W) × WR =>
        decide (candidatePred q.1.1 q.2) :=
      (computable_candidatePred (F := F) m).comp (Computable.fst.comp Computable.fst)
        Computable.snd
    exact ((Computable.cond hcond (Computable.const (some false))
      (Computable.const Option.none)).to₂).of_eq fun q => by
        rcases q with ⟨p, z⟩
        by_cases h : candidatePred p.1 z <;> simp [h]
  have hcases :=
    Computable.sumCasesOn (Computable.snd : Computable (fun p : List P × W => p.2))
      hleft hright
  exact hcases.to₂.of_eq fun xw => by
    rcases xw with ⟨fs, w⟩
    cases w <;> rfl

end Computability

section Math

private theorem aeval_eq_eval_map_C {m : ℕ} (g : Fin m → Polynomial F)
    (h : MvPolynomial (Fin m) F) :
    MvPolynomial.aeval g h = MvPolynomial.eval g (MvPolynomial.map Polynomial.C h) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map]
  rw [Polynomial.algebraMap_eq]

private theorem dvd_iff_mod_eq_zero (p h : Polynomial F) :
    p ∣ h ↔ h % p = 0 := by
  rw [EuclideanDomain.mod_eq_zero]

private theorem candidatePred_common_zero {m : ℕ} (fs : List (MvPolynomial (Fin m) F))
    {p : Polynomial F} {gs : List (Polynomial F)} (hw : candidatePred fs (p, gs)) :
    ∃ ξ : Fin m → AlgebraicClosure F, ∀ h ∈ fs, MvPolynomial.aeval ξ h = 0 := by
  let f : Fin fs.length → MvPolynomial (Fin m) F := fun i => fs[i]
  have hdiv : ∀ i, p ∣ MvPolynomial.aeval (fun j : Fin m => gs.getD j 0) (f i) := by
    intro i
    rw [aeval_eq_eval_map_C, dvd_iff_mod_eq_zero]
    exact hw.2.2 (f i) (List.getElem_mem i.isLt)
  obtain ⟨ξ, hξ⟩ :=
    common_zero_of_candidate f p hw.1 hw.2.1 (fun j : Fin m => gs.getD j 0) hdiv
  refine ⟨ξ, ?_⟩
  intro h hh
  rw [List.mem_iff_get] at hh
  obtain ⟨i, rfl⟩ := hh
  exact hξ i

private theorem candidatePred_of_candidate {m : ℕ} (fs : List (MvPolynomial (Fin m) F))
    {p : Polynomial F} {g : Fin m → Polynomial F}
    (hmonic : p.Monic) (hdeg : 1 ≤ p.natDegree)
    (hdiv : ∀ i : Fin fs.length, p ∣ MvPolynomial.aeval g fs[i]) :
    candidatePred fs (p, List.ofFn g) := by
  refine ⟨hmonic, hdeg, ?_⟩
  intro h hh
  rw [List.mem_iff_get] at hh
  obtain ⟨i, rfl⟩ := hh
  rw [← dvd_iff_mod_eq_zero, ← aeval_eq_eval_map_C]
  convert hdiv i using 2
  ext j
  simp

private theorem span_list_set_eq_range_get {m : ℕ} (fs : List (MvPolynomial (Fin m) F)) :
    ({g | g ∈ fs} : Set (MvPolynomial (Fin m) F)) = Set.range fs.get := by
  rw [Set.range_list_get]

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

private theorem one_mem_span_iff_certificate {m : ℕ} (fs : List (MvPolynomial (Fin m) F)) :
    (1 : MvPolynomial (Fin m) F) ∈ Ideal.span {g | g ∈ fs} ↔
      ∃ rs : List (MvPolynomial (Fin m) F), certificatePred fs rs := by
  rw [span_list_set_eq_range_get fs]
  change (1 : MvPolynomial (Fin m) F) ∈
      Ideal.span (Set.range fun i : Fin fs.length => fs[i]) ↔
    ∃ rs : List (MvPolynomial (Fin m) F), certificatePred fs rs
  rw [one_mem_span_iff_no_common_zero (F := F) (fun i : Fin fs.length => fs[i])]
  rw [common_zero_get_iff_common_zero_mem (F := F) fs]
  exact (exists_certificate_list_iff (F := F) fs).symm

end Math

section Search

variable [Primcodable F] [ComputableField F] [PerfectField F]

set_option linter.unusedSectionVars false

private theorem computablePred_of_rabinCheck (m : ℕ)
    {p : List (MvPolynomial (Fin m) F) → Prop}
    (hsound : ∀ (fs : List (MvPolynomial (Fin m) F)) (w : RabinWitness m F) (b : Bool),
      rabinCheck fs w = some b → (b = true ↔ p fs))
    (htotal : ∀ fs : List (MvPolynomial (Fin m) F), ∃ (w : RabinWitness m F) (b : Bool),
      rabinCheck fs w = some b) :
    ComputablePred p := by
  classical
  refine ⟨fun _ => Classical.propDecidable _, ?_⟩
  have hval : ∀ (fs : List (MvPolynomial (Fin m) F)) (w : RabinWitness m F) (b : Bool),
      rabinCheck fs w = some b → b = decide (p fs) := by
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
    Computable.bind_decode_iff.mpr (computable_rabinCheck (F := F) m)
  have hpart := Partrec.rfindOpt hstep
  refine hpart.of_eq_tot fun fs => ?_
  refine mem_rfindOpt_of_sound (fun n b hn => ?_) ?_
  · obtain ⟨w, _, hw⟩ := Option.bind_eq_some_iff.mp hn
    exact hval fs w b hw
  · obtain ⟨w, b, hw⟩ := htotal fs
    refine ⟨@Encodable.encode _ Primcodable.toEncodable w, b, ?_⟩
    rw [@Encodable.encodek _ Primcodable.toEncodable w]
    simpa using hw

/-- Rabin Lemma 5 (`rabin.tex`:336-343), finite-variable computable form.
For fixed `m`, the finite sequences `(f₁,…,fₙ)` of polynomials in
`F[x₀,…,x_{m-1}]` admitting a Bezout certificate
`r₁f₁+⋯+rₙfₙ=1` form a computable predicate.

This is the finite-`m` scope of Rabin's recursiveness claim.  The search used
here replaces Rabin's explicit elimination procedure by the audited D1
parallel search: positive certificates are checked directly; negative
candidates are sound by `common_zero_of_candidate` and complete by C1
Nullstellensatz plus `candidate_of_common_zero` over perfect computable fields.
-/
theorem computablePred_exists_certificate (m : ℕ)
    [Field F] [Primcodable F] [ComputableField F] [PerfectField F] :
    ComputablePred fun fs : List (MvPolynomial (Fin m) F) =>
      ∃ rs : List (MvPolynomial (Fin m) F), rs.length = fs.length ∧
        (List.zipWith (· * ·) rs fs).sum = 1 := by
  classical
  refine computablePred_of_rabinCheck (F := F) m ?_ ?_
  · rintro fs (rs | ⟨p, gs⟩) b hw
    · simp only [rabinCheck, Sum.elim_inl, Option.ite_none_right_eq_some,
        Option.some.injEq] at hw
      obtain ⟨hrs, hb⟩ := hw
      subst hb
      exact ⟨fun _ => ⟨rs, hrs⟩, fun _ => rfl⟩
    · simp only [rabinCheck, Sum.elim_inr, Option.ite_none_right_eq_some,
        Option.some.injEq] at hw
      obtain ⟨hcand, hb⟩ := hw
      subst hb
      constructor
      · intro hfalse
        cases hfalse
      · intro hcert
        have hno := (exists_certificate_list_iff (F := F) fs).mp hcert
        exfalso
        exact hno (candidatePred_common_zero fs hcand)
  · intro fs
    by_cases hcert :
      ∃ rs : List (MvPolynomial (Fin m) F), rs.length = fs.length ∧
        (List.zipWith (· * ·) rs fs).sum = 1
    · obtain ⟨rs, hrs⟩ := hcert
      refine ⟨Sum.inl rs, true, ?_⟩
      simp [rabinCheck, certificatePred, hrs]
    · have hzero :
        ∃ ξ : Fin m → AlgebraicClosure F, ∀ h ∈ fs, MvPolynomial.aeval ξ h = 0 := by
        exact not_not.mp (mt (exists_certificate_list_iff (F := F) fs).mpr hcert)
      let f : Fin fs.length → MvPolynomial (Fin m) F := fun i => fs[i]
      have hzeroFin :
          ∃ ξ : Fin m → AlgebraicClosure F, ∀ i, MvPolynomial.aeval ξ (f i) = 0 := by
        obtain ⟨ξ, hξ⟩ := hzero
        exact ⟨ξ, fun i => hξ (f i) (List.getElem_mem i.isLt)⟩
      obtain ⟨p, g, hmonic, hdeg, hdiv⟩ := candidate_of_common_zero f hzeroFin
      refine ⟨Sum.inr (p, List.ofFn g), false, ?_⟩
      have hcand : candidatePred fs (p, List.ofFn g) :=
        candidatePred_of_candidate fs hmonic hdeg hdiv
      simp [rabinCheck, hcand]

/-- Rabin Lemma 5 (`rabin.tex`:336-343), finite-variable ideal-span form. -/
theorem computablePred_one_mem_span (m : ℕ)
    [Field F] [Primcodable F] [ComputableField F] [PerfectField F] :
    ComputablePred fun fs : List (MvPolynomial (Fin m) F) =>
      (1 : MvPolynomial (Fin m) F) ∈ Ideal.span {g | g ∈ fs} := by
  classical
  exact (computablePred_exists_certificate (F := F) m).of_eq fun fs =>
    (one_mem_span_iff_certificate (F := F) fs).symm

example (m : ℕ) :
    ComputablePred fun fs : List (MvPolynomial (Fin m) ℚ) =>
      ∃ rs : List (MvPolynomial (Fin m) ℚ), rs.length = fs.length ∧
        (List.zipWith (· * ·) rs fs).sum = 1 :=
  computablePred_exists_certificate (F := ℚ) m

end Search

end Semicontinuity
