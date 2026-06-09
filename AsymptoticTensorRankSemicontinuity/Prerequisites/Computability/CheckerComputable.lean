/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.ComputableField
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.ListComputable
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Computable list-level checks for the algorithm of Theorem 1.1

The algorithm of Theorem 1.1 (arXiv:2411.15789, tex:313-318) receives a
`k`-tensor of arbitrary format coded as a dimension list together with the
list of its entries in little-endian mixed-radix order (the order of
`finPiFinEquiv`). This file provides the two checks the algorithm performs
on candidate witnesses, as `Bool`-valued functions on lists, and proves them
computable over a computable field:

* `restrictsCheckList`: that a candidate list of per-leg matrices witnesses
  a restriction between two coded tensors (the defining equation
  `S = (A₁ ⊗ ⋯ ⊗ A_k) T` of `Restricts`, checked entry by entry);
* `minorCheckList`: that a candidate list of `s` row indices and `s` column
  multi-indices selects an `s × s` submatrix of the `j`-th flattening with
  nonzero determinant (witnessing flattening rank `≥ s`).

All index arithmetic is primitive recursive; the field arithmetic uses the
`Computable`-level list closures from `ListComputable.lean`, and the
determinant is the evaluation of the fixed universal determinant polynomial
`(Matrix.mvPolynomialX _ _ F).det` (computable by
`ComputableField.computable_mvPolynomial_eval`).
-/

universe u

namespace Semicontinuity

variable {F : Type u} [Field F]

/-! ## Mixed-radix positions -/

/-- The `i`-th little-endian mixed-radix digit of a position `p`, for the
dimension list `dims`: `(p / (dims.take i).prod) % dims.getD i 1`. This is
the inverse formula of `finPiFinEquiv`. -/
def radixDigit (dims : List ℕ) (i p : ℕ) : ℕ :=
  (p / (dims.take i).prod) % dims.getD i 1

/-- The little-endian mixed-radix position of the multi-index whose leg-`j`
coordinate is `rv` and whose leg-`i` coordinate is `col.getD i 0` for
`i ≠ j` (matching `finPiFinEquiv`). -/
def posWithLeg (dims : List ℕ) (j rv : ℕ) (col : List ℕ) : ℕ :=
  ((List.range dims.length).map fun i =>
    (if i = j then rv else col.getD i 0) * (dims.take i).prod).sum

/-! ## Restriction check -/

open scoped Classical in
/-- Check that the per-leg matrices coded by `A` (leg `i` row-major in
`A.getD i []`, with `dT.getD i 1` columns) restrict the tensor coded by
`(dT, T)` to the tensor coded by `(dS, S)`: entrywise,
`S = (A₁ ⊗ ⋯ ⊗ A_k) T`. -/
noncomputable def restrictsCheckList (k : ℕ) (dS dT : List ℕ) (S T : List F)
    (A : List (List F)) : Bool :=
  (List.range S.length).all fun p => decide <|
    S.getD p 0 =
      ((List.range T.length).map fun q =>
        ((List.range k).map fun i =>
          (A.getD i []).getD
            (radixDigit dS i p * dT.getD i 1 + radixDigit dT i q) 0).prod
        * T.getD q 0).sum

/-! ## Minor check -/

/-- The `s × s` matrix assembled from the coded tensor `(dT, T)` by selecting,
in the `j`-th flattening, the rows `rows.getD a 0` and the column
multi-indices `cols.getD b []`. -/
def minorMatrixOfLists (s : ℕ) (dT : List ℕ) (T : List F) (j : ℕ)
    (rows : List ℕ) (cols : List (List ℕ)) : Matrix (Fin s) (Fin s) F :=
  Matrix.of fun a b =>
    T.getD (posWithLeg dT j (rows.getD (a : ℕ) 0) (cols.getD (b : ℕ) [])) 0

open scoped Classical in
/-- Check that `(j, rows, cols)` selects an `s × s` submatrix of the `j`-th
flattening of the coded tensor `(dT, T)` with nonzero determinant; includes
the range checks making the selection a genuine submatrix. -/
noncomputable def minorCheckList (k s : ℕ) (dT : List ℕ) (T : List F) (j : ℕ)
    (rows : List ℕ) (cols : List (List ℕ)) : Bool :=
  decide (j < k) &&
  ((List.range s).all fun a => decide (rows.getD a 0 < dT.getD j 1)) &&
  ((List.range s).all fun b => (List.range k).all fun i =>
    decide ((cols.getD b []).getD i 0 < dT.getD i 1)) &&
  decide ((minorMatrixOfLists (F := F) s dT T j rows cols).det ≠ 0)

/-! ## Computability -/

section Computability

variable [Primcodable F] [ComputableField F]
variable {α : Type*} [Primcodable α]

/-- Square matrices over `F` are coded entrywise (`Matrix` is a type synonym
for the function type). -/
instance instPrimcodableMatrixFin (s : ℕ) :
    Primcodable (Matrix (Fin s) (Fin s) F) :=
  Primcodable.ofEquiv (Fin s → Fin s → F) (Matrix.of (m := Fin s)).symm

/-- Equality test (as a `Bool`) is computable on a `Primcodable` type: codes
are equal iff the elements are. The `Decidable` instance is irrelevant
(`Subsingleton (Decidable p)`). -/
theorem computable_decide_eq {β : Type*} [Primcodable β] [DecidableEq β] :
    Computable₂ fun a b : β => decide (a = b) := by
  exact Primrec.eq.decide.to_comp

private theorem foldl_range_getElem?_eq_take {β : Type*} (l : List β) :
    ∀ n (acc : List β),
      (List.range n).foldl
          (fun acc i => Option.casesOn (l[i]?) acc (fun b => acc ++ [b])) acc =
        acc ++ l.take n := by
  intro n
  induction n with
  | zero =>
      intro acc
      simp
  | succ n IH =>
      intro acc
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [IH]
      cases h : l[n]? with
      | none => simp [h, List.take_add_one]
      | some b => simp [h, List.take_add_one, List.append_assoc]

private theorem computable_list_take {β : Type*} [Primcodable β]
    {fl : α → List β} {fn : α → ℕ} (hl : Computable fl) (hn : Computable fn) :
    Computable fun a => (fl a).take (fn a) := by
  let step : α → List β × ℕ → List β :=
    fun a p => Option.casesOn ((fl a)[p.2]?) p.1 (fun b => p.1 ++ [b])
  have hstep : Computable₂ step := by
    have hopt : Computable fun x : α × (List β × ℕ) => (fl x.1)[x.2.2]? :=
      (@Computable.list_getElem? β _).comp (hl.comp Computable.fst)
        (Computable.snd.comp
          (Computable.snd : Computable (fun x : α × (List β × ℕ) => x.2)))
    have hnone : Computable fun x : α × (List β × ℕ) => x.2.1 :=
      Computable.fst.comp
        (Computable.snd : Computable (fun x : α × (List β × ℕ) => x.2))
    have hsome0 : Computable fun y : (α × (List β × ℕ)) × β => y.1.2.1 ++ [y.2] :=
      (@Computable.list_concat β _).comp
        (Computable.fst.comp
          (Computable.snd.comp
            (Computable.fst :
              Computable (fun y : (α × (List β × ℕ)) × β => y.1))))
        Computable.snd
    have hsome : Computable₂ fun (x : α × (List β × ℕ)) (b : β) => x.2.1 ++ [b] :=
      hsome0.to₂
    exact (Computable.option_casesOn hopt hnone hsome).to₂.of_eq fun x => by
      rcases x with ⟨a, p⟩
      rfl
  have hfold : Computable fun a =>
      (List.range (fn a)).foldl (fun acc i => step a (acc, i)) ([] : List β) :=
    Computable.list_foldl (Primrec.list_range.to_comp.comp hn) (Computable.const ([] : List β))
      hstep
  exact hfold.of_eq fun a => by
    simpa [step] using foldl_range_getElem?_eq_take (fl a) (fn a) ([] : List β)

private theorem computable_list_getD {β : Type*} [Primcodable β]
    (d : β) {fl : α → List β} {fn : α → ℕ}
    (hl : Computable fl) (hn : Computable fn) :
    Computable fun a => (fl a).getD (fn a) d := by
  rw [show (fun a => (fl a).getD (fn a) d) =
      (fun a => ((fl a)[fn a]?).getD d) by
    funext a
    simp [List.getD_eq_getElem?_getD]]
  exact Computable.option_getD
    ((@Computable.list_getElem? β _).comp hl hn) (Computable.const d)

private theorem computable_list_range_of_length {β : Type*} [Primcodable β]
    {fl : α → List β} (hl : Computable fl) :
    Computable fun a => List.range (fl a).length :=
  Primrec.list_range.to_comp.comp (Computable.list_length.comp hl)

private theorem computable_fin_ofFn {β : Type*} [Primcodable β] {n : ℕ}
    {f : α → Fin n → β} (hf : ∀ i, Computable fun a => f a i) :
    Computable fun a => (fun i => f a i : Fin n → β) := by
  have hv : Computable fun a => List.Vector.ofFn fun i => f a i :=
    Computable.vector_ofFn (fun i => hf i)
  exact Computable.encode_iff.mp ((Computable.encode.comp hv).of_eq fun _ => rfl)

private theorem computable_sum_range {fN : α → ℕ} {fg : α → ℕ → F}
    (hN : Computable fN) (hg : Computable₂ fg) :
    Computable fun a => ((List.range (fN a)).map (fg a)).sum :=
  Computable.list_sum ComputableField.computable_add
    (Computable.list_map (Primrec.list_range.to_comp.comp hN) hg)

private theorem computable_prod_range {fN : α → ℕ} {fg : α → ℕ → F}
    (hN : Computable fN) (hg : Computable₂ fg) :
    Computable fun a => ((List.range (fN a)).map (fg a)).prod :=
  Computable.list_prod ComputableField.computable_mul
    (Computable.list_map (Primrec.list_range.to_comp.comp hN) hg)

private theorem computable_nat_sum_range {fN : α → ℕ} {fg : α → ℕ → ℕ}
    (hN : Computable fN) (hg : Computable₂ fg) :
    Computable fun a => ((List.range (fN a)).map (fg a)).sum :=
  Computable.list_sum Primrec.nat_add.to_comp
    (Computable.list_map (Primrec.list_range.to_comp.comp hN) hg)

private theorem computable_nat_prod {fl : α → List ℕ} (hl : Computable fl) :
    Computable fun a => (fl a).prod :=
  Computable.list_prod Primrec.nat_mul.to_comp hl

private theorem computable_radixDigit {fdims : α → List ℕ} {fi fp : α → ℕ}
    (hdims : Computable fdims) (hi : Computable fi) (hp : Computable fp) :
    Computable fun a => radixDigit (fdims a) (fi a) (fp a) := by
  have htake : Computable fun a => (fdims a).take (fi a) :=
    computable_list_take hdims hi
  have hprod : Computable fun a => ((fdims a).take (fi a)).prod :=
    computable_nat_prod htake
  have hdiv : Computable fun a => fp a / ((fdims a).take (fi a)).prod :=
    Primrec.nat_div.to_comp.comp hp hprod
  have hget : Computable fun a => (fdims a).getD (fi a) 1 :=
    computable_list_getD 1 hdims hi
  exact (Primrec.nat_mod.to_comp.comp hdiv hget).of_eq fun _ => rfl

private theorem computable_posWithLeg {fdims : α → List ℕ} {fj frv : α → ℕ}
    {fcol : α → List ℕ} (hdims : Computable fdims) (hj : Computable fj)
    (hrv : Computable frv) (hcol : Computable fcol) :
    Computable fun a => posWithLeg (fdims a) (fj a) (frv a) (fcol a) := by
  let term : α → ℕ → ℕ := fun a i =>
    (if i = fj a then frv a else (fcol a).getD i 0) * ((fdims a).take i).prod
  have hterm : Computable₂ term := by
    have heq : Computable fun x : α × ℕ => decide (x.2 = fj x.1) :=
      (computable_decide_eq (β := ℕ)).comp Computable.snd (hj.comp Computable.fst)
    have hchoice : Computable fun x : α × ℕ =>
        if x.2 = fj x.1 then frv x.1 else (fcol x.1).getD x.2 0 := by
      exact (Computable.cond heq (hrv.comp Computable.fst)
        (computable_list_getD 0 (hcol.comp Computable.fst) Computable.snd)).of_eq fun x => by
          by_cases h : x.2 = fj x.1 <;> simp [h]
    have htake : Computable fun x : α × ℕ => (fdims x.1).take x.2 :=
      computable_list_take (hdims.comp Computable.fst) Computable.snd
    have hprod : Computable fun x : α × ℕ => ((fdims x.1).take x.2).prod :=
      computable_nat_prod htake
    exact (Primrec.nat_mul.to_comp.comp hchoice hprod).to₂.of_eq fun x => by
      rcases x with ⟨a, i⟩
      rfl
  have hlen : Computable fun a => (fdims a).length :=
    Computable.list_length.comp hdims
  exact (computable_nat_sum_range hlen hterm).of_eq fun a => by
    simp [posWithLeg, term]

/-- `restrictsCheckList` is computable in all five list arguments. -/
theorem computable_restrictsCheckList (k : ℕ)
    {fdS fdT : α → List ℕ} {fS fT : α → List F} {fA : α → List (List F)}
    (hdS : Computable fdS) (hdT : Computable fdT)
    (hS : Computable fS) (hT : Computable fT) (hA : Computable fA) :
    Computable fun a =>
      restrictsCheckList k (fdS a) (fdT a) (fS a) (fT a) (fA a) := by
  classical
  let legTerm : ((α × ℕ) × ℕ) → ℕ → F := fun y i =>
    (fA y.1.1).getD i [] |>.getD
      (radixDigit (fdS y.1.1) i y.1.2 * (fdT y.1.1).getD i 1 +
        radixDigit (fdT y.1.1) i y.2) 0
  have hlegTerm : Computable₂ legTerm := by
    have hmat : Computable fun x : (((α × ℕ) × ℕ) × ℕ) =>
        (fA x.1.1.1).getD x.2 [] :=
      computable_list_getD ([] : List F)
        (hA.comp
          (Computable.fst.comp
            (Computable.fst.comp
              (Computable.fst : Computable (fun x : (((α × ℕ) × ℕ) × ℕ) => x.1)))))
        Computable.snd
    have hdigitS : Computable fun x : (((α × ℕ) × ℕ) × ℕ) =>
        radixDigit (fdS x.1.1.1) x.2 x.1.1.2 :=
      computable_radixDigit
        (hdS.comp
          (Computable.fst.comp
            (Computable.fst.comp
              (Computable.fst : Computable (fun x : (((α × ℕ) × ℕ) × ℕ) => x.1)))))
        Computable.snd
        (Computable.snd.comp
          (Computable.fst.comp
            (Computable.fst : Computable (fun x : (((α × ℕ) × ℕ) × ℕ) => x.1)))
          : Computable (fun x : (((α × ℕ) × ℕ) × ℕ) => x.1.1.2))
    have hcols : Computable fun x : (((α × ℕ) × ℕ) × ℕ) =>
        (fdT x.1.1.1).getD x.2 1 :=
      computable_list_getD 1
        (hdT.comp
          (Computable.fst.comp
            (Computable.fst.comp
              (Computable.fst : Computable (fun x : (((α × ℕ) × ℕ) × ℕ) => x.1)))))
        Computable.snd
    have hdigitT : Computable fun x : (((α × ℕ) × ℕ) × ℕ) =>
        radixDigit (fdT x.1.1.1) x.2 x.1.2 :=
      computable_radixDigit
        (hdT.comp
          (Computable.fst.comp
            (Computable.fst.comp
              (Computable.fst : Computable (fun x : (((α × ℕ) × ℕ) × ℕ) => x.1)))))
        Computable.snd
        (Computable.snd.comp
          (Computable.fst : Computable (fun x : (((α × ℕ) × ℕ) × ℕ) => x.1)))
    have hidx : Computable fun x : (((α × ℕ) × ℕ) × ℕ) =>
        radixDigit (fdS x.1.1.1) x.2 x.1.1.2 * (fdT x.1.1.1).getD x.2 1 +
          radixDigit (fdT x.1.1.1) x.2 x.1.2 :=
      Primrec.nat_add.to_comp.comp
        (Primrec.nat_mul.to_comp.comp hdigitS hcols) hdigitT
    exact (computable_list_getD 0 hmat hidx).to₂.of_eq fun x => by
      rcases x with ⟨⟨⟨a, p⟩, q⟩, i⟩
      rfl
  let qTerm : α × ℕ → ℕ → F := fun x q =>
    ((List.range k).map (legTerm (x, q))).prod * (fT x.1).getD q 0
  have hqTerm : Computable₂ qTerm := by
    have hprod : Computable fun y : (α × ℕ) × ℕ =>
        ((List.range k).map (legTerm y)).prod :=
      computable_prod_range (Computable.const k) hlegTerm
    have hTget : Computable fun y : (α × ℕ) × ℕ => (fT y.1.1).getD y.2 0 :=
      computable_list_getD 0
        (hT.comp
          (Computable.fst.comp
            (Computable.fst : Computable (fun y : (α × ℕ) × ℕ => y.1))))
        Computable.snd
    exact (ComputableField.computable_mul.comp hprod hTget).to₂.of_eq fun y => by
      rcases y with ⟨⟨a, p⟩, q⟩
      rfl
  let pCheck : α → ℕ → Bool := fun a p =>
    decide <| (fS a).getD p 0 =
      ((List.range (fT a).length).map (qTerm (a, p))).sum
  have hpCheck : Computable₂ pCheck := by
    have hlhs : Computable fun x : α × ℕ => (fS x.1).getD x.2 0 :=
      computable_list_getD 0 (hS.comp Computable.fst) Computable.snd
    have hlenT : Computable fun x : α × ℕ => (fT x.1).length :=
      Computable.list_length.comp (hT.comp Computable.fst)
    have hrhs : Computable fun x : α × ℕ =>
        ((List.range (fT x.1).length).map (qTerm x)).sum :=
      computable_sum_range hlenT hqTerm
    exact ((computable_decide_eq (β := F)).comp hlhs hrhs).to₂.of_eq fun x => by
      rcases x with ⟨a, p⟩
      rfl
  have hall : Computable fun a => (List.range (fS a).length).all (pCheck a) :=
    Computable.list_all (computable_list_range_of_length hS) hpCheck
  exact hall.of_eq fun a => by
    simp [restrictsCheckList, pCheck, qTerm, legTerm]

/-- Assembling an `s × s` matrix over `F` from its (row-major) list of rows
is computable. -/
theorem computable_minorMatrixOfLists (s : ℕ)
    {fdT : α → List ℕ} {fT : α → List F} {fj : α → ℕ}
    {frows : α → List ℕ} {fcols : α → List (List ℕ)}
    (hdT : Computable fdT) (hT : Computable fT) (hj : Computable fj)
    (hrows : Computable frows) (hcols : Computable fcols) :
    Computable fun a =>
      minorMatrixOfLists (F := F) s (fdT a) (fT a) (fj a) (frows a)
        (fcols a) := by
  have _hfield : Computable₂ ((· + ·) : F → F → F) := ComputableField.computable_add
  let entry : α → Fin s → Fin s → F := fun x a b =>
    (fT x).getD
      (posWithLeg (fdT x) (fj x) ((frows x).getD (a : ℕ) 0)
        ((fcols x).getD (b : ℕ) [])) 0
  have hentry : ∀ a b, Computable fun x => entry x a b := by
    intro a b
    have hrow : Computable fun x => (frows x).getD (a : ℕ) 0 :=
      computable_list_getD 0 hrows (Computable.const (a : ℕ))
    have hcol : Computable fun x => (fcols x).getD (b : ℕ) [] :=
      computable_list_getD ([] : List ℕ) hcols (Computable.const (b : ℕ))
    have hpos : Computable fun x =>
        posWithLeg (fdT x) (fj x) ((frows x).getD (a : ℕ) 0)
          ((fcols x).getD (b : ℕ) []) :=
      computable_posWithLeg hdT hj hrow hcol
    exact (computable_list_getD 0 hT hpos).of_eq fun _ => rfl
  have hfun : Computable fun x => (fun a b => entry x a b : Fin s → Fin s → F) :=
    computable_fin_ofFn fun a => computable_fin_ofFn fun b => hentry a b
  have hmatrix : Computable fun x => Matrix.of fun a b => entry x a b :=
    Computable.encode_iff.mp ((Computable.encode.comp hfun).of_eq fun _ => rfl)
  exact hmatrix.of_eq fun x => by
    simp [minorMatrixOfLists, entry]

/-- The determinant of an `s × s` matrix over a computable field is
computable: it is the evaluation of the fixed universal determinant
polynomial `(Matrix.mvPolynomialX _ _ F).det` at the matrix entries. -/
theorem computable_det (s : ℕ) :
    Computable fun M : Matrix (Fin s) (Fin s) F => M.det := by
  classical
  let entryVec : Matrix (Fin s) (Fin s) F → Fin (s * s) → F := fun M x =>
    M (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2
  have hentry : ∀ x, Computable fun M : Matrix (Fin s) (Fin s) F => entryVec M x := by
    intro x
    have hrow : Computable fun M : Matrix (Fin s) (Fin s) F =>
        M (finProdFinEquiv.symm x).1 :=
      Computable.fin_app.comp
        (Computable.id : Computable fun M : Matrix (Fin s) (Fin s) F => M)
        (Computable.const (finProdFinEquiv.symm x).1)
    exact ((Computable.fin_app.comp hrow
      (Computable.const (finProdFinEquiv.symm x).2)).of_eq fun _ => rfl)
  have hvec : Computable fun M : Matrix (Fin s) (Fin s) F =>
      (fun x => entryVec M x : Fin (s * s) → F) :=
    computable_fin_ofFn hentry
  let q : MvPolynomial (Fin (s * s)) F :=
    MvPolynomial.rename (finProdFinEquiv : Fin s × Fin s ≃ Fin (s * s))
      (Matrix.det (Matrix.mvPolynomialX (Fin s) (Fin s) F))
  have heval : Computable fun v : Fin (s * s) → F => MvPolynomial.eval v q :=
    ComputableField.computable_mvPolynomial_eval q
  exact (heval.comp hvec).of_eq fun M => by
    dsimp [q, entryVec]
    rw [MvPolynomial.eval_rename]
    have hv : ((fun x : Fin (s * s) => M x.divNat x.modNat) ∘
        (finProdFinEquiv : Fin s × Fin s ≃ Fin (s * s))) =
        fun p : Fin s × Fin s => M p.1 p.2 := by
      funext p
      exact congrArg (fun z : Fin s × Fin s => M z.1 z.2)
        (Equiv.symm_apply_apply finProdFinEquiv p)
    rw [hv, RingHom.map_det, Matrix.mvPolynomialX_mapMatrix_eval]

/-- `minorCheckList` is computable in all its data arguments. -/
theorem computable_minorCheckList (k s : ℕ)
    {fdT : α → List ℕ} {fT : α → List F} {fj : α → ℕ}
    {frows : α → List ℕ} {fcols : α → List (List ℕ)}
    (hdT : Computable fdT) (hT : Computable fT) (hj : Computable fj)
    (hrows : Computable frows) (hcols : Computable fcols) :
    Computable fun a =>
      minorCheckList (F := F) k s (fdT a) (fT a) (fj a) (frows a)
        (fcols a) := by
  classical
  let rowCheck : α → ℕ → Bool := fun a r =>
    decide ((frows a).getD r 0 < (fdT a).getD (fj a) 1)
  have hrowCheck : Computable₂ rowCheck := by
    have hrow : Computable fun x : α × ℕ => (frows x.1).getD x.2 0 :=
      computable_list_getD 0 (hrows.comp Computable.fst) Computable.snd
    have hdim : Computable fun x : α × ℕ => (fdT x.1).getD (fj x.1) 1 :=
      computable_list_getD 1 (hdT.comp Computable.fst) (hj.comp Computable.fst)
    exact ((Primrec.nat_lt.decide.to_comp.comp hrow hdim).to₂).of_eq fun x => by
      rcases x with ⟨a, r⟩
      rfl
  let colInner : α × ℕ → ℕ → Bool := fun x i =>
    decide (((fcols x.1).getD x.2 []).getD i 0 < (fdT x.1).getD i 1)
  have hcolInner : Computable₂ colInner := by
    have hcolList : Computable fun y : (α × ℕ) × ℕ => (fcols y.1.1).getD y.1.2 [] :=
      computable_list_getD ([] : List ℕ)
        (hcols.comp
          (Computable.fst.comp
            (Computable.fst : Computable (fun y : (α × ℕ) × ℕ => y.1))))
        (Computable.snd.comp
          (Computable.fst : Computable (fun y : (α × ℕ) × ℕ => y.1)))
    have hcolVal : Computable fun y : (α × ℕ) × ℕ =>
        ((fcols y.1.1).getD y.1.2 []).getD y.2 0 :=
      computable_list_getD 0 hcolList Computable.snd
    have hdim : Computable fun y : (α × ℕ) × ℕ => (fdT y.1.1).getD y.2 1 :=
      computable_list_getD 1
        (hdT.comp
          (Computable.fst.comp
            (Computable.fst : Computable (fun y : (α × ℕ) × ℕ => y.1))))
        Computable.snd
    exact ((Primrec.nat_lt.decide.to_comp.comp hcolVal hdim).to₂).of_eq fun y => by
      rcases y with ⟨⟨a, b⟩, i⟩
      rfl
  let colCheck : α → ℕ → Bool := fun a b =>
    (List.range k).all (colInner (a, b))
  have hcolCheck : Computable₂ colCheck := by
    have hinner : Computable fun x : α × ℕ => (List.range k).all (colInner x) :=
      Computable.list_all (Computable.const (List.range k)) hcolInner
    exact hinner.to₂.of_eq fun x => by
      rcases x with ⟨a, b⟩
      rfl
  have hjlt : Computable fun a => decide (fj a < k) :=
    Primrec.nat_lt.decide.to_comp.comp hj (Computable.const k)
  have hrowsAll : Computable fun a => (List.range s).all (rowCheck a) :=
    Computable.list_all (Computable.const (List.range s)) hrowCheck
  have hcolsAll : Computable fun a => (List.range s).all (colCheck a) :=
    Computable.list_all (Computable.const (List.range s)) hcolCheck
  have hmatrix : Computable fun a =>
      minorMatrixOfLists (F := F) s (fdT a) (fT a) (fj a) (frows a) (fcols a) :=
    computable_minorMatrixOfLists s hdT hT hj hrows hcols
  have hdet : Computable fun a =>
      (minorMatrixOfLists (F := F) s (fdT a) (fT a) (fj a) (frows a) (fcols a)).det :=
    (computable_det (F := F) s).comp hmatrix
  have hdetEqZero : Computable fun a =>
      decide ((minorMatrixOfLists (F := F) s (fdT a) (fT a) (fj a) (frows a) (fcols a)).det = 0) :=
    (computable_decide_eq (β := F)).comp hdet (Computable.const 0)
  have hdetNeZero : Computable fun a =>
      decide ((minorMatrixOfLists (F := F) s (fdT a) (fT a) (fj a) (frows a) (fcols a)).det ≠ 0) :=
    (Primrec.not.to_comp.comp hdetEqZero).of_eq fun a => by
      by_cases h :
        (minorMatrixOfLists (F := F) s (fdT a) (fT a) (fj a) (frows a) (fcols a)).det = 0
      · simp [h]
      · simp [h]
  have h12 : Computable fun a => decide (fj a < k) && (List.range s).all (rowCheck a) :=
    Primrec.and.to_comp.comp hjlt hrowsAll
  have h123 : Computable fun a =>
      (decide (fj a < k) && (List.range s).all (rowCheck a)) &&
        (List.range s).all (colCheck a) :=
    Primrec.and.to_comp.comp h12 hcolsAll
  have h1234 : Computable fun a =>
      ((decide (fj a < k) && (List.range s).all (rowCheck a)) &&
          (List.range s).all (colCheck a)) &&
        decide ((minorMatrixOfLists (F := F) s (fdT a) (fT a) (fj a)
          (frows a) (fcols a)).det ≠ 0) :=
    Primrec.and.to_comp.comp h123 hdetNeZero
  exact h1234.of_eq fun a => by
    simp [minorCheckList, rowCheck, colCheck, colInner]

end Computability

end Semicontinuity
