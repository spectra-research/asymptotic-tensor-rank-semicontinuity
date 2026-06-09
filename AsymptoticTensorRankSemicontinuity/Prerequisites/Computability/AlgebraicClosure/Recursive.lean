/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.AlgebraicClosure.GreedyProper
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.IdealTrivialityNat
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.PolynomialComputable

/-!
# Computability of Rabin's greedy acceptance `acceptU`

Rabin's Theorem 7 (`rabin.tex`:388-394) asserts that the regressive set `U` is
recursive, i.e. `acceptU : ℕ → Bool` is computable.  The greedy recursion is a
strong recursion whose stage step rebuilds the accepted prefix from a Boolean
history table, attaches the canonical-code guard `canonicalCode`, the current
generator `rCode j`, and the fresh Vieta prefix `gamma1Flat F (kBound …)`, then
tests properness with the (classically defined) `properTest`.

This file proves `Computable (acceptU (F := F))` by mirroring the finite-variable assembly
(`IdealTrivialityComputable`): the classical `properTest` agrees as a function
with the computable ideal-triviality decision
(`computablePred_one_mem_span_nat`), every other ingredient is computable, and
`Computable.nat_strong_rec` closes the recursion just as `primrec_validCode`
does for the code validator.
-/

universe u

set_option linter.unusedSectionVars false

namespace Semicontinuity
namespace GreedyIdeal

open Polynomial

variable {F : Type u} [Field F] [Primcodable F] [ComputableField F] [PerfectField F]

/-! ## A computable flatten helper -/

namespace Computable

variable {α β : Type*} [Primcodable α] [Primcodable β]

/-- `List.flatten` is `List.foldl (· ++ ·) []` up to associativity. -/
private theorem flatten_eq_foldl_append (l : List (List β)) :
    l.flatten = l.foldl (· ++ ·) [] := by
  have h : ∀ (acc : List β), acc ++ l.flatten = l.foldl (· ++ ·) acc := by
    induction l with
    | nil => intro acc; simp
    | cons a t ih =>
        intro acc
        rw [List.flatten_cons, ← List.append_assoc, ih (acc ++ a), List.foldl_cons]
  simpa using h []

/-- `Computable` closure of `List.flatten`. -/
theorem list_flatten {f : α → List (List β)} (hf : Computable f) :
    Computable fun a => (f a).flatten := by
  have hfold : Computable fun a => (f a).foldl (fun s b => s ++ b) ([] : List β) :=
    Computable.list_foldl hf (Computable.const []) <| Computable.to₂ <|
      Computable.list_append.comp
        (Computable.fst.comp
          (Computable.snd : Computable (fun x : α × (List β × List β) => x.2)))
        (Computable.snd.comp
          (Computable.snd : Computable (fun x : α × (List β × List β) => x.2)))
  exact hfold.of_eq fun a => (flatten_eq_foldl_append (f a)).symm

end Computable

/-! ## Computability of the stage ingredients -/

/-- The classical proper-test agrees as a function with the computable
ideal-triviality decision.  `properTest L = !decide (1 ∈ span …)`, and `decide`
is independent of the decidability instance. -/
theorem computable_properTest :
    Computable (properTest (F := F)) := by
  obtain ⟨_inst, hdec⟩ := computablePred_one_mem_span_nat (F := F)
  refine (Primrec.not.to_comp.comp hdec).of_eq fun L => ?_
  change (!decide (1 ∈ Ideal.span {g | g ∈ L})) = properTest (F := F) L
  unfold properTest
  rw [Bool.eq_iff_iff]
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]

/-- The enumeration `rCode : ℕ → MvPolynomial ℕ F` is computable: it decodes the
input and defaults junk codes to `0`. -/
theorem computable_rCode :
    Computable (rCode (F := F)) := by
  refine (Computable.option_getD Computable.decode (Computable.const 0)).of_eq fun j => ?_
  rfl

/-- The canonical-code guard is computable. -/
theorem computable_canonicalCode :
    Computable (canonicalCode (F := F)) := by
  refine ((computable_decide_eq (β := ℕ)).comp
    (Computable.encode.comp (computable_rCode (F := F))) Computable.id).of_eq fun j => ?_
  rfl

/-- `MvPolynomialNat.level` on a list is bounded by a computable `foldr max`. -/
theorem computable_levelMaxList :
    Computable (levelMaxList (F := F)) := by
  have hmap : Computable fun L : List (MvPolynomial ℕ F) =>
      L.map (MvPolynomialNat.level (F := F)) :=
    Computable.list_map Computable.id
      (MvPolynomialNat.computable_level (F := F).comp Computable.snd).to₂
  have hstep : Computable₂ fun (_ : List (MvPolynomial ℕ F)) (p : ℕ × ℕ) =>
      max p.1 p.2 :=
    (Primrec.nat_max.to_comp.comp
      (Computable.fst.comp Computable.snd)
      (Computable.snd.comp Computable.snd)).to₂
  have hfoldl : Computable fun L : List (MvPolynomial ℕ F) =>
      (L.map (MvPolynomialNat.level (F := F))).foldl (fun s b => max s b) 0 :=
    Computable.list_foldl hmap (Computable.const 0) hstep
  exact hfoldl.of_eq fun L => by
    unfold levelMaxList
    rw [List.foldl_eq_foldr (f := max)]

/-! ## Computability of the Vieta prefix `gamma1Flat` -/

/-- `blockDeg F = (enumMonic F ·).natDegree` is computable. -/
theorem computable_blockDeg :
    Computable (blockDeg F) := by
  refine (computable_poly_natDegree.comp (computable_enumMonic (F := F))).of_eq fun j => ?_
  rfl

/-- `blockOffset F j = ((range j).map (blockDeg F)).sum` is computable. -/
theorem computable_blockOffset :
    Computable (blockOffset F) := by
  have hmap : Computable fun j : ℕ => (List.range j).map (blockDeg F) :=
    Computable.list_map (Primrec.list_range.to_comp)
      (computable_blockDeg (F := F).comp Computable.snd).to₂
  refine (Computable.list_sum Primrec.nat_add.to_comp hmap).of_eq fun j => ?_
  rfl

/-- The block product `blockProd F j` expressed as a `List.range` product of
linear factors `X - C (X_{offset+i})`. -/
private theorem fin_prod_eq_range_prod {M : Type*} [CommMonoid M] (n : ℕ) (f : ℕ → M) :
    (∏ i : Fin n, f i) = ((List.range n).map f).prod := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Fin.prod_univ_castSucc, List.range_succ, List.map_append, List.prod_append]
      simp [ih]

theorem blockProd_eq_range_prod (j : ℕ) :
    blockProd F j =
      ((List.range (blockDeg F j)).map fun i =>
        (Polynomial.X - Polynomial.C (MvPolynomial.X (blockOffset F j + i) :
          MvPolynomial ℕ F))).prod := by
  rw [blockProd]
  rw [← fin_prod_eq_range_prod (blockDeg F j)
    (fun i => (Polynomial.X - Polynomial.C (MvPolynomial.X (blockOffset F j + i) :
      MvPolynomial ℕ F)))]
  rfl

/-- `blockProd F` is computable as a function `ℕ → Polynomial (MvPolynomial ℕ F)`. -/
theorem computable_blockProd :
    Computable (blockProd F) := by
  have hX : Computable fun i : ℕ => (MvPolynomial.X i : MvPolynomial ℕ F) :=
    MvPolynomialNat.computable_mvPolynomialNat_X (F := F)
  have hfactor : Computable₂ fun (j : ℕ) (i : ℕ) =>
      (Polynomial.X - Polynomial.C (MvPolynomial.X (blockOffset F j + i) :
        MvPolynomial ℕ F)) := by
    have hvar : Computable fun x : ℕ × ℕ =>
        (MvPolynomial.X (blockOffset F x.1 + x.2) : MvPolynomial ℕ F) :=
      hX.comp (Primrec.nat_add.to_comp.comp
        (computable_blockOffset (F := F).comp Computable.fst) Computable.snd)
    exact (computable₂_poly_sub.comp
      (Computable.const Polynomial.X)
      (computable_poly_C.comp hvar)).to₂
  have hmap : Computable fun j : ℕ =>
      (List.range (blockDeg F j)).map fun i =>
        (Polynomial.X - Polynomial.C (MvPolynomial.X (blockOffset F j + i) :
          MvPolynomial ℕ F)) :=
    Computable.list_map
      (Primrec.list_range.to_comp.comp (computable_blockDeg (F := F)))
      hfactor
  refine (Computable.list_prod ComputableRing.computable_mul hmap).of_eq fun j => ?_
  exact (blockProd_eq_range_prod (F := F) j).symm

/-- `vietaEqs F` is computable as a function `ℕ → List (MvPolynomial ℕ F)`. -/
theorem computable_vietaEqs :
    Computable (vietaEqs F) := by
  have hrange : Computable fun j : ℕ => List.range (blockDeg F j + 1) :=
    Primrec.list_range.to_comp.comp
      (Primrec.succ.to_comp.comp (computable_blockDeg (F := F)))
  have hterm : Computable₂ fun (j : ℕ) (k : ℕ) =>
      (blockProd F j).coeff k - MvPolynomial.C ((enumMonic F j).coeff k) := by
    have hbp : Computable fun x : ℕ × ℕ => (blockProd F x.1).coeff x.2 :=
      computable₂_poly_coeff.comp
        (computable_blockProd (F := F).comp Computable.fst) Computable.snd
    have hem : Computable fun x : ℕ × ℕ =>
        (MvPolynomial.C ((enumMonic F x.1).coeff x.2) : MvPolynomial ℕ F) :=
      MvPolynomialNat.computable_mvPolynomialNat_C (F := F).comp
        (computable₂_poly_coeff.comp
          (computable_enumMonic (F := F).comp Computable.fst) Computable.snd)
    exact (ComputableRing.computable₂_sub.comp hbp hem).to₂
  refine (Computable.list_map hrange hterm).of_eq fun j => ?_
  rfl

/-- **Computability of the Vieta prefix** (`rabin.tex`:362-386).  The flattened
list of the first `K` Vieta blocks is computable in `K`. -/
theorem computable_gamma1Flat :
    Computable (gamma1Flat F) := by
  have hmap : Computable fun K : ℕ => (List.range K).map (vietaEqs F) :=
    Computable.list_map Primrec.list_range.to_comp
      (computable_vietaEqs (F := F).comp Computable.snd).to₂
  refine (Computable.list_flatten hmap).of_eq fun K => ?_
  rfl

/-! ## The greedy strong recursion -/

/-- The stage step recomputed from the Boolean history table.  The index is read
off as `table.length`, the accepted prefix is rebuilt from the table, and the
result is `acceptStep` at that index.  The accepted prefix is built with a
`map`-then-`flatten` instead of `filterMap`, so the whole step is computable. -/
noncomputable def acceptStepFromTable (table : List Bool) : Bool :=
  let N := table.length
  let accepted :=
    ((List.range N).map fun s =>
      if table.getD s false then [rCode (F := F) s] else []).flatten
  let head := accepted ++ [rCode (F := F) N]
  canonicalCode (F := F) N &&
    properTest (F := F) (head ++ gamma1Flat F (kBound (F := F) head))

private theorem acceptedListFromTable_eq_flatten (j : ℕ) (table : List Bool) :
    acceptedListFromTable (F := F) j table =
      ((List.range j).map fun s =>
        if table.getD s false then [rCode (F := F) s] else []).flatten := by
  unfold acceptedListFromTable
  rw [List.filterMap_eq_flatMap_toList, List.flatMap_def]
  congr 1
  apply List.map_congr_left
  intro s _
  by_cases h : table.getD s false = true
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h]; rfl

/-- `acceptStepFromTable` recomputes `acceptStep` at the table's length. -/
theorem acceptStepFromTable_eq (j : ℕ) (table : List Bool)
    (hlen : table.length = j) :
    acceptStepFromTable (F := F) table = acceptStep (F := F) j table := by
  subst hlen
  unfold acceptStepFromTable acceptStep testSet
  simp only [← acceptedListFromTable_eq_flatten]

theorem computable_acceptStepFromTable :
    Computable (acceptStepFromTable (F := F)) := by
  have hlen : Computable fun table : List Bool => table.length :=
    Computable.list_length
  -- the accepted prefix, rebuilt from the table
  have hcell : Computable₂ fun (table : List Bool) (s : ℕ) =>
      (if table.getD s false then [rCode (F := F) s] else [] : List (MvPolynomial ℕ F)) := by
    have hcond : Computable fun x : List Bool × ℕ => x.1.getD x.2 false :=
      (Primrec.list_getD false).to_comp.comp Computable.fst Computable.snd
    have hsome : Computable fun x : List Bool × ℕ =>
        ([rCode (F := F) x.2] : List (MvPolynomial ℕ F)) :=
      Computable.list_cons.comp
        (computable_rCode (F := F).comp Computable.snd) (Computable.const [])
    have hc : Computable fun x : List Bool × ℕ =>
        (if x.1.getD x.2 false then [rCode (F := F) x.2] else [] :
          List (MvPolynomial ℕ F)) := by
      refine (Computable.cond hcond hsome (Computable.const [])).of_eq fun x => ?_
      by_cases h : x.1.getD x.2 false = true
      · rw [h]; rfl
      · rw [Bool.not_eq_true _ |>.mp h]; rfl
    exact hc.to₂
  have hmapcells : Computable fun table : List Bool =>
      (List.range table.length).map fun s =>
        (if table.getD s false then [rCode (F := F) s] else [] :
          List (MvPolynomial ℕ F)) :=
    Computable.list_map (Primrec.list_range.to_comp.comp hlen) hcell
  have haccepted : Computable fun table : List Bool =>
      ((List.range table.length).map fun s =>
        (if table.getD s false then [rCode (F := F) s] else [] :
          List (MvPolynomial ℕ F))).flatten :=
    Computable.list_flatten hmapcells
  -- the head list
  have hhead : Computable fun table : List Bool =>
      (((List.range table.length).map fun s =>
        (if table.getD s false then [rCode (F := F) s] else [] :
          List (MvPolynomial ℕ F))).flatten) ++ [rCode (F := F) table.length] :=
    Computable.list_append.comp haccepted
      (Computable.list_cons.comp
        (computable_rCode (F := F).comp hlen) (Computable.const []))
  -- the test set
  have hkbound : Computable fun table : List Bool =>
      kBound (F := F)
        ((((List.range table.length).map fun s =>
          (if table.getD s false then [rCode (F := F) s] else [] :
            List (MvPolynomial ℕ F))).flatten) ++ [rCode (F := F) table.length]) := by
    have : Computable fun L : List (MvPolynomial ℕ F) => kBound (F := F) L := by
      refine (Primrec.succ.to_comp.comp (computable_levelMaxList (F := F))).of_eq fun L => ?_
      rfl
    exact this.comp hhead
  have htestSet : Computable fun table : List Bool =>
      (((List.range table.length).map fun s =>
        (if table.getD s false then [rCode (F := F) s] else [] :
          List (MvPolynomial ℕ F))).flatten ++ [rCode (F := F) table.length]) ++
        gamma1Flat F (kBound (F := F)
          ((((List.range table.length).map fun s =>
            (if table.getD s false then [rCode (F := F) s] else [] :
              List (MvPolynomial ℕ F))).flatten) ++ [rCode (F := F) table.length])) :=
    Computable.list_append.comp hhead (computable_gamma1Flat (F := F).comp hkbound)
  have hresult : Computable fun table : List Bool =>
      canonicalCode (F := F) table.length &&
        properTest (F := F)
          ((((List.range table.length).map fun s =>
            (if table.getD s false then [rCode (F := F) s] else [] :
              List (MvPolynomial ℕ F))).flatten ++ [rCode (F := F) table.length]) ++
            gamma1Flat F (kBound (F := F)
              ((((List.range table.length).map fun s =>
                (if table.getD s false then [rCode (F := F) s] else [] :
                  List (MvPolynomial ℕ F))).flatten) ++ [rCode (F := F) table.length]))) :=
    Primrec.and.to_comp.comp
      (computable_canonicalCode (F := F).comp hlen)
      (computable_properTest (F := F).comp htestSet)
  exact hresult.of_eq fun table => rfl

/-- **Computability of `acceptU`** (Rabin's Theorem 7, `rabin.tex`:388-394:
"`i_R(U)` is recursive").  The greedy strong recursion is computable: the stage
step `acceptStepFromTable` reads the index off the history table's length, and
`Computable.nat_strong_rec` closes the recursion. -/
theorem computable_acceptU :
    Computable (acceptU (F := F)) := by
  have hg : Computable₂ fun (_ : Unit) (table : List Bool) =>
      some (acceptStepFromTable (F := F) table) :=
    (Computable.option_some.comp
      (computable_acceptStepFromTable (F := F).comp Computable.snd)).to₂
  have H : ∀ N : ℕ,
      (fun (_ : Unit) (table : List Bool) => some (acceptStepFromTable (F := F) table)) ()
        ((List.range N).map (fun n => acceptU (F := F) n)) = some (acceptU (F := F) N) := by
    intro N
    dsimp only
    congr 1
    have hlen : ((List.range N).map (fun n => acceptU (F := F) n)).length = N := by
      simp
    rw [acceptStepFromTable_eq (F := F) N _ hlen]
    -- the rebuilt table agrees with `acceptTable N` on the relevant entries
    have htable : ∀ s, s < N →
        ((List.range N).map (fun n => acceptU (F := F) n)).getD s false =
          (acceptTable (F := F) N).getD s false := by
      intro s hs
      rw [acceptTable_getD hs]
      rw [List.getD_eq_getElem _ _ (by simpa using hs), List.getElem_map]
      simp
    -- the accepted prefixes coincide
    have haccepted :
        acceptedListFromTable (F := F) N ((List.range N).map (fun n => acceptU (F := F) n)) =
          acceptedListFromTable (F := F) N (acceptTable (F := F) N) := by
      unfold acceptedListFromTable
      apply List.filterMap_congr
      intro s hs
      rw [htable s (List.mem_range.mp hs)]
    -- hence the stage step is `acceptStep N (acceptTable N) = acceptU N`
    have hstep : acceptStep (F := F) N ((List.range N).map (fun n => acceptU (F := F) n)) =
        acceptStep (F := F) N (acceptTable (F := F) N) := by
      unfold acceptStep testSet
      rw [haccepted]
    rw [hstep]
    rfl
  exact (Computable.nat_strong_rec
    (fun (_ : Unit) N => acceptU (F := F) N) hg
    (fun _ N => H N)).comp (Computable.const ()) Computable.id

end GreedyIdeal
end Semicontinuity
