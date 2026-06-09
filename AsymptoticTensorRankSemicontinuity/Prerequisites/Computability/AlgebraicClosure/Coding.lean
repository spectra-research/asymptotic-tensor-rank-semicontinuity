/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.AlgebraicClosure.Properties
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.AlgebraicClosure.Recursive
import Mathlib.Data.Nat.Nth

/-!
# `ComputableAlgebraicClosure F` is a computable field

`ComputableAlgebraicClosure F := R ⧸ U` is the algebraic closure of `F`
(`Properties.lean`).  This file makes it a *computable* field (Rabin 1960,
Theorem 7, `rabin.tex`:388-408) by re-indexing it by least-representative codes
so that the ring operations become computable.  The development has three parts:

* membership in `U` is decidable, `ComputableAlgebraicClosure F` has decidable
  equality and is infinite;
* least-representative codes `isLeastRep` give a bijection
  `{j // isLeastRep j} ≃ ComputableAlgebraicClosure F`, hence `Denumerable` and
  `Primcodable (ComputableAlgebraicClosure F)`;
* the ring operations are computable via a least-code search, giving
  `ComputableField (ComputableAlgebraicClosure F)`.
-/

universe u

namespace Semicontinuity
namespace GreedyIdeal

variable {F : Type u} [Field F] [Primcodable F] [ComputableField F]

/-! ## Decidability and infiniteness -/

/-- Membership in Rabin's ideal `U` is decidable: `r ∈ U` iff the Boolean
`acceptU (encode r)` is `true` (`mem_U_iff`), and `Bool`-equality is decidable.
(`acceptU` is `noncomputable`-DEFINED, but the *proposition* `acceptU _ = true`
is decidable because `Bool` has `DecidableEq`.) -/
noncomputable instance decidableMemU : DecidablePred (· ∈ U (F := F)) := fun r =>
  decidable_of_iff (acceptU (F := F) (Encodable.encode r) = true) (mem_U_iff (F := F)).symm

/-- `ComputableAlgebraicClosure F` has decidable equality: two cosets `mk a`, `mk b` are equal iff
`a - b ∈ U` (`Ideal.Quotient.mk_eq_mk_iff_sub_mem`), and membership in `U` is
decidable (`decidableMemU`).  We reduce both arguments to representatives via
`Quotient.recOnSubsingleton₂`. -/
noncomputable instance decidableEqComputableAlgebraicClosure :
    DecidableEq (ComputableAlgebraicClosure F) := by
  intro x y
  refine Quotient.recOnSubsingleton₂ (motive := fun x y => Decidable (x = y)) x y ?_
  intro a b
  exact decidable_of_iff (a - b ∈ U (F := F))
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).symm

/-- `ComputableAlgebraicClosure F` is infinite: it is an algebraically closed field
(`IsAlgClosed.instInfinite`). -/
example : Infinite (ComputableAlgebraicClosure F) := inferInstance

/-! ## Re-indexing by least-representative codes

`mk : R → ComputableAlgebraicClosure F` is surjective, and `rCode` enumerates all of `R`, so every
`x : ComputableAlgebraicClosure F` is hit by some code `j` (namely `encode r` for any representative
`r`).  Taking the *least* such code gives an injection `ComputableAlgebraicClosure F ↪ ℕ`, hence an
`Encodable` structure; together with `Infinite (ComputableAlgebraicClosure F)` this yields
`Denumerable (ComputableAlgebraicClosure F)` and finally
`Primcodable (ComputableAlgebraicClosure F)`. -/

/-- Every `x : ComputableAlgebraicClosure F` is the image under `mk` of some `rCode j`. -/
theorem exists_code_mk_rCode (x : ComputableAlgebraicClosure F) :
    ∃ j : ℕ, mk (F := F) (rCode (F := F) j) = x := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Encodable.encode r, by rw [rCode_encode]; exact hr⟩

/-- The least code `j` whose `mk (rCode j)` equals `x` (the canonical
representative index of the coset `x`). -/
noncomputable def leastCode (x : ComputableAlgebraicClosure F) : ℕ :=
  Nat.find (exists_code_mk_rCode x)

@[simp] theorem mk_rCode_leastCode (x : ComputableAlgebraicClosure F) :
    mk (F := F) (rCode (F := F) (leastCode (F := F) x)) = x :=
  Nat.find_spec (exists_code_mk_rCode x)

/-- `leastCode` is injective: if two cosets share their least code they are
equal (their common `mk (rCode ·)` value). -/
theorem leastCode_injective : Function.Injective (leastCode (F := F)) := by
  intro x y hxy
  have hx := mk_rCode_leastCode (F := F) x
  have hy := mk_rCode_leastCode (F := F) y
  rw [← hx, ← hy, hxy]

/-! ### Explicit rank via least-representative counting

Instead of compressing `leastCode`'s (sparse) range with the opaque
`Denumerable.ofEncodableOfInfinite` machinery, we build an *explicit*
`ComputableAlgebraicClosure F ≃ ℕ` whose forward map is `Nat.count isLeastRep ∘ leastCode`, a
manifestly computable counting expression.  This is what makes `computable_mk`
go through: `Encodable.encode (mk p)` becomes definitionally this count. -/

/-- A code `j` is a *least representative* when no strictly smaller code lies in
the same coset, i.e. `rCode j' - rCode j ∉ U` for all `j' < j`.  Equivalently
`j = leastCode (mk (rCode j))`. -/
def isLeastRep (j : ℕ) : Prop :=
  ∀ j' < j, rCode (F := F) j' - rCode (F := F) j ∉ U (F := F)

noncomputable instance decidableIsLeastRep : DecidablePred (isLeastRep (F := F)) :=
  fun j => Nat.decidableBallLT j _

/-- `mk (rCode j') = mk (rCode j)` iff `rCode j' - rCode j ∈ U` — the
polynomial-space match test, specialised to two codes. -/
theorem mk_rCode_eq_iff_sub_mem (j' j : ℕ) :
    mk (F := F) (rCode (F := F) j') = mk (F := F) (rCode (F := F) j) ↔
      rCode (F := F) j' - rCode (F := F) j ∈ U (F := F) :=
  Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _

/-- `j` is a least-representative iff it is the least code of its own coset. -/
theorem isLeastRep_iff_leastCode (j : ℕ) :
    isLeastRep (F := F) j ↔ leastCode (F := F) (mk (F := F) (rCode (F := F) j)) = j := by
  constructor
  · intro hj
    refine le_antisymm ?_ ?_
    · exact Nat.find_le rfl
    · by_contra hlt
      push_neg at hlt
      have hle : leastCode (F := F) (mk (F := F) (rCode (F := F) j)) < j := hlt
      have hspec := mk_rCode_leastCode (F := F) (mk (F := F) (rCode (F := F) j))
      exact hj _ hle ((mk_rCode_eq_iff_sub_mem (F := F) _ j).mp hspec)
  · intro hj j' hj' hmem
    have : mk (F := F) (rCode (F := F) j') = mk (F := F) (rCode (F := F) j) :=
      (mk_rCode_eq_iff_sub_mem (F := F) j' j).mpr hmem
    have hle : leastCode (F := F) (mk (F := F) (rCode (F := F) j)) ≤ j' := by
      apply Nat.find_le; rw [← this]
    rw [hj] at hle
    exact absurd hj' (not_lt.mpr hle)

/-- `leastCode x` is always a least representative. -/
theorem isLeastRep_leastCode (x : ComputableAlgebraicClosure F) :
    isLeastRep (F := F) (leastCode (F := F) x) := by
  rw [isLeastRep_iff_leastCode, mk_rCode_leastCode]

/-- For a least-representative `j`, `leastCode (mk (rCode j)) = j`. -/
theorem leastCode_mk_rCode_of_isLeastRep {j : ℕ} (h : isLeastRep (F := F) j) :
    leastCode (F := F) (mk (F := F) (rCode (F := F) j)) = j :=
  (isLeastRep_iff_leastCode (F := F) j).mp h

/-- The least-representative codes are infinite: `leastCode` injects the
infinite `ComputableAlgebraicClosure F` into them. -/
theorem infinite_isLeastRep : (setOf (isLeastRep (F := F))).Infinite :=
  Set.infinite_of_injective_forall_mem
    (f := fun x : ComputableAlgebraicClosure F => leastCode (F := F) x)
    (leastCode_injective (F := F)) (fun x => isLeastRep_leastCode (F := F) x)

/-- The explicit countability equivalence `ComputableAlgebraicClosure F ≃ ℕ`: rank a coset by
counting the least-representative codes strictly below its own least code. -/
noncomputable def rankEquiv : ComputableAlgebraicClosure F ≃ ℕ where
  toFun x := Nat.count (isLeastRep (F := F)) (leastCode (F := F) x)
  invFun n := mk (F := F) (rCode (F := F) (Nat.nth (isLeastRep (F := F)) n))
  left_inv x := by
    dsimp only
    rw [Nat.nth_count (isLeastRep_leastCode (F := F) x), mk_rCode_leastCode]
  right_inv n := by
    dsimp only
    have hmem : isLeastRep (F := F) (Nat.nth (isLeastRep (F := F)) n) :=
      Nat.nth_mem_of_infinite (infinite_isLeastRep (F := F)) n
    rw [leastCode_mk_rCode_of_isLeastRep (F := F) hmem,
      Nat.count_nth_of_infinite (infinite_isLeastRep (F := F)) n]

/-- `ComputableAlgebraicClosure F` is denumerable via the explicit rank `rankEquiv`. -/
noncomputable instance denumerableComputableAlgebraicClosure :
    Denumerable (ComputableAlgebraicClosure F) :=
  Denumerable.mk' (rankEquiv (F := F))

/-- **`Primcodable (ComputableAlgebraicClosure F)`** (Rabin 1960, Theorem 7, `rabin.tex`:388-408).
The `Primcodable` obligation `Nat.Primrec (encode ∘ decode)` is discharged
tautologically by `Primcodable.ofDenumerable`.  The `encode` of this instance is
*definitionally* the computable count `Nat.count isLeastRep (leastCode ·)`,
which is what unblocks `computable_mk`. -/
noncomputable instance instPrimcodable : Primcodable (ComputableAlgebraicClosure F) :=
  Primcodable.ofDenumerable (ComputableAlgebraicClosure F)

/-- `Encodable.encode` on `ComputableAlgebraicClosure F` is the explicit least-rep count. -/
theorem encode_eq_count (x : ComputableAlgebraicClosure F) :
    Encodable.encode x = Nat.count (isLeastRep (F := F)) (leastCode (F := F) x) := rfl

/-! ## Computable ring operations

Strategy.  Pick a *computable* representative selection
`reprPoly : ComputableAlgebraicClosure F → R` (a polynomial mapping to the given coset),
defined by an unbounded search over codes `n` for the first `rCode n` whose image is the coset.
Then `mk` is computable (search for the rank `n` whose decoded coset matches,
testing the match in `MvPolynomial` space via `reprPoly _ - p ∈ U`, which is
decidable), and the ring operations are
`x + y = mk (reprPoly x + reprPoly y)`, `x * y = mk (reprPoly x * reprPoly y)`,
computable by composing `reprPoly`, the `MvPolynomial` ring ops, and `mk`. -/

/-- The search trial for a representative polynomial of a coset `x`: at code `n`
emit `rCode n` if its image is `x`, else nothing. -/
noncomputable def reprTrial (x : ComputableAlgebraicClosure F) (n : ℕ) :
    Option (MvPolynomial ℕ F) :=
  if mk (F := F) (rCode (F := F) n) = x then some (rCode (F := F) n) else none

theorem reprTrial_dom (x : ComputableAlgebraicClosure F) :
    (Nat.rfindOpt (reprTrial (F := F) x)).Dom := by
  rw [Nat.rfindOpt_dom]
  obtain ⟨j, hj⟩ := exists_code_mk_rCode x
  exact ⟨j, rCode (F := F) j, by simp [reprTrial, hj]⟩

/-- A computable representative polynomial for the coset `x` (the first code's
polynomial found by the search). -/
noncomputable def reprPoly (x : ComputableAlgebraicClosure F) : MvPolynomial ℕ F :=
  (Nat.rfindOpt (reprTrial (F := F) x)).get (reprTrial_dom (F := F) x)

theorem reprPoly_mem (x : ComputableAlgebraicClosure F) :
    reprPoly (F := F) x ∈ Nat.rfindOpt (reprTrial (F := F) x) :=
  Part.get_mem _

/-- `reprPoly x` is a genuine representative: its image under `mk` is `x`. -/
@[simp] theorem mk_reprPoly (x : ComputableAlgebraicClosure F) :
    mk (F := F) (reprPoly (F := F) x) = x := by
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec (reprPoly_mem (F := F) x)
  by_cases h : mk (F := F) (rCode (F := F) n) = x
  · have : reprPoly (F := F) x = rCode (F := F) n := by
      simpa [reprTrial, h] using hn.symm
    rw [this]; exact h
  · simp [reprTrial, h] at hn

/-! ### The polynomial-space code search

The match test `mk (rCode n) = mk p` is equivalent to `rCode n - p ∈ U`
(`mk_rCode_eq_mk_iff`), a decidable, computable test *entirely in `MvPolynomial`
space* — no `ComputableAlgebraicClosure` comparison is needed.  With the explicit
rank coding, `Encodable.encode (mk p) = Nat.count isLeastRep (leastCode (mk p))`
(`encode_eq_count`) and `leastCode (mk p)` is the least code `n` with
`rCode n - p ∈ U` (`codeSearch_eq`), so the encoding of `mk p` is computed by
this search. -/

/-- The match predicate `mk (rCode n) = mk p`, expressed in `MvPolynomial`
space as `rCode n - p ∈ U` — decidable and (with `decidableMemU`) computable. -/
theorem mk_rCode_eq_mk_iff (n : ℕ) (p : MvPolynomial ℕ F) :
    mk (F := F) (rCode (F := F) n) = mk (F := F) p ↔
      rCode (F := F) n - p ∈ U (F := F) :=
  Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _

-- The computability of `rCode` (`computable_rCode`, `Recursive.lean`) needs a
-- `PerfectField F` hypothesis; the remaining declarations consume it.
variable [PerfectField F]

/-! ### Computability of the explicit rank pieces -/

/-- The boolean membership test `rCode j - p ∈ U`, in `MvPolynomial` space. -/
noncomputable def matchBool (p : MvPolynomial ℕ F) (j : ℕ) : Bool :=
  acceptU (F := F) (Encodable.encode (rCode (F := F) j - p))

omit [PerfectField F] in
theorem matchBool_iff (p : MvPolynomial ℕ F) (j : ℕ) :
    matchBool (F := F) p j = true ↔ rCode (F := F) j - p ∈ U (F := F) :=
  (mem_U_iff (F := F)).symm

/-- `matchBool` is computable in both arguments. -/
theorem computable_matchBool : Computable₂ (matchBool (F := F)) := by
  have hsub : Computable fun q : MvPolynomial ℕ F × ℕ =>
      rCode (F := F) q.2 - q.1 :=
    ComputableRing.computable₂_sub.comp (computable_rCode (F := F).comp Computable.snd)
      Computable.fst
  exact (computable_acceptU (F := F)).comp (Computable.encode.comp hsub)

/-- The code-search trial: emit `j` when `rCode j - p ∈ U`, i.e. `mk (rCode j) =
mk p`; else nothing. -/
noncomputable def codeTrial (p : MvPolynomial ℕ F) (j : ℕ) : Option ℕ :=
  if matchBool (F := F) p j = true then some j else none

omit [PerfectField F] in
theorem codeTrial_dom (p : MvPolynomial ℕ F) :
    (Nat.rfindOpt (codeTrial (F := F) p)).Dom := by
  rw [Nat.rfindOpt_dom]
  obtain ⟨j, hj⟩ := exists_code_mk_rCode (F := F) (mk (F := F) p)
  refine ⟨j, j, ?_⟩
  have : rCode (F := F) j - p ∈ U (F := F) := (mk_rCode_eq_mk_iff (F := F) j p).mp hj
  simp [codeTrial, (matchBool_iff (F := F) p j).mpr this]

/-- The least code `j` with `mk (rCode j) = mk p`, found by the search.  It is
computably extractable from `p` (it is `leastCode (mk p)`, see `codeSearch_eq`). -/
noncomputable def codeSearch (p : MvPolynomial ℕ F) : ℕ :=
  (Nat.rfindOpt (codeTrial (F := F) p)).get (codeTrial_dom (F := F) p)

omit [PerfectField F] in
theorem codeSearch_mem (p : MvPolynomial ℕ F) :
    codeSearch (F := F) p ∈ Nat.rfindOpt (codeTrial (F := F) p) :=
  Part.get_mem _

set_option maxHeartbeats 1000000 in
-- Raised limit: the `Nat.rfindOpt`/`Nat.rfind` unfolding plus the `Part.mem_bind`
-- case analysis below makes elaboration of this proof exceed the default budget.
omit [PerfectField F] in
/-- The search returns exactly the least code of the coset of `p`. -/
theorem codeSearch_eq (p : MvPolynomial ℕ F) :
    codeSearch (F := F) p = leastCode (F := F) (mk (F := F) p) := by
  have hmem := codeSearch_mem (F := F) p
  rw [Nat.rfindOpt] at hmem
  obtain ⟨n, hn, hbind⟩ := Part.mem_bind_iff.mp hmem
  -- `(codeTrial p n).isSome = true` from `rfind_spec`, with the coercion peeled.
  have hsome : (codeTrial (F := F) p n).isSome = true := by
    have hspec := Nat.rfind_spec hn
    rwa [Part.coe_some, Part.mem_some_iff, eq_comm] at hspec
  -- so `matchBool p n = true` (otherwise `codeTrial` is `none`).
  have hnmatch : matchBool (F := F) p n = true := by
    by_contra h
    rw [Bool.not_eq_true] at h
    rw [codeTrial, if_neg (by rw [h]; exact Bool.false_ne_true)] at hsome
    simp at hsome
  have htrial_n : codeTrial (F := F) p n = some n := by
    rw [codeTrial, if_pos hnmatch]
  have hval : codeSearch (F := F) p = n := by
    rw [htrial_n, Part.coe_some, Part.mem_some_iff] at hbind
    exact hbind
  have hmkn : mk (F := F) (rCode (F := F) n) = mk (F := F) p :=
    (mk_rCode_eq_mk_iff (F := F) n p).mpr ((matchBool_iff (F := F) p n).mp hnmatch)
  -- minimality: any `j < n` does NOT match.
  have hmin : ∀ j < n, ¬ mk (F := F) (rCode (F := F) j) = mk (F := F) p := by
    intro j hj hmkj
    have hjmatch : matchBool (F := F) p j = true :=
      (matchBool_iff (F := F) p j).mpr ((mk_rCode_eq_mk_iff (F := F) j p).mp hmkj)
    have hfalse := Nat.rfind_min hn hj
    rw [Part.coe_some, Part.mem_some_iff, eq_comm] at hfalse
    rw [codeTrial, if_pos hjmatch] at hfalse
    simp at hfalse
  rw [hval]
  -- `n = leastCode (mk p)` via `Nat.find` characterisation.
  refine le_antisymm ?_ ?_
  · exact (Nat.le_find_iff _ _).mpr (fun j hj => hmin j hj)
  · exact Nat.find_le hmkn

/-- `codeSearch` is computable. -/
theorem computable_codeSearch : Computable (codeSearch (F := F)) := by
  have htrial : Computable₂ (codeTrial (F := F)) := by
    have htest : Computable fun q : MvPolynomial ℕ F × ℕ =>
        matchBool (F := F) q.1 q.2 := computable_matchBool (F := F)
    have hsome : Computable fun q : MvPolynomial ℕ F × ℕ => some q.2 :=
      Computable.option_some.comp Computable.snd
    refine (Computable.cond htest hsome (Computable.const none)).to₂.of_eq ?_
    rintro ⟨p, j⟩
    by_cases h : matchBool (F := F) p j = true <;> simp [codeTrial, h]
  exact (Partrec.rfindOpt htrial).of_eq_tot fun p => codeSearch_mem (F := F) p

/-- The boolean form of `isLeastRep j`: no earlier code lies in the same coset,
i.e. `(List.range j).all (fun j' => ! (rCode j' - rCode j ∈ U))`. -/
noncomputable def isLeastRepBool (j : ℕ) : Bool :=
  (List.range j).all
    (fun j' => ! acceptU (F := F) (Encodable.encode (rCode (F := F) j' - rCode (F := F) j)))

omit [PerfectField F] in
theorem isLeastRepBool_iff (j : ℕ) :
    isLeastRepBool (F := F) j = true ↔ isLeastRep (F := F) j := by
  rw [isLeastRepBool, List.all_eq_true]
  constructor
  · intro h j' hj' hmem
    have hin : j' ∈ List.range j := List.mem_range.mpr hj'
    have hb := h j' hin
    have hacc : acceptU (F := F) (Encodable.encode
        (rCode (F := F) j' - rCode (F := F) j)) = true := mem_U_iff.mp hmem
    rw [hacc] at hb
    exact absurd hb (by simp)
  · intro h j' hin
    have hj' : j' < j := List.mem_range.mp hin
    have hnmem : rCode (F := F) j' - rCode (F := F) j ∉ U (F := F) := h j' hj'
    have : acceptU (F := F) (Encodable.encode
        (rCode (F := F) j' - rCode (F := F) j)) = false := by
      rw [Bool.eq_false_iff]; intro hacc; exact hnmem (mem_U_iff.mpr hacc)
    rw [this]; rfl

/-- `isLeastRepBool` is computable. -/
theorem computable_isLeastRepBool : Computable (isLeastRepBool (F := F)) := by
  have hrange : Computable fun j : ℕ => List.range j := Primrec.list_range.to_comp
  have hpred : Computable₂ fun j j' : ℕ =>
      ! acceptU (F := F) (Encodable.encode (rCode (F := F) j' - rCode (F := F) j)) := by
    have hsub : Computable fun q : ℕ × ℕ =>
        rCode (F := F) q.2 - rCode (F := F) q.1 :=
      ComputableRing.computable₂_sub.comp (computable_rCode (F := F).comp Computable.snd)
        (computable_rCode (F := F).comp Computable.fst)
    exact (Primrec.not.to_comp.comp
      ((computable_acceptU (F := F)).comp (Computable.encode.comp hsub))).to₂
  exact (Computable.list_all hrange hpred)

/-- `Nat.count isLeastRep` is computable in its argument: sum of the indicator
`isLeastRepBool` over `List.range n`. -/
theorem computable_count_isLeastRep :
    Computable (fun n => Nat.count (isLeastRep (F := F)) n) := by
  -- `Nat.count p n = ((List.range n).map (fun j => if isLeastRepBool j then 1 else 0)).sum`
  have hmap : Computable fun n : ℕ =>
      (List.range n).map (fun j => if isLeastRepBool (F := F) j = true then 1 else 0) := by
    have hterm : Computable₂ fun (_ : ℕ) (j : ℕ) =>
        if isLeastRepBool (F := F) j = true then (1 : ℕ) else 0 := by
      have h1 : Computable fun q : ℕ × ℕ => isLeastRepBool (F := F) q.2 :=
        (computable_isLeastRepBool (F := F)).comp Computable.snd
      exact (Computable.cond h1 (Computable.const 1) (Computable.const 0)).to₂.of_eq
        (by rintro ⟨_, j⟩; by_cases h : isLeastRepBool (F := F) j = true <;> simp [h])
    exact Computable.list_map (Primrec.list_range.to_comp) hterm
  have hsum : Computable fun n : ℕ =>
      ((List.range n).map (fun j => if isLeastRepBool (F := F) j = true then 1 else 0)).sum :=
    Computable.list_sum Primrec.nat_add.to_comp hmap
  refine hsum.of_eq fun n => ?_
  -- identify the sum with `Nat.count`
  rw [Nat.count, List.countP_eq_length_filter]
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih,
      List.filter_append, List.length_append]
    have hcongr : decide (isLeastRep (F := F) m) = isLeastRepBool (F := F) m := by
      by_cases h : isLeastRep (F := F) m
      · rw [decide_eq_true h, (isLeastRepBool_iff (F := F) m).mpr h]
      · have hb : isLeastRepBool (F := F) m = false := by
          rw [Bool.eq_false_iff]
          exact fun hb => h ((isLeastRepBool_iff (F := F) m).mp hb)
        rw [decide_eq_false h, hb]
    by_cases h : isLeastRepBool (F := F) m = true <;>
      simp [hcongr, h]

/-- **`Computable (mk : R → ComputableAlgebraicClosure F)`**
(Rabin 1960, Theorem 7, `rabin.tex`:388-408).

`Encodable.encode (mk p) = Nat.count isLeastRep (leastCode (mk p))` (definitional,
`encode_eq_count`), and `leastCode (mk p) = codeSearch p` (`codeSearch_eq`) is a
computable polynomial-space code-search.  Composing `computable_count_isLeastRep`
with `computable_codeSearch` gives the result via `Computable.encode_iff`. -/
theorem computable_mk : Computable (mk (F := F)) := by
  rw [← Computable.encode_iff]
  have h : Computable fun p : MvPolynomial ℕ F =>
      Nat.count (isLeastRep (F := F)) (codeSearch (F := F) p) :=
    (computable_count_isLeastRep (F := F)).comp (computable_codeSearch (F := F))
  refine h.of_eq fun p => ?_
  rw [encode_eq_count, codeSearch_eq]

/-- `reprPoly` is computable (downstream of `computable_mk`).

Given `computable_mk`, the trial
`reprTrial x n = if mk (rCode n) = x then some (rCode n) else none` is a
`Computable₂` (the test `mk (rCode n) = x` is `decide (encode (mk (rCode n)) =
encode x)`, computable via `computable_mk`), and `Computable reprPoly` follows
from `(Partrec.rfindOpt _).of_eq_tot (reprPoly_mem ·)`. -/
theorem computable_reprPoly : Computable (reprPoly (F := F)) := by
  have htrial : Computable₂ (reprTrial (F := F)) := by
    have hrcode : Computable fun y : ComputableAlgebraicClosure F × ℕ => rCode (F := F) y.2 :=
      computable_rCode (F := F).comp Computable.snd
    have hmkr : Computable fun y : ComputableAlgebraicClosure F × ℕ =>
        mk (F := F) (rCode (F := F) y.2) :=
      computable_mk.comp hrcode
    have htest : Computable fun y : ComputableAlgebraicClosure F × ℕ =>
        decide (mk (F := F) (rCode (F := F) y.2) = y.1) :=
      (Primrec.eq.decide.to_comp.comp hmkr Computable.fst)
    have hsome : Computable fun y : ComputableAlgebraicClosure F × ℕ => some (rCode (F := F) y.2) :=
      Computable.option_some.comp hrcode
    refine (Computable.cond htest hsome (Computable.const none)).to₂.of_eq ?_
    rintro ⟨x, n⟩
    by_cases h : mk (F := F) (rCode (F := F) n) = x <;> simp [reprTrial, h]
  exact (Partrec.rfindOpt htrial).of_eq_tot fun x => reprPoly_mem (F := F) x

/-- **`ComputableField (ComputableAlgebraicClosure F)`**
(Rabin 1960, Theorem 7, `rabin.tex`:388-408).

Given `computable_mk` and `computable_reprPoly`, the field operations are
`x + y = mk (reprPoly x + reprPoly y)` and `x * y = mk (reprPoly x * reprPoly y)`
(`mk` is a ring hom and `mk_reprPoly` rewrites representatives back), each
computable by composing `computable_reprPoly` (twice), the `MvPolynomial` ring
operations (`ComputableRing.computable_add` / `computable_mul`), and
`computable_mk`. -/
noncomputable instance instComputableField : ComputableField (ComputableAlgebraicClosure F) where
  computable_add := by
    have hadd : Computable fun q : ComputableAlgebraicClosure F × ComputableAlgebraicClosure F =>
        mk (F := F) (reprPoly (F := F) q.1 + reprPoly (F := F) q.2) :=
      computable_mk.comp
        (ComputableRing.computable_add.comp
          (computable_reprPoly.comp Computable.fst)
          (computable_reprPoly.comp Computable.snd))
    exact hadd.of_eq fun q => by
      rw [map_add, mk_reprPoly, mk_reprPoly]
  computable_mul := by
    have hmul : Computable fun q : ComputableAlgebraicClosure F × ComputableAlgebraicClosure F =>
        mk (F := F) (reprPoly (F := F) q.1 * reprPoly (F := F) q.2) :=
      computable_mk.comp
        (ComputableRing.computable_mul.comp
          (computable_reprPoly.comp Computable.fst)
          (computable_reprPoly.comp Computable.snd))
    exact hmul.of_eq fun q => by
      rw [map_mul, mk_reprPoly, mk_reprPoly]

end GreedyIdeal
end Semicontinuity
