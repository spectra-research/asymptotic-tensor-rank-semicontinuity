/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.MvPolynomialComputable
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Data.Finsupp.Encodable

/-!
# Coding countably-many-variable multivariate polynomials

Rabin forms the ring `R = F[x₁,x₂,⋯]` by adjoining a countable sequence of
indeterminates to `F`, and then fixes an effective indexing `i_R` of this
ring (`rabin.tex`:356-358).  This file starts the concrete Lean engineering
choice for that indexing: a polynomial in variables indexed by `ℕ` is coded at
its least finite level and then by the existing finite tower coding.

Only the indexing/coding layer belongs here.  Rabin's admissibility assertion
("Since `F` is computable, `i_R` is an admissible indexing of `R`") requires
computability of the ring operations and is deferred to the next phase.

Mathlib already supplies `Encodable (α →₀ β)` in `Data.Finsupp.Encodable`, so
there is a noncanonical encodable path for the representation
`MvPolynomial σ F = AddMonoidAlgebra F (σ →₀ ℕ)`.  The definitions below do not
use that path as the public encoding: the intended canonical code is the
least-level tower code.
-/

noncomputable section

universe u

namespace Semicontinuity

namespace MvPolynomialNat

variable {F : Type u} [CommRing F]

section ListCode

variable {α : Type*} [Encodable α]

/-- Mathlib's list code is elementwise: coding a list of coded objects agrees
with coding the list of their numeric codes. -/
theorem List.encode_eq_encode_map_encode (l : List α) :
    Encodable.encode l = Encodable.encode (l.map Encodable.encode : List ℕ) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp [ih]

/-- Every element code is strictly below the code of a nonempty list containing
it.  This is the basic descent fact used by recursive code validators. -/
theorem List.encode_mem_lt_encode {a : α} {l : List α} (ha : a ∈ l) :
    Encodable.encode a < Encodable.encode l := by
  induction l with
  | nil => cases ha
  | cons b t ih =>
      simp only [List.mem_cons] at ha
      rw [Encodable.encode_list_cons]
      rcases ha with rfl | ha
      · exact lt_of_le_of_lt (Nat.left_le_pair _ _) (Nat.lt_succ_self _)
      · exact lt_of_lt_of_le (ih ha)
          (Nat.le_succ_of_le (Nat.right_le_pair _ _))

end ListCode

/-- Include the finite level `Fin n` into the countable-variable polynomial
ring by renaming variables along `Fin.val`. -/
def inclLevel (n : ℕ) : MvPolynomial (Fin n) F →ₐ[F] MvPolynomial ℕ F :=
  MvPolynomial.rename Fin.val

/-- Retract the countable-variable polynomial ring onto the finite level
`Fin n`, killing variables outside the range of `Fin.val`. -/
def restrictLevel (n : ℕ) : MvPolynomial ℕ F →ₐ[F] MvPolynomial (Fin n) F :=
  MvPolynomial.killCompl (R := F) (f := Fin.val) Fin.val_injective

@[simp] theorem restrict_inclLevel (n : ℕ) (q : MvPolynomial (Fin n) F) :
    restrictLevel (F := F) n (inclLevel (F := F) n q) = q := by
  simp [restrictLevel, inclLevel,
    (MvPolynomial.killCompl_rename_app (R := F) (f := Fin.val)
      (hf := Fin.val_injective) q)]

/-- The least finite level containing all variables of a countable-variable
multivariate polynomial. -/
def level (p : MvPolynomial ℕ F) : ℕ :=
  p.vars.sup (fun i => i + 1)

theorem mem_vars_lt_level {p : MvPolynomial ℕ F} {i : ℕ} (hi : i ∈ p.vars) :
    i < level p := by
  dsimp [level]
  exact Nat.lt_of_succ_le (Finset.le_sup hi)

theorem level_le_of_vars_lt {p : MvPolynomial ℕ F} {n : ℕ}
    (h : ∀ i ∈ p.vars, i < n) : level p ≤ n := by
  dsimp [level]
  rw [Finset.sup_le_iff]
  intro i hi
  exact h i hi

theorem level_le_iff {p : MvPolynomial ℕ F} {n : ℕ} :
    level p ≤ n ↔ ∀ i ∈ p.vars, i < n := by
  constructor
  · intro h i hi
    exact lt_of_lt_of_le (mem_vars_lt_level (F := F) hi) h
  · exact level_le_of_vars_lt (F := F)

theorem vars_subset_range_fin_val_of_level_le {p : MvPolynomial ℕ F} {n : ℕ}
    (h : level (F := F) p ≤ n) :
    (p.vars : Set ℕ) ⊆ Set.range (Fin.val : Fin n → ℕ) := by
  intro i hi
  exact ⟨⟨i, (level_le_iff (F := F)).mp h i hi⟩, rfl⟩

theorem incl_restrictLevel_of_vars_subset {n : ℕ} {p : MvPolynomial ℕ F}
    (h : (p.vars : Set ℕ) ⊆ Set.range (Fin.val : Fin n → ℕ)) :
    inclLevel (F := F) n (restrictLevel (F := F) n p) = p := by
  classical
  obtain ⟨q, hq⟩ :=
    MvPolynomial.exists_rename_eq_of_vars_subset_range (R := F) p
      (Fin.val : Fin n → ℕ) Fin.val_injective h
  rw [← hq]
  simp [inclLevel, restrictLevel]

theorem incl_restrictLevel_of_level_le {n : ℕ} {p : MvPolynomial ℕ F}
    (h : level (F := F) p ≤ n) :
    inclLevel (F := F) n (restrictLevel (F := F) n p) = p :=
  incl_restrictLevel_of_vars_subset (F := F) (vars_subset_range_fin_val_of_level_le (F := F) h)

@[simp] theorem incl_restrictLevel_level (p : MvPolynomial ℕ F) :
    inclLevel (F := F) (level (F := F) p)
      (restrictLevel (F := F) (level (F := F) p) p) = p :=
  incl_restrictLevel_of_level_le (F := F) le_rfl

theorem level_inclLevel_le (n : ℕ) (q : MvPolynomial (Fin n) F) :
    level (F := F) (inclLevel (F := F) n q) ≤ n := by
  classical
  rw [level_le_iff]
  intro i hi
  obtain ⟨j, _hj, hj⟩ := MvPolynomial.mem_vars_rename (Fin.val : Fin n → ℕ) q hi
  exact hj ▸ j.isLt

theorem inclLevel_rename_castSucc (n : ℕ) (q : MvPolynomial (Fin n) F) :
    inclLevel (F := F) (n + 1) (MvPolynomial.rename Fin.castSucc q) =
      inclLevel (F := F) n q := by
  rw [inclLevel, inclLevel, MvPolynomial.rename_rename]
  have hfun : (Fin.val ∘ (Fin.castSucc : Fin n → Fin (n + 1))) = Fin.val := by
    funext i
    rfl
  rw [hfun]

theorem level_inclLevel_succ_le_iff (n : ℕ)
    (p : MvPolynomial (Fin (n + 1)) F) :
    level (F := F) (inclLevel (F := F) (n + 1) p) ≤ n ↔
      ∃ q : MvPolynomial (Fin n) F, p = MvPolynomial.rename Fin.castSucc q := by
  constructor
  · intro h
    let r := restrictLevel (F := F) n (inclLevel (F := F) (n + 1) p)
    refine ⟨r, ?_⟩
    apply MvPolynomial.rename_injective (R := F) (Fin.val : Fin (n + 1) → ℕ) Fin.val_injective
    change inclLevel (F := F) (n + 1) p =
      inclLevel (F := F) (n + 1) (MvPolynomial.rename Fin.castSucc r)
    rw [inclLevel_rename_castSucc]
    exact (incl_restrictLevel_of_level_le (F := F) h).symm
  · rintro ⟨q, rfl⟩
    rw [inclLevel_rename_castSucc]
    exact level_inclLevel_le (F := F) n q

/-- Public form of the intended canonical code for the countable-variable
carrier.  The `Primcodable` instance is meant to use this exact pairing. -/
def natTowerCode [Primcodable F] [ComputableRing F] (p : MvPolynomial ℕ F) : ℕ :=
  Nat.pair (level (F := F) p)
    (Encodable.encode (restrictLevel (F := F) (level (F := F) p) p))

/-! ## Canonical level-code validation -/

section CodeLayer

variable (F) [Primcodable F] [ComputableRing F]

/-- The canonical code of the zero polynomial at a finite level.

For `n + 1`, the tower instance identifies zero with the empty coefficient
list and hence code `0`; at level `0`, the transported empty-variable coding
is the coefficient-ring code of `0`.  This is the concrete code layer behind
Rabin's effective indexing of `R = F[x₁,x₂,…]`; Rabin justifies admissibility
from the computable-field hypothesis (`rabin.tex`:357: "Since F is computable,
i_R is an admissible indexing of R."). -/
def zeroCode (n : ℕ) : ℕ :=
  Encodable.encode (0 : MvPolynomial (Fin n) F)

variable {F}

@[simp] theorem zeroCode_succ (n : ℕ) :
    zeroCode F (n + 1) = 0 := by
  simp only [zeroCode]
  unfold instPrimcodableMvPolynomialFin mvTower
  rw [Encodable.encode_ofEquiv]
  simp

@[simp] theorem zeroCode_zero :
    zeroCode F 0 = Encodable.encode (0 : F) := by
  simp only [zeroCode]
  unfold instPrimcodableMvPolynomialFin mvTower
  rw [Encodable.encode_ofEquiv]
  simp

/-- The canonical code of the unit polynomial at a finite level. -/
def oneCode (n : ℕ) : ℕ :=
  Encodable.encode (1 : MvPolynomial (Fin n) F)

/-- At level zero, the unit code is the coefficient-ring unit code transported
through the empty-variable equivalence. -/
@[simp] theorem oneCode_zero :
    oneCode (F := F) 0 = Encodable.encode (1 : F) := by
  simp only [oneCode]
  unfold instPrimcodableMvPolynomialFin mvTower
  rw [Encodable.encode_ofEquiv]
  simp

/-- Mathlib's list code sends a singleton numeric list to `succ (pair c 0)`. -/
@[simp] theorem encode_singleton_list (c : ℕ) :
    Encodable.encode ([c] : List ℕ) = Nat.succ (Nat.pair c 0) := rfl

/-- Mathlib's list code sends a two-element numeric list to the corresponding
nested pair code. -/
@[simp] theorem encode_pair_list (a b : ℕ) :
    Encodable.encode ([a, b] : List ℕ) =
      Nat.succ (Nat.pair a (Nat.succ (Nat.pair b 0))) := rfl

/-- A primitive-recursive zero-code recursion that agrees with `zeroCode`.
This is used only for code-level bookkeeping; it avoids computing encodings of
polynomial objects from the input level. -/
def zeroCodeRec : ℕ → ℕ
  | 0 => Encodable.encode (0 : F)
  | _ + 1 => 0

/-- The recursive zero-code function agrees with the canonical zero code. -/
@[simp] theorem zeroCodeRec_eq_zeroCode (n : ℕ) :
    zeroCodeRec (F := F) n = zeroCode (F := F) n := by
  cases n <;> simp [zeroCodeRec]

/-- A primitive-recursive unit-code recursion that agrees with `oneCode` over
nontrivial coefficient rings. -/
def oneCodeRec : ℕ → ℕ
  | 0 => Encodable.encode (1 : F)
  | n + 1 => Nat.succ (Nat.pair (oneCodeRec n) 0)

/-- At a successor level, the tower code is the list code of the coefficient
codes.  This exposes the exact instance chain
`MvPolynomial (Fin (n+1)) ≃ Polynomial (MvPolynomial (Fin n)) ≃ coefficient
list`, avoiding ad hoc instance arguments in later proofs. -/
theorem encode_succ_eq_encode_coeff_codes (n : ℕ)
    (p : MvPolynomial (Fin (n + 1)) F) :
    Encodable.encode p =
      Encodable.encode ((polyCoeffs (towerEquiv F n p)).map Encodable.encode : List ℕ) := by
  unfold instPrimcodableMvPolynomialFin
  simp only [mvTower]
  rw [Encodable.encode_ofEquiv]
  unfold instPrimcodablePolynomial Primcodable.ofEquiv Encodable.ofEquiv
    Encodable.ofLeftInverse Encodable.ofLeftInjection Primcodable.subtype
  change Encodable.encode (polyCoeffs (towerEquiv F n p)) =
    Encodable.encode
      ((polyCoeffs (towerEquiv F n p)).map
        (@Encodable.encode _ ((mvTower F n).prim).toEncodable) : List ℕ)
  exact List.encode_eq_encode_map_encode _

/-- At a successor level over a nontrivial coefficient ring, the unit is coded
as the singleton list containing the previous-level unit code. -/
@[simp] theorem oneCode_succ [Nontrivial F] (n : ℕ) :
    oneCode (F := F) (n + 1) =
      Encodable.encode ([oneCode (F := F) n] : List ℕ) := by
  simp only [oneCode]
  rw [encode_succ_eq_encode_coeff_codes (F := F) n (1 : MvPolynomial (Fin (n + 1)) F)]
  have htower :
      towerEquiv F n (1 : MvPolynomial (Fin (n + 1)) F) =
        Polynomial.C (1 : MvPolynomial (Fin n) F) := by
    exact map_one (towerEquiv F n)
  rw [htower]
  change Encodable.encode
      ((polyCoeffs (Polynomial.C (1 : MvPolynomial (Fin n) F))).map Encodable.encode : List ℕ) =
    Nat.succ (Nat.pair (Encodable.encode (1 : MvPolynomial (Fin n) F)) 0)
  rw [polyCoeffs_C]
  simp [one_ne_zero]

/-- The recursive unit-code function agrees with the canonical unit code over
nontrivial coefficient rings. -/
@[simp] theorem oneCodeRec_eq_oneCode [Nontrivial F] (n : ℕ) :
    oneCodeRec (F := F) n = oneCode (F := F) n := by
  induction n with
  | zero => simp [oneCodeRec]
  | succ n ih =>
      rw [oneCodeRec, ih, oneCode_succ (F := F) n]
      rfl

/-- The level-zero tower code is the coefficient-ring code transported through
the empty-variable equivalence. -/
theorem encode_fin_zero_eq_encode_coeff (p : MvPolynomial (Fin 0) F) :
    Encodable.encode p =
      Encodable.encode ((MvPolynomial.isEmptyAlgEquiv F (Fin 0)) p) := by
  unfold instPrimcodableMvPolynomialFin mvTower
  rw [Encodable.encode_ofEquiv]
  rfl

theorem encode_isEmptyAlgEquiv_symm (a : F) :
    Encodable.encode
      ((MvPolynomial.isEmptyAlgEquiv F (Fin 0)).symm a : MvPolynomial (Fin 0) F) =
        Encodable.encode a := by
  unfold instPrimcodableMvPolynomialFin mvTower
  rw [Encodable.encode_ofEquiv]
  simp

/-- Whether `c` is a canonical tower code for level `n`.

The level-zero case tests exact membership in the image of the coefficient
ring coding.  The successor case reads `c` as the list code of coefficient
codes, recursively validates each coefficient, and enforces the no-trailing
zero invariant of `Polynomial`'s coefficient-list coding. -/
def validCode : ℕ → ℕ → Bool
  | 0, c =>
      decide ((Encodable.decode (α := F) c).map Encodable.encode = some c)
  | n + 1, c =>
      let l := Denumerable.ofNat (List ℕ) c
      l.all (fun e => validCode n e) &&
        decide (l.getLast? ≠ some (zeroCode (F := F) n))

/-- Exact level codes are valid canonical codes that do not descend one tower
level.  At level zero every valid coefficient-ring code is exact; at positive
levels the coefficient list must have length at least two. -/
def exactCode (n c : ℕ) : Bool :=
  validCode (F := F) n c &&
    decide (n = 0 ∨ 2 ≤ (Denumerable.ofNat (List ℕ) c).length)

@[simp] theorem validCode_zero (c : ℕ) :
    validCode (F := F) 0 c =
      decide ((Encodable.decode (α := F) c).map Encodable.encode = some c) := rfl

@[simp] theorem validCode_succ (n c : ℕ) :
    validCode (F := F) (n + 1) c =
      let l := Denumerable.ofNat (List ℕ) c
      l.all (fun e => validCode (F := F) n e) &&
        decide (l.getLast? ≠ some (zeroCode (F := F) n)) := rfl

@[simp] theorem exactCode_eq (n c : ℕ) :
    exactCode (F := F) n c =
      (validCode (F := F) n c &&
        decide (n = 0 ∨ 2 ≤ (Denumerable.ofNat (List ℕ) c).length)) := rfl

lemma zeroCode_eq_ite (k : ℕ) :
    zeroCode (F := F) k = if k = 0 then Encodable.encode (0 : F) else 0 := by
  cases k <;> simp

lemma validCode_zero_eq_decide_succ (c : ℕ) :
    validCode (F := F) 0 c =
      decide (Encodable.encode (Encodable.decode (α := F) c) = c + 1) := by
  rw [validCode_zero]
  cases h : Encodable.decode (α := F) c with
  | none =>
      simp [Encodable.encode_none]
  | some a =>
      simp [Encodable.encode_some, Nat.succ_eq_add_one]

lemma all_eq_mapfold (l : List ℕ) (p : ℕ → Bool) :
    l.all p = (l.map p).foldr (· && ·) true := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

private def validStep (table : List Bool) : Bool :=
  let N := table.length
  let n := N.unpair.1
  let c := N.unpair.2
  if n = 0 then
    decide (Encodable.encode (Encodable.decode (α := F) c) = c + 1)
  else
    let l := Denumerable.ofNat (List ℕ) c
    ((l.map fun e => table.getD (Nat.pair (n - 1) e) false).foldr (· && ·) true) &&
      !decide (l.getLast? = some (zeroCode (F := F) (n - 1)))

private lemma primrec_validStep :
    Primrec (validStep (F := F)) := by
  let len : List Bool → ℕ := fun t => t.length
  let nOf : List Bool → ℕ := fun t => t.length.unpair.1
  let cOf : List Bool → ℕ := fun t => t.length.unpair.2
  have hlen : Primrec len := Primrec.list_length
  have hn : Primrec nOf := by
    exact ((Primrec.fst.comp Primrec.unpair).comp hlen)
  have hc : Primrec cOf := by
    exact ((Primrec.snd.comp Primrec.unpair).comp hlen)
  have hF : Primrec fun c : ℕ => Encodable.encode (Encodable.decode (α := F) c) :=
    Primrec.encode.comp Primrec.decode
  have hFtest : Primrec fun c : ℕ =>
      decide (Encodable.encode (Encodable.decode (α := F) c) = c + 1) := by
    exact (@Primrec.eq ℕ _).decide.comp hF (Primrec.succ.comp Primrec.id)
  have hl : Primrec fun t : List Bool => Denumerable.ofNat (List ℕ) (cOf t) :=
    (Primrec.ofNat (List ℕ)).comp hc
  have hpredn : Primrec fun t : List Bool => nOf t - 1 :=
    Primrec.nat_sub.comp hn (Primrec.const 1)
  have hidx : Primrec₂ fun (t : List Bool) (e : ℕ) => Nat.pair (nOf t - 1) e := by
    exact Primrec₂.natPair.comp₂ (hpredn.comp₂ Primrec₂.left) Primrec₂.right
  have hlook : Primrec₂ fun (t : List Bool) (e : ℕ) =>
      t.getD (Nat.pair (nOf t - 1) e) false := by
    exact (Primrec.list_getD false).comp₂ Primrec₂.left hidx
  have hmap : Primrec fun t : List Bool =>
      (Denumerable.ofNat (List ℕ) (cOf t)).map
        (fun e => t.getD (Nat.pair (nOf t - 1) e) false) :=
    Primrec.list_map hl hlook
  have hfold : Primrec fun t : List Bool =>
      ((Denumerable.ofNat (List ℕ) (cOf t)).map
        (fun e => t.getD (Nat.pair (nOf t - 1) e) false)).foldr (· && ·) true := by
    have hstep : Primrec₂ (fun (_ : List Bool) (p : Bool × Bool) => p.1 && p.2) :=
      (Primrec.and.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
    exact Primrec.list_foldr (h := fun (_ : List Bool) (p : Bool × Bool) => p.1 && p.2)
      hmap (Primrec.const true) hstep
  have hlast : Primrec fun t : List Bool =>
      (Denumerable.ofNat (List ℕ) (cOf t)).getLast? := by
    refine (Primrec.list_head?.comp (Primrec.list_reverse.comp hl)).of_eq ?_
    intro t
    exact List.head?_reverse
  have hzc_nat : Primrec fun t : List Bool => zeroCode (F := F) (nOf t - 1) := by
    refine (Primrec.ite
      ((@Primrec.eq ℕ _).comp hpredn (Primrec.const 0))
      (Primrec.const (Encodable.encode (0 : F))) (Primrec.const 0)).of_eq ?_
    intro t
    rw [zeroCode_eq_ite]
  have hzc : Primrec fun t : List Bool => some (zeroCode (F := F) (nOf t - 1)) :=
    Primrec.option_some.comp hzc_nat
  have heqLast : Primrec fun t : List Bool =>
      decide ((Denumerable.ofNat (List ℕ) (cOf t)).getLast? =
        some (zeroCode (F := F) (nOf t - 1))) := by
    exact (@Primrec.eq (Option ℕ) _).decide.comp hlast hzc
  have hneq : Primrec fun t : List Bool =>
      !decide ((Denumerable.ofNat (List ℕ) (cOf t)).getLast? =
        some (zeroCode (F := F) (nOf t - 1))) :=
    Primrec.not.comp heqLast
  have hand : Primrec fun t : List Bool =>
      (((Denumerable.ofNat (List ℕ) (cOf t)).map
        (fun e => t.getD (Nat.pair (nOf t - 1) e) false)).foldr (· && ·) true) &&
        !decide ((Denumerable.ofNat (List ℕ) (cOf t)).getLast? =
          some (zeroCode (F := F) (nOf t - 1))) :=
    Primrec.and.comp hfold hneq
  have hzero : PrimrecPred fun t : List Bool => nOf t = 0 :=
    (@Primrec.eq ℕ _).comp hn (Primrec.const 0)
  refine (Primrec.ite hzero (hFtest.comp hc) hand).of_eq ?_
  intro t
  simp [validStep, nOf, cOf]

theorem validCode_zero_iff (c : ℕ) :
    validCode (F := F) 0 c = true ↔ ∃ a : F, Encodable.encode a = c := by
  simp only [validCode_zero, decide_eq_true_eq]
  constructor
  · intro h
    rcases hdec : Encodable.decode (α := F) c with _ | a
    · simp [hdec] at h
    · have hsome : some (Encodable.encode a) = some c := by
        simpa only [hdec, Option.map_some] using h
      exact ⟨a, Option.some.inj hsome⟩
  · rintro ⟨a, rfl⟩
    simp [Encodable.encodek]

/-- The code validator recognizes exactly the image of the finite-level tower
encoder. -/
theorem validCode_iff (n c : ℕ) :
    validCode (F := F) n c = true ↔
      ∃ p : MvPolynomial (Fin n) F, Encodable.encode p = c := by
  revert c
  induction n with
  | zero =>
      intro c
      constructor
      · intro h
        rcases (validCode_zero_iff (F := F) c).mp h with ⟨a, ha⟩
        refine ⟨(MvPolynomial.isEmptyAlgEquiv F (Fin 0)).symm a, ?_⟩
        rw [encode_isEmptyAlgEquiv_symm, ha]
      · rintro ⟨p, hp⟩
        exact (validCode_zero_iff (F := F) c).mpr
          ⟨(MvPolynomial.isEmptyAlgEquiv F (Fin 0)) p,
            by rw [← encode_fin_zero_eq_encode_coeff, hp]⟩
  | succ n ih =>
      intro c
      constructor
      · intro h
        simp only [validCode_succ] at h
        let l := Denumerable.ofNat (List ℕ) c
        have hand : (l.all (fun e => validCode (F := F) n e) = true) ∧
            decide (l.getLast? ≠ some (zeroCode F n)) = true :=
          Bool.and_eq_true_iff.mp h
        have hall : ∀ e ∈ l, validCode (F := F) n e = true :=
          List.all_eq_true.mp hand.1
        have hlast : l.getLast? ≠ some (zeroCode F n) :=
          of_decide_eq_true hand.2
        have hex : ∀ e : {e // e ∈ l},
            ∃ p : MvPolynomial (Fin n) F, Encodable.encode p = e.1 :=
          fun e => (ih e.1).mp (hall e.1 e.2)
        choose ps hps using hex
        let coeffs : List (MvPolynomial (Fin n) F) := l.attach.map ps
        let P : Polynomial (MvPolynomial (Fin n) F) := polyOfList coeffs
        refine ⟨(towerEquiv F n).symm P, ?_⟩
        have hcoeff_codes : coeffs.map Encodable.encode = l := by
          dsimp [coeffs]
          apply List.ext_getElem
          · simp
          · intro i hi₁ hi₂
            simp only [List.getElem_map]
            calc
              Encodable.encode (ps (l.attach[i]'(by simpa using hi₂))) =
                  (l.attach[i]'(by simpa using hi₂)).1 := hps _
              _ = l[i] := by simp
        have hcoeff_last : coeffs.getLast? ≠ some 0 := by
          intro hz
          apply hlast
          rw [← hcoeff_codes, List.getLast?_map, hz]
          rfl
        have hcanon : polyCoeffs P = coeffs := by
          dsimp [P]
          have hright :=
            (polyEquivList (R := MvPolynomial (Fin n) F)).right_inv
              ⟨coeffs, hcoeff_last⟩
          exact Subtype.ext_iff.mp hright
        calc
          Encodable.encode ((towerEquiv F n).symm P) =
              Encodable.encode
                ((polyCoeffs (towerEquiv F n ((towerEquiv F n).symm P))).map
                  Encodable.encode : List ℕ) :=
            encode_succ_eq_encode_coeff_codes (F := F) n ((towerEquiv F n).symm P)
          _ = Encodable.encode (coeffs.map Encodable.encode : List ℕ) := by
            simp [hcanon]
          _ = Encodable.encode l := by rw [hcoeff_codes]
          _ = c := Denumerable.encode_ofNat (α := List ℕ) c
      · rintro ⟨p, hp⟩
        let coeffs := polyCoeffs (towerEquiv F n p)
        have hl : Denumerable.ofNat (List ℕ) c =
            (coeffs.map Encodable.encode : List ℕ) := by
          rw [← hp, encode_succ_eq_encode_coeff_codes (F := F) n p]
          exact Denumerable.ofNat_encode _
        simp only [validCode_succ, hl]
        apply Bool.and_eq_true_iff.mpr
        constructor
        · apply List.all_eq_true.mpr
          intro e he
          rw [List.mem_map] at he
          rcases he with ⟨q, _hqmem, rfl⟩
          exact (ih (Encodable.encode q)).mpr ⟨q, rfl⟩
        · apply decide_eq_true
          intro hlast
          have hpoly_last := polyCoeffs_getLast?_ne_zero (towerEquiv F n p)
          rw [List.getLast?_map] at hlast
          rw [zeroCode] at hlast
          rcases Option.map_eq_some_iff.mp hlast with ⟨q, hq_last, hq_code⟩
          apply hpoly_last
          rw [hq_last]
          exact congr_arg some (Encodable.encode_injective hq_code)

/-- Descending from a successor-level list element gives a smaller paired
recursive argument. -/
lemma pair_mem_lt {n c e : ℕ} (he : e ∈ Denumerable.ofNat (List ℕ) c) :
    Nat.pair n e < Nat.pair (n + 1) c := by
  have hlt : e < c := by
    simpa [Denumerable.encode_ofNat (α := List ℕ) c] using
      (List.encode_mem_lt_encode (α := ℕ) (a := e)
        (l := Denumerable.ofNat (List ℕ) c) he)
  exact (Nat.pair_lt_pair_left e (Nat.lt_succ_self n)).trans
    (Nat.pair_lt_pair_right (n + 1) hlt)

/-- The strong-recursion history table agrees with the recursive function at
any previous index. -/
lemma table_getD {σ : Type*} {f : ℕ → σ} {d : σ} {N i : ℕ} (h : i < N) :
    ((List.range N).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map]
  simp

/-- Primitive-recursive form of the code validator, with the recursive call
indexed by `Nat.pair level code`.

The successor-level table rebuild is intentionally split into a lookup map
followed by a closed Boolean fold, so the fold step does not capture the
current table or level. -/
theorem primrec_validCode :
    Primrec fun N : ℕ => validCode (F := F) N.unpair.1 N.unpair.2 := by
  let f : ℕ → Bool := fun N => validCode (F := F) N.unpair.1 N.unpair.2
  have H : ∀ N,
      validStep (F := F) ((List.range N).map f) = f N := by
    intro N
    dsimp [f]
    unfold validStep
    rw [List.length_map, List.length_range]
    cases hn : N.unpair.1 with
    | zero =>
        rw [validCode_zero_eq_decide_succ (F := F) N.unpair.2]
        simp [hn]
    | succ n =>
        let c := N.unpair.2
        let l := Denumerable.ofNat (List ℕ) c
        have hpair : Nat.pair (n + 1) c = N := by
          dsimp [c]
          simpa [hn] using (Nat.pair_unpair N)
        have hlookup : ∀ e ∈ l,
            ((List.range N).map fun i : ℕ =>
              validCode (F := F) i.unpair.1 i.unpair.2).getD
                (Nat.pair n e) false = validCode (F := F) n e := by
          intro e he
          rw [table_getD]
          · simp
          · dsimp [l, c] at he
            exact lt_of_lt_of_eq (pair_mem_lt (n := n) (c := c) he) hpair
        have hmap :
            (List.map
              (fun e =>
                (Option.map (fun i : ℕ => validCode (F := F) i.unpair.1 i.unpair.2)
                  (List.range N)[Nat.pair n e]?).getD false)
              (Denumerable.ofNat (List ℕ) N.unpair.2)) =
              List.map (fun e => validCode (F := F) n e)
                (Denumerable.ofNat (List ℕ) N.unpair.2) := by
          apply List.map_congr_left
          intro e he
          have he' : e ∈ l := by simpa [l, c] using he
          simpa [List.getD_eq_getElem?_getD] using hlookup e he'
        simp [hn, hmap, all_eq_mapfold]
  have hg : Primrec₂ (fun (_ : Unit) (table : List Bool) =>
      some (validStep (F := F) table)) := by
    exact (Primrec.option_some.comp (primrec_validStep (F := F).comp Primrec.snd)).to₂
  exact (Primrec.nat_strong_rec
    (fun (_ : Unit) N => validCode (F := F) N.unpair.1 N.unpair.2)
    hg (fun _ n => by simpa [f] using H n)).comp (Primrec.const ()) Primrec.id

/-- Primitive-recursive form of exact level-code validation. -/
theorem primrec_exactCode :
    Primrec fun N : ℕ => exactCode (F := F) N.unpair.1 N.unpair.2 := by
  have hn : Primrec fun N : ℕ => N.unpair.1 :=
    Primrec.fst.comp Primrec.unpair
  have hc : Primrec fun N : ℕ => N.unpair.2 :=
    Primrec.snd.comp Primrec.unpair
  have hl : Primrec fun N : ℕ => Denumerable.ofNat (List ℕ) N.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp hc
  have hllen : Primrec fun N : ℕ => (Denumerable.ofNat (List ℕ) N.unpair.2).length :=
    Primrec.list_length.comp hl
  have hzero : Primrec fun N : ℕ => decide (N.unpair.1 = 0) :=
    (@Primrec.eq ℕ _).decide.comp hn (Primrec.const 0)
  have hle : Primrec fun N : ℕ =>
      decide (2 ≤ (Denumerable.ofNat (List ℕ) N.unpair.2).length) :=
    Primrec.nat_le.decide.comp (Primrec.const 2) hllen
  have hor : Primrec fun N : ℕ =>
      decide (N.unpair.1 = 0) ||
        decide (2 ≤ (Denumerable.ofNat (List ℕ) N.unpair.2).length) :=
    Primrec.or.comp hzero hle
  have hand : Primrec fun N : ℕ =>
      validCode (F := F) N.unpair.1 N.unpair.2 &&
        (decide (N.unpair.1 = 0) ||
          decide (2 ≤ (Denumerable.ofNat (List ℕ) N.unpair.2).length)) :=
    Primrec.and.comp primrec_validCode hor
  refine hand.of_eq ?_
  intro N
  by_cases h0 : N.unpair.1 = 0 <;>
    by_cases hle : 2 ≤ (Denumerable.ofNat (List ℕ) N.unpair.2).length <;>
      simp [exactCode_eq, h0, hle]

/-- Canonical tower codes are exact at their least countable-variable level. -/
theorem exactCode_natTowerCode (p : MvPolynomial ℕ F) :
    exactCode (F := F) (level (F := F) p)
      (Encodable.encode (restrictLevel (F := F) (level (F := F) p) p)) = true := by
  cases hlev : level (F := F) p with
  | zero =>
      let q := restrictLevel (F := F) 0 p
      have hvalid : validCode (F := F) 0 (Encodable.encode q) = true :=
        (validCode_iff (F := F) 0 (Encodable.encode q)).mpr ⟨q, rfl⟩
      rw [exactCode_eq]
      change validCode (F := F) 0 (Encodable.encode q) &&
        decide (0 = 0 ∨ 2 ≤ (Denumerable.ofNat (List ℕ) (Encodable.encode q)).length) = true
      simp [hvalid]
  | succ n =>
      let q := restrictLevel (F := F) (n + 1) p
      have hvalid : validCode (F := F) (n + 1) (Encodable.encode q) = true :=
        (validCode_iff (F := F) (n + 1) (Encodable.encode q)).mpr ⟨q, rfl⟩
      have hlen :
          2 ≤ (Denumerable.ofNat (List ℕ) (Encodable.encode q)).length := by
        by_contra hnot
        have hle_one :
            (Denumerable.ofNat (List ℕ) (Encodable.encode q)).length ≤ 1 := by
          omega
        have hlist :
            Denumerable.ofNat (List ℕ) (Encodable.encode q) =
              ((polyCoeffs (towerEquiv F n q)).map Encodable.encode : List ℕ) := by
          rw [encode_succ_eq_encode_coeff_codes (F := F) n q]
          exact Denumerable.ofNat_encode _
        have hcoeff_len :
            (polyCoeffs (towerEquiv F n q)).length ≤ 1 := by
          simpa [hlist, List.length_map] using hle_one
        have hnat : (towerEquiv F n q).natDegree = 0 :=
          _root_.Semicontinuity.natDegree_eq_zero_of_polyCoeffs_length_le_one hcoeff_len
        rcases (_root_.Semicontinuity.natDegree_towerEquiv_eq_zero_iff F n q).mp hnat with
          ⟨r, hr⟩
        have hp_eq :
            p = inclLevel (F := F) (n + 1) q := by
          exact (incl_restrictLevel_of_level_le (F := F) (n := n + 1) (p := p)
            (by omega)).symm
        have hdesc :
            level (F := F) p ≤ n := by
          rw [hp_eq]
          exact (level_inclLevel_succ_le_iff (F := F) n q).mpr ⟨r, hr⟩
        omega
      rw [exactCode_eq]
      dsimp [q] at hvalid hlen ⊢
      rw [hvalid]
      simp [hlen]

/-- Exact finite-level codes decode to a polynomial whose countable inclusion
has exactly that level. -/
theorem exactCode_round_trip (n c : ℕ) (h : exactCode (F := F) n c = true) :
    ∃ p : MvPolynomial (Fin n) F,
      Encodable.encode p = c ∧
        level (F := F) (inclLevel (F := F) n p) = n := by
  rw [exactCode_eq] at h
  have hv : validCode (F := F) n c = true := (Bool.and_eq_true_iff.mp h).1
  have hexact :
      n = 0 ∨ 2 ≤ (Denumerable.ofNat (List ℕ) c).length :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
  rcases (validCode_iff (F := F) n c).mp hv with ⟨p, hp⟩
  refine ⟨p, hp, ?_⟩
  have hle : level (F := F) (inclLevel (F := F) n p) ≤ n :=
    level_inclLevel_le (F := F) n p
  apply le_antisymm hle
  cases n with
  | zero =>
      exact Nat.zero_le _
  | succ m =>
      have hlen : 2 ≤ (Denumerable.ofNat (List ℕ) c).length := by
        rcases hexact with hzero | hlen
        · omega
        · exact hlen
      by_contra hnot
      have hdesc : level (F := F) (inclLevel (F := F) (m + 1) p) ≤ m := by
        omega
      rcases (level_inclLevel_succ_le_iff (F := F) m p).mp hdesc with ⟨r, hr⟩
      have hnat : (towerEquiv F m p).natDegree = 0 := by
        rw [hr, towerEquiv_rename_castSucc]
        exact Polynomial.natDegree_C r
      have hcoeff_len : (polyCoeffs (towerEquiv F m p)).length ≤ 1 :=
        _root_.Semicontinuity.polyCoeffs_length_le_one_of_natDegree_eq_zero hnat
      have hlist :
          Denumerable.ofNat (List ℕ) c =
            ((polyCoeffs (towerEquiv F m p)).map Encodable.encode : List ℕ) := by
        rw [← hp, encode_succ_eq_encode_coeff_codes (F := F) m p]
        exact Denumerable.ofNat_encode _
      have : (Denumerable.ofNat (List ℕ) c).length ≤ 1 := by
        simpa [hlist, List.length_map] using hcoeff_len
      omega

/-! ## Code-level lifting and canonical descent -/

/-- Lift one finite tower code from level `n` to level `n + 1` by viewing the
polynomial as independent of the new last variable.  The zero polynomial stays
at the successor-level zero code; every nonzero code becomes a singleton
coefficient list. -/
def liftOnce (n c : ℕ) : ℕ :=
  if c = zeroCode (F := F) n then 0 else Nat.succ (Nat.pair c 0)

/-- `liftOnce` correctly codes renaming along `Fin.castSucc`. -/
theorem liftOnce_encode (n : ℕ) (q : MvPolynomial (Fin n) F) :
    liftOnce (F := F) n (Encodable.encode q) =
      Encodable.encode (MvPolynomial.rename Fin.castSucc q :
        MvPolynomial (Fin (n + 1)) F) := by
  by_cases hq : q = 0
  · subst q
    rw [liftOnce, if_pos (show
      Encodable.encode (0 : MvPolynomial (Fin n) F) = zeroCode (F := F) n from rfl)]
    change 0 = Encodable.encode (0 : MvPolynomial (Fin (n + 1)) F)
    rw [← zeroCode_succ (F := F) n]
    rfl
  · rw [liftOnce, if_neg]
    · rw [encode_succ_eq_encode_coeff_codes (F := F) n
        (MvPolynomial.rename Fin.castSucc q)]
      rw [towerEquiv_rename_castSucc]
      symm
      change Encodable.encode
          ((polyCoeffs (Polynomial.C q)).map Encodable.encode : List ℕ) =
        Nat.succ (Nat.pair (Encodable.encode q) 0)
      rw [polyCoeffs_C]
      simp [hq]
    · intro h
      apply hq
      rw [zeroCode] at h
      exact Encodable.encode_injective h

/-- Iterate `liftOnce` through a fixed amount of successor finite tower levels.

This is the code-level re-indexing operation for Rabin's admissible indexing
of `F[x₁,x₂,…]` (`rabin.tex`:357). -/
def liftIter : ℕ → ℕ → ℕ → ℕ
  | 0, _, c => c
  | k + 1, lvl, c => liftIter k (lvl + 1) (liftOnce (F := F) lvl c)

/-- Lift a code from level `n` to level `m`, using no fuel when `m ≤ n`.

This is the finite-level code transport behind canonical re-indexing for
Rabin's admissible indexing (`rabin.tex`:357). -/
def liftTo (m n c : ℕ) : ℕ :=
  liftIter (F := F) (m - n) n c

omit [Primcodable F] [ComputableRing F] in
theorem restrict_succ_step (n : ℕ) (p : MvPolynomial ℕ F)
    (hp : level (F := F) p ≤ n) :
    MvPolynomial.rename Fin.castSucc (restrictLevel (F := F) n p) =
      restrictLevel (F := F) (n + 1) p := by
  apply MvPolynomial.rename_injective (R := F)
    (Fin.val : Fin (n + 1) → ℕ) Fin.val_injective
  change inclLevel (F := F) (n + 1)
      (MvPolynomial.rename Fin.castSucc (restrictLevel (F := F) n p)) =
    inclLevel (F := F) (n + 1) (restrictLevel (F := F) (n + 1) p)
  rw [inclLevel_rename_castSucc]
  rw [incl_restrictLevel_of_level_le (F := F) hp,
    incl_restrictLevel_of_level_le (F := F) (le_trans hp (Nat.le_succ n))]

theorem liftIter_encode_restrict (k n : ℕ) (p : MvPolynomial ℕ F)
    (hp : level (F := F) p ≤ n) :
    liftIter (F := F) k n
        (Encodable.encode (restrictLevel (F := F) n p)) =
      Encodable.encode (restrictLevel (F := F) (n + k) p) := by
  revert n
  induction k with
  | zero =>
      intro n hp
      simp [liftIter]
  | succ k ih =>
      intro n hp
      rw [liftIter]
      rw [liftOnce_encode (F := F) n (restrictLevel (F := F) n p)]
      rw [restrict_succ_step (F := F) n p hp]
      have hp' : level (F := F) p ≤ n + 1 := le_trans hp (Nat.le_succ n)
      have h := ih (n + 1) hp'
      rw [show n + 1 + k = n + (k + 1) by omega] at h
      exact h

/-- Lifting a finite-level code for a restricted countable polynomial produces
the finite-level code for the same polynomial at the target level. -/
theorem liftTo_encode_restrict {n m : ℕ} (h : n ≤ m) (p : MvPolynomial ℕ F)
    (hp : level (F := F) p ≤ n) :
    liftTo (F := F) m n
        (Encodable.encode (restrictLevel (F := F) n p)) =
      Encodable.encode (restrictLevel (F := F) m p) := by
  rw [liftTo]
  have hm : n + (m - n) = m := Nat.add_sub_cancel' h
  rw [← hm]
  rw [show n + (m - n) - n = m - n by omega]
  exact liftIter_encode_restrict (F := F) (m - n) n p hp

/-- One canonical descent step for finite tower codes.

At a successor level, empty coefficient lists descend to the zero code and
singleton coefficient lists descend to their sole coefficient.  Longer lists
are already exact.  This is Rabin's canonical re-indexing of the admissible
coding (`rabin.tex`:357). -/
def canonDownStep : ℕ × ℕ → ℕ × ℕ
  | (0, c) => (0, c)
  | (lvl + 1, c) =>
      let l := Denumerable.ofNat (List ℕ) c
      if l.length = 0 then (lvl, zeroCode (F := F) lvl)
      else if l.length = 1 then (lvl, l.headD 0)
      else (lvl + 1, c)

/-- Fuelled canonical descent for finite tower codes.

The fuel is an upper bound on the starting level.  It repeatedly applies
`canonDownStep`, implementing the canonical re-indexing used for Rabin's
admissible indexing (`rabin.tex`:357). -/
def canonDownAux : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, s => s
  | k + 1, s => canonDownAux k (canonDownStep (F := F) s)

/-- Canonicalize a finite tower code by descending through empty or singleton
last-variable coefficient lists.

The output is the least level and the corresponding finite-level code for
Rabin's admissible indexing (`rabin.tex`:357). -/
def canonDown (m c : ℕ) : ℕ × ℕ :=
  canonDownAux (F := F) m (m, c)

@[simp] theorem canonDownAux_succ (k : ℕ) (s : ℕ × ℕ) :
    canonDownAux (F := F) (k + 1) s =
      canonDownAux (F := F) k (canonDownStep (F := F) s) := rfl

lemma canonDownAux_fixed {s : ℕ × ℕ}
    (hs : canonDownStep (F := F) s = s) :
    ∀ k, canonDownAux (F := F) k s = s := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [canonDownAux_succ, hs, ih]

lemma ofNat_encode_coeff_codes (n : ℕ) (q : MvPolynomial (Fin (n + 1)) F) :
    Denumerable.ofNat (List ℕ) (Encodable.encode q) =
      ((polyCoeffs (towerEquiv F n q)).map Encodable.encode : List ℕ) := by
  rw [encode_succ_eq_encode_coeff_codes (F := F) n q]
  exact Denumerable.ofNat_encode _

omit [Primcodable F] [ComputableRing F] in
lemma polyCoeffs_eq_nil_iff {P : Polynomial (MvPolynomial (Fin n) F)} :
    polyCoeffs P = [] ↔ P = 0 := by
  constructor
  · intro h
    calc
      P = polyOfList (polyCoeffs P) := (polyOfList_polyCoeffs P).symm
      _ = 0 := by simp [h, polyOfList]
  · intro h
    subst P
    simp

omit [Primcodable F] [ComputableRing F] in
lemma poly_eq_C_of_polyCoeffs_eq_singleton
    {P : Polynomial (MvPolynomial (Fin n) F)}
    {q : MvPolynomial (Fin n) F} (h : polyCoeffs P = [q]) :
    P = Polynomial.C q := by
  calc
    P = polyOfList (polyCoeffs P) := (polyOfList_polyCoeffs P).symm
    _ = Polynomial.C q := by
      apply Polynomial.ext
      intro i
      cases i <;> simp [h, polyOfList_coeff, Polynomial.coeff_C]

lemma list_map_eq_singleton_iff {α β : Type*} {f : α → β} {xs : List α} {y : β} :
    xs.map f = [y] ↔ ∃ x, xs = [x] ∧ f x = y := by
  cases xs with
  | nil => simp
  | cons a t =>
      cases t with
      | nil => simp
      | cons b t => simp

lemma list_eq_singleton_headD_of_length_eq_one (l : List ℕ)
    (h : l.length = 1) :
    l = [l.headD 0] := by
  cases l with
  | nil => simp at h
  | cons a t =>
      cases t with
      | nil => simp
      | cons b t => simp at h

lemma list_head?_getD_eq_headD (l : List ℕ) :
    l.head?.getD 0 = l.headD 0 := by
  cases l <;> rfl

omit [Primcodable F] [ComputableRing F] in
lemma inclLevel_zero_restrictLevel_zero (p : MvPolynomial (Fin 0) F) :
    restrictLevel (F := F) 0 (inclLevel (F := F) 0 p) = p := by
  simp

lemma canonDown_encode_zero_level (q : MvPolynomial (Fin 0) F) :
    canonDown (F := F) 0 (Encodable.encode q) =
      (level (F := F) (inclLevel (F := F) 0 q),
        Encodable.encode (restrictLevel (F := F)
          (level (F := F) (inclLevel (F := F) 0 q))
          (inclLevel (F := F) 0 q))) := by
  have hlevel : level (F := F) (inclLevel (F := F) 0 q) = 0 := by
    exact le_antisymm (level_inclLevel_le (F := F) 0 q) (Nat.zero_le _)
  rw [hlevel]
  simp [canonDown, canonDownAux]

/-- `canonDown` returns the least countable-variable level and its finite tower
code for an encoded finite-level polynomial. -/
theorem canonDown_encode (m : ℕ) (q : MvPolynomial (Fin m) F) :
    canonDown (F := F) m (Encodable.encode q) =
      (level (F := F) (inclLevel (F := F) m q),
        Encodable.encode (restrictLevel (F := F)
          (level (F := F) (inclLevel (F := F) m q)) (inclLevel (F := F) m q))) := by
  induction m with
  | zero =>
      exact canonDown_encode_zero_level (F := F) q
  | succ k ih =>
      let P : Polynomial (MvPolynomial (Fin k) F) := towerEquiv F k q
      let l : List ℕ := Denumerable.ofNat (List ℕ) (Encodable.encode q)
      have hl :
          l = ((polyCoeffs P).map Encodable.encode : List ℕ) := by
        dsimp [l, P]
        exact ofNat_encode_coeff_codes (F := F) k q
      rw [canonDown]
      change canonDownAux (F := F) (k + 1) (k + 1, Encodable.encode q) = _
      rw [canonDownAux_succ]
      by_cases hlen0 : l.length = 0
      · have hcoeff_nil : polyCoeffs P = [] := by
          have hcoeff_len0 : (polyCoeffs P).length = 0 := by
            simpa [hl, List.length_map] using hlen0
          cases hcoeff : polyCoeffs P with
          | nil => rfl
          | cons a t => simp [hcoeff] at hcoeff_len0
        have hP0 : P = 0 := polyCoeffs_eq_nil_iff (F := F).mp hcoeff_nil
        have hq0 : q = 0 := by
          apply (towerEquiv F k).injective
          simpa [P] using hP0
        subst q
        have hstep :
            canonDownStep (F := F) (k + 1,
                Encodable.encode (0 : MvPolynomial (Fin (k + 1)) F)) =
              (k, Encodable.encode (0 : MvPolynomial (Fin k) F)) := by
          simp [canonDownStep, l, hlen0, zeroCode]
        rw [hstep]
        have hih := ih (0 : MvPolynomial (Fin k) F)
        rw [canonDown] at hih
        rw [hih]
        simp [map_zero]
      · by_cases hlen1 : l.length = 1
        · let e := l.headD 0
          have hl_single : l = [e] := by
            exact list_eq_singleton_headD_of_length_eq_one l hlen1
          have hmap_single :
              (polyCoeffs P).map Encodable.encode = [e] := by
            simpa [hl_single] using hl.symm
          rcases list_map_eq_singleton_iff.mp hmap_single with
            ⟨q₀, hcoeff_single, hq₀_code⟩
          have hP_C : P = Polynomial.C q₀ :=
            poly_eq_C_of_polyCoeffs_eq_singleton (F := F) hcoeff_single
          have hq : q = MvPolynomial.rename Fin.castSucc q₀ := by
            apply (towerEquiv F k).injective
            rw [towerEquiv_rename_castSucc]
            exact hP_C
          have hstep :
              canonDownStep (F := F) (k + 1, Encodable.encode q) =
                (k, Encodable.encode q₀) := by
            have hhead : l.headD 0 = Encodable.encode q₀ := by
              rw [hl_single]
              simp [hq₀_code]
            have hhead' :
                (Denumerable.ofNat (List ℕ) (Encodable.encode q)).headD 0 =
                  Encodable.encode q₀ := by
              simpa [l] using hhead
            have hlen0' :
                ¬ (Denumerable.ofNat (List ℕ) (Encodable.encode q)).length = 0 := by
              simpa [l] using hlen0
            have hlen1' :
                (Denumerable.ofNat (List ℕ) (Encodable.encode q)).length = 1 := by
              simpa [l] using hlen1
            dsimp [canonDownStep]
            rw [if_neg hlen0', if_pos hlen1']
            exact Prod.ext rfl hhead'
          rw [hstep]
          have hih := ih q₀
          rw [canonDown] at hih
          rw [hih]
          rw [hq, inclLevel_rename_castSucc]
        · have hlen_ge2 : 2 ≤ l.length := by omega
          have hcoeff_ge2 : 2 ≤ (polyCoeffs P).length := by
            simpa [hl, List.length_map] using hlen_ge2
          have hnot_natDegree0 : P.natDegree ≠ 0 := by
            intro hnat
            have hle :=
              _root_.Semicontinuity.polyCoeffs_length_le_one_of_natDegree_eq_zero
                (R := MvPolynomial (Fin k) F) (P := P) hnat
            omega
          have hnot_desc :
              ¬ level (F := F) (inclLevel (F := F) (k + 1) q) ≤ k := by
            intro hdesc
            rcases (level_inclLevel_succ_le_iff (F := F) k q).mp hdesc with
              ⟨r, hr⟩
            apply hnot_natDegree0
            dsimp [P]
            rw [hr, towerEquiv_rename_castSucc]
            exact Polynomial.natDegree_C r
          have hlevel :
              level (F := F) (inclLevel (F := F) (k + 1) q) = k + 1 := by
            exact le_antisymm (level_inclLevel_le (F := F) (k + 1) q)
              (by omega)
          have hstep :
              canonDownStep (F := F) (k + 1, Encodable.encode q) =
                (k + 1, Encodable.encode q) := by
            simp [canonDownStep, l, hlen0, hlen1]
          rw [hstep]
          rw [canonDownAux_fixed (F := F) hstep k]
          rw [hlevel]
          simp

end CodeLayer

section CountableInstance

variable (F) [Primcodable F] [ComputableRing F]

/-- Decode a canonical least-level tower code for a countably-many-variable
polynomial.  The `Encodable.encode q = c` guard keeps the finite decoder from
accepting noncanonical aliases. -/
noncomputable def decodeNatTowerCode (N : ℕ) : Option (MvPolynomial ℕ F) :=
  let n := N.unpair.1
  let c := N.unpair.2
  (Encodable.decode (α := MvPolynomial (Fin n) F) c).bind fun q =>
    if Encodable.encode q = c ∧ level (F := F) (inclLevel (F := F) n q) = n then
      some (inclLevel (F := F) n q)
    else
      none

variable {F}

/-- Canonical `Encodable` instance for countably-many-variable polynomials:
pair the least finite level with the finite tower code at that level. -/
noncomputable instance (priority := 1000) instEncodableMvPolynomialNat :
    Encodable (MvPolynomial ℕ F) where
  encode := natTowerCode (F := F)
  decode := decodeNatTowerCode F
  encodek := by
    intro p
    unfold natTowerCode
    unfold decodeNatTowerCode
    rw [Nat.unpair_pair]
    change (Encodable.decode
        (α := MvPolynomial (Fin (level (F := F) p)) F)
        (Encodable.encode (restrictLevel (F := F) (level (F := F) p) p))).bind
        (fun a =>
          if Encodable.encode a =
                Encodable.encode (restrictLevel (F := F) (level (F := F) p) p) ∧
              level (F := F) (inclLevel (F := F) (level (F := F) p) a) =
                level (F := F) p then
            some (inclLevel (F := F) (level (F := F) p) a)
          else none) = some p
    rw [Encodable.encodek (restrictLevel (F := F) (level (F := F) p) p)]
    simp [incl_restrictLevel_level (F := F) p]

/-- Canonical `Primcodable` instance for countably-many-variable polynomials.

Mathlib provides a generic `Encodable` route through the representation of
`MvPolynomial` as a finitely supported object.  This high-priority instance is
the Rabin effective indexing: least finite level paired with the finite tower
code.  No generic `Primcodable (MvPolynomial ℕ F)` instance is reachable in
this checkout. -/
noncomputable instance (priority := 1000) instPrimcodableMvPolynomialNat :
    Primcodable (MvPolynomial ℕ F) where
  prim := by
    have encode_decodeNat (N : ℕ) :
        Encodable.encode (decodeNatTowerCode F N) =
          if exactCode (F := F) N.unpair.1 N.unpair.2 = true then N + 1 else 0 := by
      by_cases hN : exactCode (F := F) N.unpair.1 N.unpair.2 = true
      · rcases exactCode_round_trip (F := F) N.unpair.1 N.unpair.2 hN with
          ⟨p, hp, hlevel⟩
        have hdec :
            Encodable.decode (α := MvPolynomial (Fin N.unpair.1) F) N.unpair.2 =
              some p := by
          rw [← hp, Encodable.encodek]
        have henc_incl :
            Encodable.encode (inclLevel (F := F) N.unpair.1 p) = N := by
          change natTowerCode (F := F) (inclLevel (F := F) N.unpair.1 p) = N
          unfold natTowerCode
          rw [hlevel, restrict_inclLevel, hp, Nat.pair_unpair]
        rw [if_pos hN]
        simp [decodeNatTowerCode, hdec, hp, hlevel, henc_incl, Encodable.encode_some]
      · have hnone : decodeNatTowerCode F N = none := by
          unfold decodeNatTowerCode
          cases hdec :
              Encodable.decode (α := MvPolynomial (Fin N.unpair.1) F) N.unpair.2 with
          | none =>
              simp [hdec]
          | some p =>
              by_cases hguard :
                  Encodable.encode p = N.unpair.2 ∧
                    level (F := F) (inclLevel (F := F) N.unpair.1 p) = N.unpair.1
              · have hex :
                    exactCode (F := F) N.unpair.1 N.unpair.2 = true := by
                  have htower :=
                    exactCode_natTowerCode (F := F)
                      (inclLevel (F := F) N.unpair.1 p)
                  rw [hguard.2, restrict_inclLevel, hguard.1] at htower
                  exact htower
                exact (hN hex).elim
              · simp [hdec, hguard]
        rw [if_neg hN, hnone]
        simp [Encodable.encode_none]
    have hpred : PrimrecPred fun N : ℕ =>
        exactCode (F := F) N.unpair.1 N.unpair.2 = true :=
      (@Primrec.eq Bool _).comp primrec_exactCode (Primrec.const true)
    have hif : Primrec fun N : ℕ =>
        if exactCode (F := F) N.unpair.1 N.unpair.2 = true then N + 1 else 0 :=
      Primrec.ite hpred Primrec.succ (Primrec.const 0)
    exact Primrec.nat_iff.mp (hif.of_eq fun N => (encode_decodeNat N).symm)

/-- Public equation for the countable-variable canonical code. -/
theorem encode_eq_pair (p : MvPolynomial ℕ F) :
    Encodable.encode p =
      Nat.pair (level (F := F) p)
        (Encodable.encode (restrictLevel (F := F) (level (F := F) p) p)) := by
  rfl

/-- Pairing the output of `canonDown` recovers the canonical
countable-variable code of the included polynomial. -/
theorem canonDown_encode_pair (m : ℕ) (q : MvPolynomial (Fin m) F) :
    Nat.pair (canonDown (F := F) m (Encodable.encode q)).1
      (canonDown (F := F) m (Encodable.encode q)).2 =
      Encodable.encode (inclLevel (F := F) m q) := by
  rw [canonDown_encode (F := F) m q]
  rw [encode_eq_pair]

/-- Explicit canonical code of the countable variable `X i` over a nontrivial
coefficient ring.  The nontrivial hypothesis is used only for
`MvPolynomial.vars_X` and `polyCoeffs_X`; fields satisfy it. -/
theorem encode_mvPolynomialNat_X [Nontrivial F] (i : ℕ) :
    Encodable.encode (MvPolynomial.X i : MvPolynomial ℕ F) =
      Nat.pair (i + 1)
        (Encodable.encode ([zeroCode (F := F) i, oneCode (F := F) i] : List ℕ)) := by
  have hlevel :
      level (F := F) (MvPolynomial.X i : MvPolynomial ℕ F) = i + 1 := by
    simp [level, MvPolynomial.vars_X]
  have hrestr :
      restrictLevel (F := F) (i + 1) (MvPolynomial.X i : MvPolynomial ℕ F) =
        (MvPolynomial.X (Fin.last i) : MvPolynomial (Fin (i + 1)) F) := by
    apply MvPolynomial.rename_injective (R := F)
      (Fin.val : Fin (i + 1) → ℕ) Fin.val_injective
    change inclLevel (F := F) (i + 1)
        (restrictLevel (F := F) (i + 1) (MvPolynomial.X i : MvPolynomial ℕ F)) =
      inclLevel (F := F) (i + 1)
        (MvPolynomial.X (Fin.last i) : MvPolynomial (Fin (i + 1)) F)
    rw [incl_restrictLevel_of_level_le (F := F)]
    · simp [inclLevel, Fin.last]
    · rw [hlevel]
  have htower :
      towerEquiv F i (MvPolynomial.X (Fin.last i) :
          MvPolynomial (Fin (i + 1)) F) =
        (Polynomial.X : Polynomial (MvPolynomial (Fin i) F)) := by
    rw [towerEquiv, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
      MvPolynomial.rename_X]
    simp [finSuccEquivLast_last, MvPolynomial.optionEquivLeft_X_none]
  rw [encode_eq_pair, hlevel, hrestr]
  rw [encode_succ_eq_encode_coeff_codes (F := F) i
    (MvPolynomial.X (Fin.last i) : MvPolynomial (Fin (i + 1)) F)]
  rw [htower, polyCoeffs_X]
  rfl

/-- The least finite level is computable from the canonical code. -/
theorem computable_level :
    Computable fun p : MvPolynomial ℕ F => level (F := F) p := by
  have henc :
      Computable (@Encodable.encode (MvPolynomial ℕ F) instEncodableMvPolynomialNat) :=
    Computable.encode
  have hunpair : Computable fun n : ℕ => n.unpair.1 :=
    (Primrec.fst.comp Primrec.unpair).to_comp
  exact (hunpair.comp henc).of_eq fun p => by
    rw [encode_eq_pair]
    simp

/-! ## Code-level arithmetic and evaluation -/

def trimTrailingStep (z : ℕ) (a : ℕ) (r : List ℕ) : List ℕ :=
  if r = [] then if a = z then [] else [a] else a :: r

def trimTrailing (z : ℕ) (l : List ℕ) : List ℕ :=
  l.foldr (fun a r => trimTrailingStep z a r) []

def addCodeLists (z : ℕ) (f : ℕ → ℕ → ℕ) (l₁ l₂ : List ℕ) : List ℕ :=
  (List.range (max l₁.length l₂.length)).map fun i => f (l₁.getD i z) (l₂.getD i z)

/-- Add two finite tower codes at a fixed level.  The successor case follows
the same coefficient-list shape as `Polynomial.addCoeffs`: zero-pad through
the maximum length, add the common coefficients recursively, then trim
trailing previous-level zero codes. -/
def addCodeAt : ℕ → ℕ → ℕ → ℕ
  | 0, c₁, c₂ =>
      Encodable.encode
        (((Encodable.decode (α := F) c₁).getD 0) +
          ((Encodable.decode (α := F) c₂).getD 0))
  | k + 1, c₁, c₂ =>
      let l₁ := Denumerable.ofNat (List ℕ) c₁
      let l₂ := Denumerable.ofNat (List ℕ) c₂
      Encodable.encode
        (trimTrailing (zeroCode (F := F) k)
          (addCodeLists (zeroCode (F := F) k) (addCodeAt k) l₁ l₂))

def addCode (N : ℕ) : ℕ :=
  addCodeAt (F := F) N.unpair.1 N.unpair.2.unpair.1 N.unpair.2.unpair.2

def sumCodes (z : ℕ) (add : ℕ → ℕ → ℕ) (xs : List ℕ) : ℕ :=
  xs.foldr (fun a acc => add a acc) z

def mulCodeLists (z : ℕ) (mul add : ℕ → ℕ → ℕ) (l₁ l₂ : List ℕ) : List ℕ :=
  (List.range (l₁.length + l₂.length)).map fun s =>
    sumCodes z add
      ((List.range (s + 1)).map fun i => mul (l₁.getD i z) (l₂.getD (s - i) z))

/-- Multiply two finite tower codes at a fixed level.  The successor case is
the coefficient-list convolution for univariate polynomial multiplication:
products are recursive level-`k` multiplications, while each convolution sum is
folded with the already-computable level-`k` addition code. -/
def mulCodeAt : ℕ → ℕ → ℕ → ℕ
  | 0, c₁, c₂ =>
      Encodable.encode
        (((Encodable.decode (α := F) c₁).getD 0) *
          ((Encodable.decode (α := F) c₂).getD 0))
  | k + 1, c₁, c₂ =>
      let l₁ := Denumerable.ofNat (List ℕ) c₁
      let l₂ := Denumerable.ofNat (List ℕ) c₂
      Encodable.encode
        (trimTrailing (zeroCode (F := F) k)
          (mulCodeLists (zeroCode (F := F) k) (mulCodeAt k) (addCodeAt (F := F) k) l₁ l₂))

def mulCode (N : ℕ) : ℕ :=
  mulCodeAt (F := F) N.unpair.1 N.unpair.2.unpair.1 N.unpair.2.unpair.2

def mvNatAddCode (e₁ e₂ : ℕ) : ℕ :=
  let n₁ := e₁.unpair.1
  let c₁ := e₁.unpair.2
  let n₂ := e₂.unpair.1
  let c₂ := e₂.unpair.2
  let m := max n₁ n₂
  let s :=
    canonDown (F := F) m
      (addCodeAt (F := F) m
        (liftTo (F := F) m n₁ c₁)
      (liftTo (F := F) m n₂ c₂))
  Nat.pair s.1 s.2

def mvNatMulCode (e₁ e₂ : ℕ) : ℕ :=
  let n₁ := e₁.unpair.1
  let c₁ := e₁.unpair.2
  let n₂ := e₂.unpair.1
  let c₂ := e₂.unpair.2
  let m := max n₁ n₂
  let s :=
    canonDown (F := F) m
      (mulCodeAt (F := F) m
        (liftTo (F := F) m n₁ c₁)
      (liftTo (F := F) m n₂ c₂))
  Nat.pair s.1 s.2


def evalCodeAt {Q : Type u} [CommRing Q] (φ : F →+* Q) :
    ℕ → List Q → ℕ → Q
  | 0, _xs, c => φ ((Encodable.decode (α := F) c).getD 0)
  | k + 1, xs, c =>
      ((Denumerable.ofNat (List ℕ) c).map
        (fun e => evalCodeAt φ k xs e)).foldr
          (fun a acc => a + xs.getD k 0 * acc) 0

def evalCode {Q : Type u} [CommRing Q] (φ : F →+* Q) (xs : List Q) (N : ℕ) : Q :=
  evalCodeAt (F := F) φ N.unpair.1 xs N.unpair.2

lemma encode_eq_zeroCode_iff (k : ℕ) (q : MvPolynomial (Fin k) F) :
    Encodable.encode q = zeroCode (F := F) k ↔ q = 0 := by
  constructor
  · intro h
    rw [zeroCode] at h
    exact Encodable.encode_injective h
  · intro h
    subst q
    rfl

lemma addCodeLists_map_encode (k : ℕ)
    (IH : ∀ q₁ q₂ : MvPolynomial (Fin k) F,
      addCodeAt (F := F) k (Encodable.encode q₁) (Encodable.encode q₂) =
        Encodable.encode (q₁ + q₂))
    (l₁ l₂ : List (MvPolynomial (Fin k) F)) :
    addCodeLists (zeroCode (F := F) k) (addCodeAt (F := F) k)
        (l₁.map Encodable.encode) (l₂.map Encodable.encode) =
      (addCoeffs l₁ l₂).map Encodable.encode := by
  apply List.ext_getElem
  · simp [addCodeLists, addCoeffs]
  · intro i hi₁ hi₂
    simp only [addCodeLists, addCoeffs, List.getElem_map, List.getElem_range]
    have hget₁ :
        (l₁.map Encodable.encode).getD i (zeroCode (F := F) k) =
          Encodable.encode (l₁.getD i 0) := by
      by_cases hi : i < l₁.length
      · rw [List.getD_eq_getElem _ _ (by simpa [List.length_map] using hi)]
        rw [List.getD_eq_getElem _ _ hi]
        simp
      · rw [List.getD_eq_default]
        · rw [List.getD_eq_default _ _ (le_of_not_gt hi)]
          rw [zeroCode]
        · simpa [List.length_map] using le_of_not_gt hi
    have hget₂ :
        (l₂.map Encodable.encode).getD i (zeroCode (F := F) k) =
          Encodable.encode (l₂.getD i 0) := by
      by_cases hi : i < l₂.length
      · rw [List.getD_eq_getElem _ _ (by simpa [List.length_map] using hi)]
        rw [List.getD_eq_getElem _ _ hi]
        simp
      · rw [List.getD_eq_default]
        · rw [List.getD_eq_default _ _ (le_of_not_gt hi)]
          rw [zeroCode]
        · simpa [List.length_map] using le_of_not_gt hi
    rw [hget₁, hget₂, IH]

lemma trimTrailing_map_encode_zeroCode (k : ℕ)
    (l : List (MvPolynomial (Fin k) F)) :
    trimTrailing (zeroCode (F := F) k) (l.map Encodable.encode) =
      (trimZeros (R := MvPolynomial (Fin k) F) l).map Encodable.encode := by
  induction l with
  | nil =>
      rfl
  | cons a t ih =>
      have hcode :
          Encodable.encode a = zeroCode (F := F) k ↔ a = 0 :=
        encode_eq_zeroCode_iff (F := F) k a
      change trimTrailingStep (zeroCode (F := F) k) (Encodable.encode a)
          (trimTrailing (zeroCode (F := F) k) (t.map Encodable.encode)) =
        (trimZeros (R := MvPolynomial (Fin k) F) (a :: t)).map Encodable.encode
      rw [ih]
      by_cases ht : trimZeros (R := MvPolynomial (Fin k) F) t = []
      · by_cases ha : a = 0
        · rw [ha]
          simp only [trimZeros, ht, List.map_nil, trimTrailingStep, ↓reduceIte]
          rw [if_pos
            ((encode_eq_zeroCode_iff (F := F) k (0 : MvPolynomial (Fin k) F)).mpr rfl)]
        · have hne : Encodable.encode a ≠ zeroCode (F := F) k :=
            mt hcode.mp ha
          simp [trimTrailingStep, trimZeros, ht, ha, hne]
      · have hmapne :
          (trimZeros (R := MvPolynomial (Fin k) F) t).map Encodable.encode ≠ [] := by
          intro hnil
          apply ht
          simpa using hnil
        simp [trimTrailingStep, trimZeros, ht, hmapne]

omit [Primcodable F] [ComputableRing F] in
lemma eval₂_coeff_after_map {Q : Type u} [CommRing Q] (φ : F →+* Q)
    (k : ℕ) (xs : List Q) (q : MvPolynomial (Fin k) F) :
    MvPolynomial.eval₂ φ (fun i : Fin k => xs.getD i 0) q =
      MvPolynomial.eval (fun i : Fin k => xs.getD i 0) (MvPolynomial.map φ q) := by
  rw [MvPolynomial.eval₂_eq_eval_map]

omit [Primcodable F] [ComputableRing F] in
lemma eval₂_fin_zero {Q : Type u} [CommRing Q] (φ : F →+* Q)
    (x : Fin 0 → Q) (q : MvPolynomial (Fin 0) F) :
    MvPolynomial.eval₂ φ x q =
      φ (MvPolynomial.eval (fun a : Fin 0 => isEmptyElim a) q) := by
  induction q using MvPolynomial.induction_on with
  | C a =>
      simp
  | add p r hp hr =>
      simp [hp, hr]
  | mul_X p i hp =>
      exact Fin.elim0 i

lemma evalCodeAt_succ_coeffs {Q : Type u} [CommRing Q] (φ : F →+* Q)
    (k : ℕ) (xs : List Q)
    (IH : ∀ q : MvPolynomial (Fin k) F,
      evalCodeAt (F := F) φ k xs (Encodable.encode q) =
        MvPolynomial.eval₂ φ (fun i : Fin k => xs.getD i 0) q)
    (l : List (MvPolynomial (Fin k) F)) :
    ((l.map Encodable.encode).map
        (fun e => evalCodeAt (F := F) φ k xs e)).foldr
          (fun a acc => a + xs.getD k 0 * acc) 0 =
      evalCoeffs (xs.getD k 0)
        (l.map (MvPolynomial.eval₂ φ (fun i : Fin k => xs.getD i 0))) := by
  induction l with
  | nil =>
      rfl
  | cons a t ih =>
      change evalCodeAt (F := F) φ k xs (Encodable.encode a) +
          xs.getD k 0 *
            ((t.map Encodable.encode).map
              (fun e => evalCodeAt (F := F) φ k xs e)).foldr
                (fun a acc => a + xs.getD k 0 * acc) 0 =
        MvPolynomial.eval₂ φ (fun i : Fin k => xs.getD i 0) a +
          xs.getD k 0 *
            evalCoeffs (xs.getD k 0)
              (t.map (MvPolynomial.eval₂ φ (fun i : Fin k => xs.getD i 0)))
      rw [IH a, ih]

omit [Primcodable F] [ComputableRing F] in
lemma level_add_le (p q : MvPolynomial ℕ F) :
    level (F := F) (p + q) ≤ max (level (F := F) p) (level (F := F) q) := by
  classical
  rw [level_le_iff]
  intro i hi
  have hvars := MvPolynomial.vars_add_subset p q hi
  rw [Finset.mem_union] at hvars
  rcases hvars with hp | hq
  · exact lt_of_lt_of_le (mem_vars_lt_level (F := F) hp) (le_max_left _ _)
  · exact lt_of_lt_of_le (mem_vars_lt_level (F := F) hq) (le_max_right _ _)

omit [Primcodable F] [ComputableRing F] in
lemma level_mul_le (p q : MvPolynomial ℕ F) :
    level (F := F) (p * q) ≤ max (level (F := F) p) (level (F := F) q) := by
  classical
  rw [level_le_iff]
  intro i hi
  have hvars := MvPolynomial.vars_mul p q hi
  rw [Finset.mem_union] at hvars
  rcases hvars with hp | hq
  · exact lt_of_lt_of_le (mem_vars_lt_level (F := F) hp) (le_max_left _ _)
  · exact lt_of_lt_of_le (mem_vars_lt_level (F := F) hq) (le_max_right _ _)

theorem addCodeAt_encode (k : ℕ) (q₁ q₂ : MvPolynomial (Fin k) F) :
    addCodeAt (F := F) k (Encodable.encode q₁) (Encodable.encode q₂) =
      Encodable.encode (q₁ + q₂) := by
  induction k with
  | zero =>
      unfold addCodeAt
      have hq₁ :
          Encodable.decode (α := F) (Encodable.encode q₁) =
            some ((MvPolynomial.isEmptyAlgEquiv F (Fin 0)) q₁) := by
        rw [encode_fin_zero_eq_encode_coeff (F := F) q₁, Encodable.encodek]
      have hq₂ :
          Encodable.decode (α := F) (Encodable.encode q₂) =
            some ((MvPolynomial.isEmptyAlgEquiv F (Fin 0)) q₂) := by
        rw [encode_fin_zero_eq_encode_coeff (F := F) q₂, Encodable.encodek]
      rw [hq₁, hq₂, encode_fin_zero_eq_encode_coeff (F := F) (q₁ + q₂)]
      simp
  | succ k IH =>
      let P₁ : Polynomial (MvPolynomial (Fin k) F) := towerEquiv F k q₁
      let P₂ : Polynomial (MvPolynomial (Fin k) F) := towerEquiv F k q₂
      have h₁ :
          Denumerable.ofNat (List ℕ) (Encodable.encode q₁) =
            ((polyCoeffs P₁).map Encodable.encode : List ℕ) := by
        dsimp [P₁]
        exact ofNat_encode_coeff_codes (F := F) k q₁
      have h₂ :
          Denumerable.ofNat (List ℕ) (Encodable.encode q₂) =
            ((polyCoeffs P₂).map Encodable.encode : List ℕ) := by
        dsimp [P₂]
        exact ofNat_encode_coeff_codes (F := F) k q₂
      have hlist :
          trimTrailing (zeroCode (F := F) k)
              (addCodeLists (zeroCode (F := F) k) (addCodeAt (F := F) k)
                (Denumerable.ofNat (List ℕ) (Encodable.encode q₁))
                (Denumerable.ofNat (List ℕ) (Encodable.encode q₂))) =
            ((polyCoeffs (P₁ + P₂)).map Encodable.encode : List ℕ) := by
        rw [h₁, h₂]
        rw [addCodeLists_map_encode (F := F) k IH (polyCoeffs P₁) (polyCoeffs P₂)]
        rw [trimTrailing_map_encode_zeroCode (F := F) k
          (addCoeffs (polyCoeffs P₁) (polyCoeffs P₂))]
        rw [_root_.Semicontinuity.polyCoeffs_add]
      unfold addCodeAt
      dsimp only
      rw [hlist]
      rw [encode_succ_eq_encode_coeff_codes (F := F) k (q₁ + q₂)]
      have hmap : towerEquiv F k (q₁ + q₂) = P₁ + P₂ := by
        dsimp [P₁, P₂]
        rw [map_add]
      rw [hmap]

lemma sumCodes_encode (k : ℕ) (qs : List (MvPolynomial (Fin k) F)) :
    sumCodes (zeroCode (F := F) k) (addCodeAt (F := F) k)
        (qs.map Encodable.encode) =
      Encodable.encode qs.sum := by
  induction qs with
  | nil =>
      simp [sumCodes, zeroCode]
  | cons q qs ih =>
      change addCodeAt (F := F) k (Encodable.encode q)
          (sumCodes (zeroCode (F := F) k) (addCodeAt (F := F) k)
            (qs.map Encodable.encode)) =
        Encodable.encode (q + qs.sum)
      rw [ih, addCodeAt_encode (F := F) k q qs.sum]

lemma map_encode_getD_zeroCode (k : ℕ)
    (l : List (MvPolynomial (Fin k) F)) (i : ℕ) :
    (l.map Encodable.encode).getD i (zeroCode (F := F) k) =
      Encodable.encode (l.getD i 0) := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ (by simpa [List.length_map] using hi)]
    rw [List.getD_eq_getElem _ _ hi]
    simp
  · rw [List.getD_eq_default]
    · rw [List.getD_eq_default _ _ (le_of_not_gt hi)]
      rw [zeroCode]
    · simpa [List.length_map] using le_of_not_gt hi

lemma mulCodeLists_map_encode (k : ℕ)
    (IH : ∀ q₁ q₂ : MvPolynomial (Fin k) F,
      mulCodeAt (F := F) k (Encodable.encode q₁) (Encodable.encode q₂) =
        Encodable.encode (q₁ * q₂))
    (l₁ l₂ : List (MvPolynomial (Fin k) F)) :
    mulCodeLists (zeroCode (F := F) k) (mulCodeAt (F := F) k)
        (addCodeAt (F := F) k)
        (l₁.map Encodable.encode) (l₂.map Encodable.encode) =
      (mulCoeffs l₁ l₂).map Encodable.encode := by
  apply List.ext_getElem
  · simp [mulCodeLists, mulCoeffs]
  · intro s hs₁ hs₂
    simp only [mulCodeLists, mulCoeffs, List.getElem_map, List.getElem_range]
    let qs : List (MvPolynomial (Fin k) F) :=
      (List.range (s + 1)).map fun i => l₁.getD i 0 * l₂.getD (s - i) 0
    have hproducts :
        ((List.range (s + 1)).map fun i =>
            mulCodeAt (F := F) k
              ((l₁.map Encodable.encode).getD i (zeroCode (F := F) k))
              ((l₂.map Encodable.encode).getD (s - i) (zeroCode (F := F) k))) =
          qs.map Encodable.encode := by
      dsimp [qs]
      rw [List.map_map]
      apply List.map_congr_left
      intro i _hi
      rw [map_encode_getD_zeroCode (F := F) k l₁ i]
      rw [map_encode_getD_zeroCode (F := F) k l₂ (s - i)]
      rw [IH]
      rfl
    rw [hproducts]
    exact sumCodes_encode (F := F) k qs

theorem mulCodeAt_encode (k : ℕ) (q₁ q₂ : MvPolynomial (Fin k) F) :
    mulCodeAt (F := F) k (Encodable.encode q₁) (Encodable.encode q₂) =
      Encodable.encode (q₁ * q₂) := by
  induction k with
  | zero =>
      unfold mulCodeAt
      have hq₁ :
          Encodable.decode (α := F) (Encodable.encode q₁) =
            some ((MvPolynomial.isEmptyAlgEquiv F (Fin 0)) q₁) := by
        rw [encode_fin_zero_eq_encode_coeff (F := F) q₁, Encodable.encodek]
      have hq₂ :
          Encodable.decode (α := F) (Encodable.encode q₂) =
            some ((MvPolynomial.isEmptyAlgEquiv F (Fin 0)) q₂) := by
        rw [encode_fin_zero_eq_encode_coeff (F := F) q₂, Encodable.encodek]
      rw [hq₁, hq₂, encode_fin_zero_eq_encode_coeff (F := F) (q₁ * q₂)]
      simp
  | succ k IH =>
      let P₁ : Polynomial (MvPolynomial (Fin k) F) := towerEquiv F k q₁
      let P₂ : Polynomial (MvPolynomial (Fin k) F) := towerEquiv F k q₂
      have h₁ :
          Denumerable.ofNat (List ℕ) (Encodable.encode q₁) =
            ((polyCoeffs P₁).map Encodable.encode : List ℕ) := by
        dsimp [P₁]
        exact ofNat_encode_coeff_codes (F := F) k q₁
      have h₂ :
          Denumerable.ofNat (List ℕ) (Encodable.encode q₂) =
            ((polyCoeffs P₂).map Encodable.encode : List ℕ) := by
        dsimp [P₂]
        exact ofNat_encode_coeff_codes (F := F) k q₂
      have hlist :
          trimTrailing (zeroCode (F := F) k)
              (mulCodeLists (zeroCode (F := F) k) (mulCodeAt (F := F) k)
                (addCodeAt (F := F) k)
                (Denumerable.ofNat (List ℕ) (Encodable.encode q₁))
                (Denumerable.ofNat (List ℕ) (Encodable.encode q₂))) =
            ((polyCoeffs (P₁ * P₂)).map Encodable.encode : List ℕ) := by
        rw [h₁, h₂]
        rw [mulCodeLists_map_encode (F := F) k IH (polyCoeffs P₁) (polyCoeffs P₂)]
        rw [trimTrailing_map_encode_zeroCode (F := F) k
          (mulCoeffs (polyCoeffs P₁) (polyCoeffs P₂))]
        rw [_root_.Semicontinuity.polyCoeffs_mul]
      unfold mulCodeAt
      dsimp only
      rw [hlist]
      rw [encode_succ_eq_encode_coeff_codes (F := F) k (q₁ * q₂)]
      have hmap : towerEquiv F k (q₁ * q₂) = P₁ * P₂ := by
        dsimp [P₁, P₂]
        rw [map_mul]
      rw [hmap]

lemma Nat.pair_le_pair_left' {a₁ a₂ b : ℕ} (h : a₁ ≤ a₂) :
    Nat.pair a₁ b ≤ Nat.pair a₂ b := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · rfl
  · exact le_of_lt (Nat.pair_lt_pair_left b hlt)

lemma Nat.pair_le_pair_right' {a b₁ b₂ : ℕ} (h : b₁ ≤ b₂) :
    Nat.pair a b₁ ≤ Nat.pair a b₂ := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · rfl
  · exact le_of_lt (Nat.pair_lt_pair_right a hlt)

lemma list_getD_lt_encode_of_lt {l : List ℕ} {i : ℕ} (hi : i < l.length) :
    l.getD i 0 < Encodable.encode l := by
  have hmem : l.getD i 0 ∈ l := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  exact List.encode_mem_lt_encode (α := ℕ) hmem

lemma list_getD_le_encode (l : List ℕ) (i : ℕ) :
    l.getD i 0 ≤ Encodable.encode l := by
  by_cases hi : i < l.length
  · exact le_of_lt (list_getD_lt_encode_of_lt (l := l) hi)
  · rw [List.getD_eq_default _ _ (le_of_not_gt hi)]
    exact Nat.zero_le _

lemma pair_inner_lt_of_getD {l₁ l₂ : List ℕ} {i : ℕ}
    (hi : i < max l₁.length l₂.length) :
    Nat.pair (l₁.getD i 0) (l₂.getD i 0) <
      Nat.pair (Encodable.encode l₁) (Encodable.encode l₂) := by
  have hcase : i < l₁.length ∨ i < l₂.length := by
    omega
  rcases hcase with hi₁ | hi₂
  · exact lt_of_lt_of_le
      (Nat.pair_lt_pair_left (l₂.getD i 0)
        (list_getD_lt_encode_of_lt (l := l₁) hi₁))
      (Nat.pair_le_pair_right' (list_getD_le_encode l₂ i))
  · exact lt_of_le_of_lt
      (Nat.pair_le_pair_left' (list_getD_le_encode l₁ i))
      (Nat.pair_lt_pair_right (Encodable.encode l₁)
        (list_getD_lt_encode_of_lt (l := l₂) hi₂))

lemma pair_getD_lt {k c₁ c₂ : ℕ} {i : ℕ}
    (hi : i < max (Denumerable.ofNat (List ℕ) c₁).length
        (Denumerable.ofNat (List ℕ) c₂).length) :
    Nat.pair k
        (Nat.pair ((Denumerable.ofNat (List ℕ) c₁).getD i 0)
          ((Denumerable.ofNat (List ℕ) c₂).getD i 0)) <
      Nat.pair (k + 1) (Nat.pair c₁ c₂) := by
  let l₁ := Denumerable.ofNat (List ℕ) c₁
  let l₂ := Denumerable.ofNat (List ℕ) c₂
  have hinner :
      Nat.pair (l₁.getD i 0) (l₂.getD i 0) < Nat.pair c₁ c₂ := by
    simpa [l₁, l₂, Denumerable.encode_ofNat (α := List ℕ)] using
      (pair_inner_lt_of_getD (l₁ := l₁) (l₂ := l₂) (i := i) (by simpa [l₁, l₂] using hi))
  exact (Nat.pair_lt_pair_left (Nat.pair (l₁.getD i 0) (l₂.getD i 0))
      (Nat.lt_succ_self k)).trans
    (Nat.pair_lt_pair_right (k + 1) hinner)

lemma pair_inner_lt_of_getD_mul {l₁ l₂ : List ℕ} {s i : ℕ}
    (hs : s < l₁.length + l₂.length) (hi : i ∈ List.range (s + 1)) :
    Nat.pair (l₁.getD i 0) (l₂.getD (s - i) 0) <
      Nat.pair (Encodable.encode l₁) (Encodable.encode l₂) := by
  have hi_le : i ≤ s := by
    exact Nat.le_of_lt_succ (List.mem_range.mp hi)
  have hcase : i < l₁.length ∨ s - i < l₂.length := by
    by_contra hnot
    push_neg at hnot
    omega
  rcases hcase with hi₁ | hi₂
  · exact lt_of_lt_of_le
      (Nat.pair_lt_pair_left (l₂.getD (s - i) 0)
        (list_getD_lt_encode_of_lt (l := l₁) hi₁))
      (Nat.pair_le_pair_right' (list_getD_le_encode l₂ (s - i)))
  · exact lt_of_le_of_lt
      (Nat.pair_le_pair_left' (list_getD_le_encode l₁ i))
      (Nat.pair_lt_pair_right (Encodable.encode l₁)
        (list_getD_lt_encode_of_lt (l := l₂) hi₂))

lemma pair_getD_mul_lt {k c₁ c₂ : ℕ} {s i : ℕ}
    (hs : s < (Denumerable.ofNat (List ℕ) c₁).length +
        (Denumerable.ofNat (List ℕ) c₂).length)
    (hi : i ∈ List.range (s + 1)) :
    Nat.pair k
        (Nat.pair ((Denumerable.ofNat (List ℕ) c₁).getD i 0)
          ((Denumerable.ofNat (List ℕ) c₂).getD (s - i) 0)) <
      Nat.pair (k + 1) (Nat.pair c₁ c₂) := by
  let l₁ := Denumerable.ofNat (List ℕ) c₁
  let l₂ := Denumerable.ofNat (List ℕ) c₂
  have hinner :
      Nat.pair (l₁.getD i 0) (l₂.getD (s - i) 0) < Nat.pair c₁ c₂ := by
    simpa [l₁, l₂, Denumerable.encode_ofNat (α := List ℕ)] using
      (pair_inner_lt_of_getD_mul (l₁ := l₁) (l₂ := l₂) (s := s) (i := i)
        (by simpa [l₁, l₂] using hs) hi)
  exact (Nat.pair_lt_pair_left (Nat.pair (l₁.getD i 0) (l₂.getD (s - i) 0))
      (Nat.lt_succ_self k)).trans
    (Nat.pair_lt_pair_right (k + 1) hinner)

private def addCodeBase (c₁ c₂ : ℕ) : ℕ :=
  Encodable.encode
    (((Encodable.decode (α := F) c₁).getD 0) +
      ((Encodable.decode (α := F) c₂).getD 0))

private def mulCodeBase (c₁ c₂ : ℕ) : ℕ :=
  Encodable.encode
    (((Encodable.decode (α := F) c₁).getD 0) *
      ((Encodable.decode (α := F) c₂).getD 0))

private def addCodeStep (table : List ℕ) : ℕ :=
  let N := table.length
  let lvl := N.unpair.1
  let c₁ := N.unpair.2.unpair.1
  let c₂ := N.unpair.2.unpair.2
  if lvl = 0 then
    addCodeBase (F := F) c₁ c₂
  else if lvl = 1 then
    let l₁ := Denumerable.ofNat (List ℕ) c₁
    let l₂ := Denumerable.ofNat (List ℕ) c₂
    Encodable.encode
      (trimTrailing (zeroCode (F := F) 0)
        (addCodeLists (zeroCode (F := F) 0) (addCodeBase (F := F)) l₁ l₂))
  else
    let k := lvl - 2
    let l₁ := Denumerable.ofNat (List ℕ) c₁
    let l₂ := Denumerable.ofNat (List ℕ) c₂
    Encodable.encode
      (trimTrailing 0
        (addCodeLists 0
          (fun a b => table.getD (Nat.pair (k + 1) (Nat.pair a b)) 0) l₁ l₂))

private def mulCodeStep (table : List ℕ) : ℕ :=
  let N := table.length
  let lvl := N.unpair.1
  let c₁ := N.unpair.2.unpair.1
  let c₂ := N.unpair.2.unpair.2
  if lvl = 0 then
    mulCodeBase (F := F) c₁ c₂
  else if lvl = 1 then
    let l₁ := Denumerable.ofNat (List ℕ) c₁
    let l₂ := Denumerable.ofNat (List ℕ) c₂
    Encodable.encode
      (trimTrailing (zeroCode (F := F) 0)
        (mulCodeLists (zeroCode (F := F) 0) (mulCodeBase (F := F))
          (addCodeAt (F := F) 0) l₁ l₂))
  else
    let k := lvl - 2
    let l₁ := Denumerable.ofNat (List ℕ) c₁
    let l₂ := Denumerable.ofNat (List ℕ) c₂
    Encodable.encode
      (trimTrailing 0
        (mulCodeLists 0
          (fun a b => table.getD (Nat.pair (k + 1) (Nat.pair a b)) 0)
          (addCodeAt (F := F) (k + 1)) l₁ l₂))

private theorem computable_addCodeBase :
    Computable₂ (addCodeBase (F := F)) := by
  have h₁ : Computable fun x : ℕ × ℕ => (Encodable.decode (α := F) x.1).getD 0 :=
    Computable.option_getD (Computable.decode.comp Computable.fst) (Computable.const 0)
  have h₂ : Computable fun x : ℕ × ℕ => (Encodable.decode (α := F) x.2).getD 0 :=
    Computable.option_getD (Computable.decode.comp Computable.snd) (Computable.const 0)
  exact (Computable.encode.comp (ComputableRing.computable_add.comp h₁ h₂)).to₂

private theorem computable_mulCodeBase :
    Computable₂ (mulCodeBase (F := F)) := by
  have h₁ : Computable fun x : ℕ × ℕ => (Encodable.decode (α := F) x.1).getD 0 :=
    Computable.option_getD (Computable.decode.comp Computable.fst) (Computable.const 0)
  have h₂ : Computable fun x : ℕ × ℕ => (Encodable.decode (α := F) x.2).getD 0 :=
    Computable.option_getD (Computable.decode.comp Computable.snd) (Computable.const 0)
  exact (Computable.encode.comp (ComputableRing.computable_mul.comp h₁ h₂)).to₂

private theorem primrec_trimTrailingStep :
    Primrec fun x : ℕ × ℕ × List ℕ =>
      trimTrailingStep x.1 x.2.1 x.2.2 := by
  have hrnil : PrimrecPred fun x : ℕ × ℕ × List ℕ => x.2.2 = [] :=
    (@Primrec.eq (List ℕ) _).comp (Primrec.snd.comp Primrec.snd) (Primrec.const [])
  have haz : PrimrecPred fun x : ℕ × ℕ × List ℕ => x.2.1 = x.1 :=
    (@Primrec.eq ℕ _).comp (Primrec.fst.comp Primrec.snd) Primrec.fst
  have hsingleton : Primrec fun x : ℕ × ℕ × List ℕ => [x.2.1] :=
    Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.const [])
  have hcons : Primrec fun x : ℕ × ℕ × List ℕ => x.2.1 :: x.2.2 :=
    Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact (Primrec.ite hrnil
    (Primrec.ite haz (Primrec.const []) hsingleton) hcons).of_eq fun x => by
      rcases x with ⟨z, a, r⟩
      simp [trimTrailingStep]

private theorem computable_trimTrailing :
    Computable fun x : ℕ × List ℕ => trimTrailing x.1 x.2 := by
  have hstep : Primrec₂ fun (x : ℕ × List ℕ) (p : ℕ × List ℕ) =>
      trimTrailingStep x.1 p.1 p.2 := by
    exact primrec_trimTrailingStep.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))
  exact (Primrec.list_foldr (f := fun x : ℕ × List ℕ => x.2)
    (g := fun _ : ℕ × List ℕ => ([] : List ℕ))
    (h := fun x p => trimTrailingStep x.1 p.1 p.2)
    Primrec.snd (Primrec.const []) hstep).to_comp

private theorem computable_addCodeStep :
    Computable (addCodeStep (F := F)) := by
  let len : List ℕ → ℕ := fun t => t.length
  let lvlOf : List ℕ → ℕ := fun t => t.length.unpair.1
  let c₁Of : List ℕ → ℕ := fun t => t.length.unpair.2.unpair.1
  let c₂Of : List ℕ → ℕ := fun t => t.length.unpair.2.unpair.2
  have hlen : Computable len := Computable.list_length
  have hlvl : Computable lvlOf :=
    ((Primrec.fst.comp Primrec.unpair).to_comp).comp hlen
  have hpairCode : Computable fun t : List ℕ => t.length.unpair.2 :=
    ((Primrec.snd.comp Primrec.unpair).to_comp).comp hlen
  have hc₁ : Computable c₁Of :=
    ((Primrec.fst.comp Primrec.unpair).to_comp).comp hpairCode
  have hc₂ : Computable c₂Of :=
    ((Primrec.snd.comp Primrec.unpair).to_comp).comp hpairCode
  have hl₁ : Computable fun t : List ℕ => Denumerable.ofNat (List ℕ) (c₁Of t) :=
    (Primrec.ofNat (List ℕ)).to_comp.comp hc₁
  have hl₂ : Computable fun t : List ℕ => Denumerable.ofNat (List ℕ) (c₂Of t) :=
    (Primrec.ofNat (List ℕ)).to_comp.comp hc₂
  have hmaxLen : Computable fun t : List ℕ =>
      max (Denumerable.ofNat (List ℕ) (c₁Of t)).length
        (Denumerable.ofNat (List ℕ) (c₂Of t)).length :=
    Primrec.nat_max.to_comp.comp
      (Computable.list_length.comp hl₁) (Computable.list_length.comp hl₂)
  have hbaseBranch : Computable fun t : List ℕ => addCodeBase (F := F) (c₁Of t) (c₂Of t) :=
    computable_addCodeBase (F := F).comp hc₁ hc₂
  have hget₁_z (z : ℕ) : Computable fun x : List ℕ × ℕ =>
      (Denumerable.ofNat (List ℕ) (c₁Of x.1)).getD x.2 z :=
    (Primrec.list_getD z).to_comp.comp (hl₁.comp Computable.fst) Computable.snd
  have hget₂_z (z : ℕ) : Computable fun x : List ℕ × ℕ =>
      (Denumerable.ofNat (List ℕ) (c₂Of x.1)).getD x.2 z :=
    (Primrec.list_getD z).to_comp.comp (hl₂.comp Computable.fst) Computable.snd
  have hlistInline : Computable fun t : List ℕ =>
      addCodeLists (zeroCode (F := F) 0) (addCodeBase (F := F))
        (Denumerable.ofNat (List ℕ) (c₁Of t))
        (Denumerable.ofNat (List ℕ) (c₂Of t)) := by
    have hterm : Computable₂ fun t i =>
        addCodeBase (F := F)
          ((Denumerable.ofNat (List ℕ) (c₁Of t)).getD i (zeroCode (F := F) 0))
          ((Denumerable.ofNat (List ℕ) (c₂Of t)).getD i (zeroCode (F := F) 0)) :=
      (computable_addCodeBase (F := F)).comp (hget₁_z (zeroCode (F := F) 0))
        (hget₂_z (zeroCode (F := F) 0))
    exact (Computable.list_map (Primrec.list_range.to_comp.comp hmaxLen) hterm).of_eq fun t => rfl
  have hinlineBranch : Computable fun t : List ℕ =>
      Encodable.encode
        (trimTrailing (zeroCode (F := F) 0)
          (addCodeLists (zeroCode (F := F) 0) (addCodeBase (F := F))
            (Denumerable.ofNat (List ℕ) (c₁Of t))
            (Denumerable.ofNat (List ℕ) (c₂Of t)))) :=
    Computable.encode.comp
      (computable_trimTrailing.comp
        (Computable.pair (Computable.const (zeroCode (F := F) 0)) hlistInline))
  have hk : Computable fun t : List ℕ => lvlOf t - 2 :=
    Primrec.nat_sub.to_comp.comp hlvl (Computable.const 2)
  have hlistTable : Computable fun t : List ℕ =>
      addCodeLists 0
        (fun a b => (t : List ℕ).getD (Nat.pair ((lvlOf t - 2) + 1) (Nat.pair a b)) 0)
        (Denumerable.ofNat (List ℕ) (c₁Of t))
        (Denumerable.ofNat (List ℕ) (c₂Of t)) := by
    have hidx : Computable fun x : List ℕ × ℕ =>
        Nat.pair ((lvlOf x.1 - 2) + 1)
          (Nat.pair
            ((Denumerable.ofNat (List ℕ) (c₁Of x.1)).getD x.2 0)
            ((Denumerable.ofNat (List ℕ) (c₂Of x.1)).getD x.2 0)) :=
      Primrec₂.natPair.to_comp.comp
        (Primrec.succ.to_comp.comp (hk.comp Computable.fst))
        (Primrec₂.natPair.to_comp.comp (hget₁_z 0) (hget₂_z 0))
    have hterm : Computable₂ fun t i =>
        (t : List ℕ).getD (Nat.pair ((lvlOf t - 2) + 1)
          (Nat.pair
            ((Denumerable.ofNat (List ℕ) (c₁Of t)).getD i 0)
            ((Denumerable.ofNat (List ℕ) (c₂Of t)).getD i 0))) 0 :=
      (((Primrec.list_getD 0).to_comp.comp Computable.fst hidx).to₂).of_eq fun _ => rfl
    exact (Computable.list_map (Primrec.list_range.to_comp.comp hmaxLen) hterm).of_eq fun t => rfl
  have htableBranch : Computable fun t : List ℕ =>
      Encodable.encode
        (trimTrailing 0
          (addCodeLists 0
            (fun a b => (t : List ℕ).getD (Nat.pair ((lvlOf t - 2) + 1) (Nat.pair a b)) 0)
            (Denumerable.ofNat (List ℕ) (c₁Of t))
            (Denumerable.ofNat (List ℕ) (c₂Of t)))) :=
    Computable.encode.comp
      (computable_trimTrailing.comp
        (Computable.pair (Computable.const 0) hlistTable))
  have hzero : Computable fun t : List ℕ => decide (lvlOf t = 0) :=
    (@Primrec.eq ℕ _).decide.to_comp.comp hlvl (Computable.const 0)
  have hone : Computable fun t : List ℕ => decide (lvlOf t = 1) :=
    (@Primrec.eq ℕ _).decide.to_comp.comp hlvl (Computable.const 1)
  exact (Computable.cond hzero hbaseBranch
    (Computable.cond hone hinlineBranch htableBranch)).of_eq fun t => by
      by_cases h0 : lvlOf t = 0
      · simp [addCodeStep, lvlOf, c₁Of, c₂Of, h0]
      · by_cases h1 : lvlOf t = 1
        · simp [addCodeStep, lvlOf, c₁Of, c₂Of, h1]
        · simp [addCodeStep, lvlOf, c₁Of, c₂Of, h0, h1, List.getD_eq_getElem?_getD]

set_option maxHeartbeats 5000000 in
-- The strong-recursion table proof builds a large computable step term.
set_option linter.flexible false in
theorem computable_addCode :
    Computable (addCode (F := F)) := by
  let f : ℕ → ℕ := fun N =>
    addCodeAt (F := F) N.unpair.1 N.unpair.2.unpair.1 N.unpair.2.unpair.2
  have H : ∀ N, addCodeStep (F := F) ((List.range N).map f) = f N := by
    intro N
    dsimp [f]
    unfold addCodeStep
    rw [List.length_map, List.length_range]
    rcases hn0 : N.unpair.1 with _ | lvl
    · simp [hn0, addCodeBase, addCodeAt]
    · cases lvl with
      | zero =>
          unfold addCodeBase
          simp [hn0, addCodeAt]
      | succ k =>
          let c₁ := N.unpair.2.unpair.1
          let c₂ := N.unpair.2.unpair.2
          let l₁ := Denumerable.ofNat (List ℕ) c₁
          let l₂ := Denumerable.ofNat (List ℕ) c₂
          have hpair : Nat.pair (k + 2) (Nat.pair c₁ c₂) = N := by
            dsimp [c₁, c₂]
            simpa [hn0] using (Nat.pair_unpair N)
          have hmap :
              addCodeLists 0
                (fun a b =>
                  (Option.map (fun i : ℕ =>
                    addCodeAt (F := F) i.unpair.1 i.unpair.2.unpair.1
                      i.unpair.2.unpair.2)
                    (List.range N)[Nat.pair (k + 1) (Nat.pair a b)]?).getD 0)
                l₁ l₂ =
              addCodeLists (zeroCode (F := F) (k + 1))
                (addCodeAt (F := F) (k + 1)) l₁ l₂ := by
            apply List.map_congr_left
            intro i hi
            have hi' : i < max l₁.length l₂.length := by
              simpa [addCodeLists] using List.mem_range.mp hi
            have hlt :
                Nat.pair (k + 1) (Nat.pair (l₁.getD i 0) (l₂.getD i 0)) < N := by
              exact lt_of_lt_of_eq
                (pair_getD_lt (k := k + 1) (c₁ := c₁) (c₂ := c₂) (i := i)
                  (by simpa [l₁, l₂] using hi')) hpair
            have hlookup :
                ((List.range N).map f).getD
                  (Nat.pair (k + 1) (Nat.pair (l₁.getD i 0) (l₂.getD i 0))) 0 =
                f (Nat.pair (k + 1) (Nat.pair (l₁.getD i 0) (l₂.getD i 0))) :=
              table_getD (d := 0) hlt
            simpa [List.getD_eq_getElem?_getD, f, Nat.unpair_pair, zeroCode_succ]
              using hlookup
          have hnot0 : ¬ k + 1 + 1 = 0 := by omega
          have hnot1 : ¬ k + 1 + 1 = 1 := by omega
          simp [hn0, addCodeAt, List.getD_eq_getElem?_getD]
          change trimTrailing 0
              (addCodeLists 0
                (fun a b =>
                  (Option.map (fun i : ℕ =>
                    addCodeAt (F := F) i.unpair.1 i.unpair.2.unpair.1
                      i.unpair.2.unpair.2)
                    (List.range N)[Nat.pair (k + 1) (Nat.pair a b)]?).getD 0)
                l₁ l₂) =
            trimTrailing 0
              (addCodeLists 0 (addCodeAt (F := F) (k + 1)) l₁ l₂)
          rw [hmap]
          simp [zeroCode_succ]
  have hg : Computable₂ (fun (_ : Unit) (table : List ℕ) =>
      some (addCodeStep (F := F) table)) := by
    exact (Computable.option_some.comp
      (computable_addCodeStep (F := F).comp Computable.snd)).to₂
  exact (Computable.nat_strong_rec
    (fun (_ : Unit) N => f N)
    hg (fun _ n => by simpa using H n)).comp (Computable.const ()) Computable.id

private theorem computable_mulCodeStep :
    Computable (mulCodeStep (F := F)) := by
  let len : List ℕ → ℕ := fun t => t.length
  let lvlOf : List ℕ → ℕ := fun t => t.length.unpair.1
  let c₁Of : List ℕ → ℕ := fun t => t.length.unpair.2.unpair.1
  let c₂Of : List ℕ → ℕ := fun t => t.length.unpair.2.unpair.2
  have hlen : Computable len := Computable.list_length
  have hlvl : Computable lvlOf :=
    ((Primrec.fst.comp Primrec.unpair).to_comp).comp hlen
  have hpairCode : Computable fun t : List ℕ => t.length.unpair.2 :=
    ((Primrec.snd.comp Primrec.unpair).to_comp).comp hlen
  have hc₁ : Computable c₁Of :=
    ((Primrec.fst.comp Primrec.unpair).to_comp).comp hpairCode
  have hc₂ : Computable c₂Of :=
    ((Primrec.snd.comp Primrec.unpair).to_comp).comp hpairCode
  have hl₁ : Computable fun t : List ℕ => Denumerable.ofNat (List ℕ) (c₁Of t) :=
    (Primrec.ofNat (List ℕ)).to_comp.comp hc₁
  have hl₂ : Computable fun t : List ℕ => Denumerable.ofNat (List ℕ) (c₂Of t) :=
    (Primrec.ofNat (List ℕ)).to_comp.comp hc₂
  have hconvLen : Computable fun t : List ℕ =>
      (Denumerable.ofNat (List ℕ) (c₁Of t)).length +
        (Denumerable.ofNat (List ℕ) (c₂Of t)).length :=
    Primrec.nat_add.to_comp.comp
      (Computable.list_length.comp hl₁) (Computable.list_length.comp hl₂)
  have hbaseBranch : Computable fun t : List ℕ => mulCodeBase (F := F) (c₁Of t) (c₂Of t) :=
    computable_mulCodeBase (F := F).comp hc₁ hc₂
  have hget₁_z (z : ℕ) : Computable fun x : List ℕ × ℕ =>
      (Denumerable.ofNat (List ℕ) (c₁Of x.1)).getD x.2 z :=
    (Primrec.list_getD z).to_comp.comp (hl₁.comp Computable.fst) Computable.snd
  have hget₂_z (z : ℕ) : Computable fun x : List ℕ × ℕ =>
      (Denumerable.ofNat (List ℕ) (c₂Of x.1)).getD x.2 z :=
    (Primrec.list_getD z).to_comp.comp (hl₂.comp Computable.fst) Computable.snd
  have haddAt0 : Computable₂ fun a b => addCodeAt (F := F) 0 a b := by
    have hraw : Computable fun p : ℕ × ℕ =>
        addCode (F := F) (Nat.pair 0 (Nat.pair p.1 p.2)) :=
      (computable_addCode (F := F)).comp
        (Primrec₂.natPair.to_comp.comp (Computable.const 0)
          (Primrec₂.natPair.to_comp.comp Computable.fst Computable.snd))
    exact hraw.to₂.of_eq fun p => by
      simp [addCode, Nat.unpair_pair]
  have hlistInline : Computable fun t : List ℕ =>
      mulCodeLists (zeroCode (F := F) 0) (mulCodeBase (F := F)) (addCodeAt (F := F) 0)
        (Denumerable.ofNat (List ℕ) (c₁Of t))
        (Denumerable.ofNat (List ℕ) (c₂Of t)) := by
    have hterm : Computable₂ fun t s =>
        sumCodes (zeroCode (F := F) 0) (addCodeAt (F := F) 0)
          ((List.range (s + 1)).map fun i =>
            mulCodeBase (F := F)
              ((Denumerable.ofNat (List ℕ) (c₁Of t)).getD i (zeroCode (F := F) 0))
              ((Denumerable.ofNat (List ℕ) (c₂Of t)).getD (s - i)
                (zeroCode (F := F) 0))) := by
      have hinner : Computable fun y : List ℕ × ℕ =>
          sumCodes (zeroCode (F := F) 0) (addCodeAt (F := F) 0)
            ((List.range (y.2 + 1)).map fun i =>
              mulCodeBase (F := F)
                ((Denumerable.ofNat (List ℕ) (c₁Of y.1)).getD i
                  (zeroCode (F := F) 0))
                ((Denumerable.ofNat (List ℕ) (c₂Of y.1)).getD (y.2 - i)
                  (zeroCode (F := F) 0))) := by
        have hN : Computable fun y : List ℕ × ℕ => y.2 + 1 :=
          Primrec.nat_add.to_comp.comp Computable.snd (Computable.const 1)
        have hprod : Computable₂ fun (y : List ℕ × ℕ) i =>
            mulCodeBase (F := F)
              ((Denumerable.ofNat (List ℕ) (c₁Of y.1)).getD i (zeroCode (F := F) 0))
              ((Denumerable.ofNat (List ℕ) (c₂Of y.1)).getD (y.2 - i)
                (zeroCode (F := F) 0)) := by
          have hleft : Computable fun z : (List ℕ × ℕ) × ℕ =>
              (Denumerable.ofNat (List ℕ) (c₁Of z.1.1)).getD z.2
                (zeroCode (F := F) 0) :=
            (hget₁_z (zeroCode (F := F) 0)).comp
              (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
          have hidx : Computable fun z : (List ℕ × ℕ) × ℕ => z.1.2 - z.2 :=
            Primrec.nat_sub.to_comp.comp (Computable.snd.comp Computable.fst)
              Computable.snd
          have hright : Computable fun z : (List ℕ × ℕ) × ℕ =>
              (Denumerable.ofNat (List ℕ) (c₂Of z.1.1)).getD (z.1.2 - z.2)
                (zeroCode (F := F) 0) :=
            (hget₂_z (zeroCode (F := F) 0)).comp
              (Computable.pair (Computable.fst.comp Computable.fst) hidx)
          exact (computable_mulCodeBase (F := F)).comp hleft hright
        have hproducts : Computable fun y : List ℕ × ℕ =>
            (List.range (y.2 + 1)).map fun i =>
              mulCodeBase (F := F)
                ((Denumerable.ofNat (List ℕ) (c₁Of y.1)).getD i
                  (zeroCode (F := F) 0))
                ((Denumerable.ofNat (List ℕ) (c₂Of y.1)).getD (y.2 - i)
                  (zeroCode (F := F) 0)) :=
          Computable.list_map (Primrec.list_range.to_comp.comp hN) hprod
        have hrev : Computable fun y : List ℕ × ℕ =>
            (((List.range (y.2 + 1)).map fun i =>
              mulCodeBase (F := F)
                ((Denumerable.ofNat (List ℕ) (c₁Of y.1)).getD i
                  (zeroCode (F := F) 0))
                ((Denumerable.ofNat (List ℕ) (c₂Of y.1)).getD (y.2 - i)
                  (zeroCode (F := F) 0))).reverse) :=
          Computable.list_reverse.comp hproducts
        have hfoldStep : Computable₂ fun (_ : List ℕ × ℕ) (p : ℕ × ℕ) =>
            addCodeAt (F := F) 0 p.2 p.1 := by
          exact (haddAt0.comp (Computable.snd.comp Computable.snd)
            (Computable.fst.comp Computable.snd)).to₂
        have hfold := Computable.list_foldl hrev
          (Computable.const (zeroCode (F := F) 0)) hfoldStep
        exact hfold.of_eq fun y => by
          simp [sumCodes, List.foldl_reverse]
      exact hinner.to₂
    exact (Computable.list_map (Primrec.list_range.to_comp.comp hconvLen) hterm).of_eq fun t => rfl
  have hinlineBranch : Computable fun t : List ℕ =>
      Encodable.encode
        (trimTrailing (zeroCode (F := F) 0)
          (mulCodeLists (zeroCode (F := F) 0) (mulCodeBase (F := F)) (addCodeAt (F := F) 0)
            (Denumerable.ofNat (List ℕ) (c₁Of t))
            (Denumerable.ofNat (List ℕ) (c₂Of t)))) :=
    Computable.encode.comp
      (computable_trimTrailing.comp
        (Computable.pair (Computable.const (zeroCode (F := F) 0)) hlistInline))
  have hk : Computable fun t : List ℕ => lvlOf t - 2 :=
    Primrec.nat_sub.to_comp.comp hlvl (Computable.const 2)
  have haddAtTable : Computable₂ fun t (p : ℕ × ℕ) =>
      addCodeAt (F := F) ((lvlOf t - 2) + 1) p.1 p.2 := by
    have hlvl' : Computable fun x : List ℕ × (ℕ × ℕ) => (lvlOf x.1 - 2) + 1 :=
      Primrec.nat_add.to_comp.comp (hk.comp Computable.fst) (Computable.const 1)
    have hraw : Computable fun x : List ℕ × (ℕ × ℕ) =>
        addCode (F := F)
          (Nat.pair ((lvlOf x.1 - 2) + 1) (Nat.pair x.2.1 x.2.2)) :=
      (computable_addCode (F := F)).comp
        (Primrec₂.natPair.to_comp.comp hlvl'
          (Primrec₂.natPair.to_comp.comp
            (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)))
    exact hraw.to₂.of_eq fun x => by
      simp [addCode, Nat.unpair_pair]
  have hlistTable : Computable fun t : List ℕ =>
      mulCodeLists 0
        (fun a b => (t : List ℕ).getD (Nat.pair ((lvlOf t - 2) + 1) (Nat.pair a b)) 0)
        (addCodeAt (F := F) ((lvlOf t - 2) + 1))
        (Denumerable.ofNat (List ℕ) (c₁Of t))
        (Denumerable.ofNat (List ℕ) (c₂Of t)) := by
    have hterm : Computable₂ fun t s =>
        sumCodes 0 (addCodeAt (F := F) ((lvlOf t - 2) + 1))
          ((List.range (s + 1)).map fun i =>
            (t : List ℕ).getD
              (Nat.pair ((lvlOf t - 2) + 1)
                (Nat.pair
                  ((Denumerable.ofNat (List ℕ) (c₁Of t)).getD i 0)
                  ((Denumerable.ofNat (List ℕ) (c₂Of t)).getD (s - i) 0))) 0) := by
      have hinner : Computable fun y : List ℕ × ℕ =>
          sumCodes 0 (addCodeAt (F := F) ((lvlOf y.1 - 2) + 1))
            ((List.range (y.2 + 1)).map fun i =>
              (y.1 : List ℕ).getD
                (Nat.pair ((lvlOf y.1 - 2) + 1)
                  (Nat.pair
                    ((Denumerable.ofNat (List ℕ) (c₁Of y.1)).getD i 0)
                    ((Denumerable.ofNat (List ℕ) (c₂Of y.1)).getD (y.2 - i) 0))) 0) := by
        have hN : Computable fun y : List ℕ × ℕ => y.2 + 1 :=
          Primrec.nat_add.to_comp.comp Computable.snd (Computable.const 1)
        have hidxProd : Computable fun z : (List ℕ × ℕ) × ℕ =>
            Nat.pair ((lvlOf z.1.1 - 2) + 1)
              (Nat.pair
                ((Denumerable.ofNat (List ℕ) (c₁Of z.1.1)).getD z.2 0)
                ((Denumerable.ofNat (List ℕ) (c₂Of z.1.1)).getD (z.1.2 - z.2) 0)) := by
          have hlevel : Computable fun z : (List ℕ × ℕ) × ℕ => (lvlOf z.1.1 - 2) + 1 :=
            Primrec.nat_add.to_comp.comp
              (hk.comp (Computable.fst.comp Computable.fst)) (Computable.const 1)
          have hleft : Computable fun z : (List ℕ × ℕ) × ℕ =>
              (Denumerable.ofNat (List ℕ) (c₁Of z.1.1)).getD z.2 0 :=
            (hget₁_z 0).comp
              (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
          have hdiff : Computable fun z : (List ℕ × ℕ) × ℕ => z.1.2 - z.2 :=
            Primrec.nat_sub.to_comp.comp (Computable.snd.comp Computable.fst)
              Computable.snd
          have hright : Computable fun z : (List ℕ × ℕ) × ℕ =>
              (Denumerable.ofNat (List ℕ) (c₂Of z.1.1)).getD (z.1.2 - z.2) 0 :=
            (hget₂_z 0).comp
              (Computable.pair (Computable.fst.comp Computable.fst) hdiff)
          exact Primrec₂.natPair.to_comp.comp hlevel
            (Primrec₂.natPair.to_comp.comp hleft hright)
        have hprod : Computable₂ fun (y : List ℕ × ℕ) i =>
            (y.1 : List ℕ).getD
              (Nat.pair ((lvlOf y.1 - 2) + 1)
                (Nat.pair
                  ((Denumerable.ofNat (List ℕ) (c₁Of y.1)).getD i 0)
                  ((Denumerable.ofNat (List ℕ) (c₂Of y.1)).getD (y.2 - i) 0))) 0 :=
          (((Primrec.list_getD 0).to_comp.comp
            (Computable.fst.comp Computable.fst) hidxProd).to₂).of_eq fun _ => rfl
        have hproducts : Computable fun y : List ℕ × ℕ =>
            (List.range (y.2 + 1)).map fun i =>
              (y.1 : List ℕ).getD
                (Nat.pair ((lvlOf y.1 - 2) + 1)
                  (Nat.pair
                    ((Denumerable.ofNat (List ℕ) (c₁Of y.1)).getD i 0)
                    ((Denumerable.ofNat (List ℕ) (c₂Of y.1)).getD (y.2 - i) 0))) 0 :=
          Computable.list_map (Primrec.list_range.to_comp.comp hN) hprod
        have hrev : Computable fun y : List ℕ × ℕ =>
            (((List.range (y.2 + 1)).map fun i =>
              (y.1 : List ℕ).getD
                (Nat.pair ((lvlOf y.1 - 2) + 1)
                  (Nat.pair
                    ((Denumerable.ofNat (List ℕ) (c₁Of y.1)).getD i 0)
                    ((Denumerable.ofNat (List ℕ) (c₂Of y.1)).getD (y.2 - i) 0))) 0).reverse) :=
          Computable.list_reverse.comp hproducts
        have hfoldStep : Computable₂ fun (y : List ℕ × ℕ) (p : ℕ × ℕ) =>
            addCodeAt (F := F) ((lvlOf y.1 - 2) + 1) p.2 p.1 := by
          exact (haddAtTable.comp
            (Computable.fst.comp Computable.fst)
            (Computable.pair (Computable.snd.comp Computable.snd)
              (Computable.fst.comp Computable.snd))).to₂
        have hfold := Computable.list_foldl hrev (Computable.const 0) hfoldStep
        exact hfold.of_eq fun y => by
          simp [sumCodes, List.foldl_reverse]
      exact hinner.to₂
    exact (Computable.list_map (Primrec.list_range.to_comp.comp hconvLen) hterm).of_eq fun t => rfl
  have htableBranch : Computable fun t : List ℕ =>
      Encodable.encode
        (trimTrailing 0
          (mulCodeLists 0
            (fun a b => (t : List ℕ).getD (Nat.pair ((lvlOf t - 2) + 1) (Nat.pair a b)) 0)
            (addCodeAt (F := F) ((lvlOf t - 2) + 1))
            (Denumerable.ofNat (List ℕ) (c₁Of t))
            (Denumerable.ofNat (List ℕ) (c₂Of t)))) :=
    Computable.encode.comp
      (computable_trimTrailing.comp
        (Computable.pair (Computable.const 0) hlistTable))
  have hzero : Computable fun t : List ℕ => decide (lvlOf t = 0) :=
    (@Primrec.eq ℕ _).decide.to_comp.comp hlvl (Computable.const 0)
  have hone : Computable fun t : List ℕ => decide (lvlOf t = 1) :=
    (@Primrec.eq ℕ _).decide.to_comp.comp hlvl (Computable.const 1)
  exact (Computable.cond hzero hbaseBranch
    (Computable.cond hone hinlineBranch htableBranch)).of_eq fun t => by
      by_cases h0 : lvlOf t = 0
      · simp [mulCodeStep, lvlOf, c₁Of, c₂Of, h0]
      · by_cases h1 : lvlOf t = 1
        · simp [mulCodeStep, lvlOf, c₁Of, c₂Of, h1]
        · simp [mulCodeStep, lvlOf, c₁Of, c₂Of, h0, h1, List.getD_eq_getElem?_getD]

set_option maxHeartbeats 5000000 in
-- The strong-recursion table proof builds a large computable step term.
set_option linter.flexible false in
theorem computable_mulCode :
    Computable (mulCode (F := F)) := by
  let f : ℕ → ℕ := fun N =>
    mulCodeAt (F := F) N.unpair.1 N.unpair.2.unpair.1 N.unpair.2.unpair.2
  have H : ∀ N, mulCodeStep (F := F) ((List.range N).map f) = f N := by
    intro N
    dsimp [f]
    unfold mulCodeStep
    rw [List.length_map, List.length_range]
    rcases hn0 : N.unpair.1 with _ | lvl
    · simp [hn0, mulCodeBase, mulCodeAt]
    · cases lvl with
      | zero =>
          unfold mulCodeBase
          simp [hn0, mulCodeAt]
      | succ k =>
          let c₁ := N.unpair.2.unpair.1
          let c₂ := N.unpair.2.unpair.2
          let l₁ := Denumerable.ofNat (List ℕ) c₁
          let l₂ := Denumerable.ofNat (List ℕ) c₂
          have hpair : Nat.pair (k + 2) (Nat.pair c₁ c₂) = N := by
            dsimp [c₁, c₂]
            simpa [hn0] using (Nat.pair_unpair N)
          have hmap :
              mulCodeLists 0
                (fun a b =>
                  (Option.map (fun i : ℕ =>
                    mulCodeAt (F := F) i.unpair.1 i.unpair.2.unpair.1
                      i.unpair.2.unpair.2)
                    (List.range N)[Nat.pair (k + 1) (Nat.pair a b)]?).getD 0)
                (addCodeAt (F := F) (k + 1)) l₁ l₂ =
              mulCodeLists (zeroCode (F := F) (k + 1))
                (mulCodeAt (F := F) (k + 1)) (addCodeAt (F := F) (k + 1)) l₁ l₂ := by
            apply List.map_congr_left
            intro s hs
            have hs' : s < l₁.length + l₂.length := by
              simpa [mulCodeLists] using List.mem_range.mp hs
            apply congrArg (sumCodes 0 (addCodeAt (F := F) (k + 1)))
            apply List.map_congr_left
            intro i hi
            have hlt :
                Nat.pair (k + 1) (Nat.pair (l₁.getD i 0) (l₂.getD (s - i) 0)) < N := by
              exact lt_of_lt_of_eq
                (pair_getD_mul_lt (k := k + 1) (c₁ := c₁) (c₂ := c₂) (s := s) (i := i)
                  (by simpa [l₁, l₂] using hs') hi) hpair
            have hlookup :
                ((List.range N).map f).getD
                  (Nat.pair (k + 1) (Nat.pair (l₁.getD i 0) (l₂.getD (s - i) 0))) 0 =
                f (Nat.pair (k + 1) (Nat.pair (l₁.getD i 0) (l₂.getD (s - i) 0))) :=
              table_getD (d := 0) hlt
            simpa [List.getD_eq_getElem?_getD, f, Nat.unpair_pair, zeroCode_succ]
              using hlookup
          have hnot0 : ¬ k + 1 + 1 = 0 := by omega
          have hnot1 : ¬ k + 1 + 1 = 1 := by omega
          simp [hn0, mulCodeAt, List.getD_eq_getElem?_getD]
          change trimTrailing 0
              (mulCodeLists 0
                (fun a b =>
                  (Option.map (fun i : ℕ =>
                    mulCodeAt (F := F) i.unpair.1 i.unpair.2.unpair.1
                      i.unpair.2.unpair.2)
                    (List.range N)[Nat.pair (k + 1) (Nat.pair a b)]?).getD 0)
                (addCodeAt (F := F) (k + 1)) l₁ l₂) =
            trimTrailing 0
              (mulCodeLists 0 (mulCodeAt (F := F) (k + 1))
                (addCodeAt (F := F) (k + 1)) l₁ l₂)
          rw [hmap]
          simp [zeroCode_succ]
  have hg : Computable₂ (fun (_ : Unit) (table : List ℕ) =>
      some (mulCodeStep (F := F) table)) := by
    exact (Computable.option_some.comp
      (computable_mulCodeStep (F := F).comp Computable.snd)).to₂
  exact (Computable.nat_strong_rec
    (fun (_ : Unit) N => f N)
    hg (fun _ n => by simpa using H n)).comp (Computable.const ()) Computable.id

theorem evalCodeAt_encode {Q : Type u} [CommRing Q] (φ : F →+* Q)
    (k : ℕ) (xs : List Q) (q : MvPolynomial (Fin k) F) :
    evalCodeAt (F := F) φ k xs (Encodable.encode q) =
      MvPolynomial.eval₂ φ (fun i : Fin k => xs.getD i 0) q := by
  induction k with
  | zero =>
      unfold evalCodeAt
      have hq :
          Encodable.decode (α := F) (Encodable.encode q) =
            some ((MvPolynomial.isEmptyAlgEquiv F (Fin 0)) q) := by
        rw [encode_fin_zero_eq_encode_coeff (F := F) q, Encodable.encodek]
      rw [hq]
      change φ (MvPolynomial.eval (fun a : Fin 0 => isEmptyElim a) q) =
        MvPolynomial.eval₂ φ (fun i : Fin 0 => xs.getD i 0) q
      rw [eval₂_fin_zero (F := F) φ (fun i : Fin 0 => xs.getD i 0) q]
  | succ k IH =>
      let P : Polynomial (MvPolynomial (Fin k) F) := towerEquiv F k q
      let pt : Fin (k + 1) → Q := fun i => xs.getD i 0
      have hcodes :
          Denumerable.ofNat (List ℕ) (Encodable.encode q) =
            ((polyCoeffs P).map Encodable.encode : List ℕ) := by
        dsimp [P]
        exact ofNat_encode_coeff_codes (F := F) k q
      unfold evalCodeAt
      rw [hcodes]
      rw [evalCodeAt_succ_coeffs (F := F) φ k xs IH (polyCoeffs P)]
      have hcoeff :
          (polyCoeffs P).map
              (MvPolynomial.eval₂ φ (fun i : Fin k => xs.getD i 0)) =
            (polyCoeffs P).map
              ((MvPolynomial.eval fun i : Fin k => xs.getD i 0) ∘
                MvPolynomial.map φ) := by
        apply List.map_congr_left
        intro a _ha
        exact eval₂_coeff_after_map (F := F) φ k xs a
      rw [hcoeff]
      let ψ : MvPolynomial (Fin k) F →+* Q :=
        (MvPolynomial.eval fun i : Fin k => xs.getD i 0).comp (MvPolynomial.map φ)
      change evalCoeffs (xs.getD k 0) ((polyCoeffs P).map ψ) =
        MvPolynomial.eval₂ φ (fun i : Fin (k + 1) => xs.getD i 0) q
      rw [_root_.Semicontinuity.evalCoeffs_map
        (R := MvPolynomial (Fin k) F) (S := Q)
        ψ (xs.getD k 0) P]
      have hmain :
          MvPolynomial.eval₂ φ pt q =
            Polynomial.eval (pt (Fin.last k))
              (Polynomial.map
                ((MvPolynomial.eval fun i : Fin k => pt (Fin.castSucc i)).comp
                  (MvPolynomial.map φ)) P) := by
        rw [MvPolynomial.eval₂_eq_eval_map]
        rw [mvPolynomial_eval_towerEquiv Q k pt (MvPolynomial.map φ q)]
        rw [towerEquiv_map F k φ q]
        rw [Polynomial.map_map]
      rw [hmain]
      rfl

private def evalCodeStep {Q : Type u} [CommRing Q] (φ : F →+* Q)
    (xs : List Q) (table : List Q) : Q :=
  let N := table.length
  let lvl := N.unpair.1
  let c := N.unpair.2
  if lvl = 0 then
    φ ((Encodable.decode (α := F) c).getD 0)
  else
    let k := lvl - 1
    let l := Denumerable.ofNat (List ℕ) c
    ((l.map fun e => table.getD (Nat.pair k e) 0).reverse).foldl
      (fun acc a => a + xs.getD k 0 * acc) 0

omit [ComputableRing F] in
private theorem computable_evalCodeStep {Q : Type u} [CommRing Q] [Primcodable Q]
    [ComputableRing Q] (φ : F →+* Q) (hφ : Computable φ) :
    Computable₂ (evalCodeStep (F := F) φ) := by
  let lvlOf : List Q → ℕ := fun t => t.length.unpair.1
  let cOf : List Q → ℕ := fun t => t.length.unpair.2
  have hlen : Computable fun t : List Q => t.length := Computable.list_length
  have hlvl : Computable lvlOf :=
    ((Primrec.fst.comp Primrec.unpair).to_comp).comp hlen
  have hc : Computable cOf :=
    ((Primrec.snd.comp Primrec.unpair).to_comp).comp hlen
  have hzeroTest : Computable fun x : List Q × List Q => decide (lvlOf x.2 = 0) :=
    (@Primrec.eq ℕ _).decide.to_comp.comp (hlvl.comp Computable.snd) (Computable.const 0)
  have hbase : Computable fun x : List Q × List Q =>
      φ ((Encodable.decode (α := F) (cOf x.2)).getD 0) := by
    have hdec : Computable fun x : List Q × List Q =>
        (Encodable.decode (α := F) (cOf x.2)).getD 0 :=
      Computable.option_getD (Computable.decode.comp (hc.comp Computable.snd))
        (Computable.const 0)
    exact hφ.comp hdec
  have hk : Computable fun x : List Q × List Q => lvlOf x.2 - 1 :=
    Primrec.nat_sub.to_comp.comp (hlvl.comp Computable.snd) (Computable.const 1)
  have hl : Computable fun x : List Q × List Q =>
      Denumerable.ofNat (List ℕ) (cOf x.2) :=
    (Primrec.ofNat (List ℕ)).to_comp.comp (hc.comp Computable.snd)
  have hvals : Computable fun x : List Q × List Q =>
      (Denumerable.ofNat (List ℕ) (cOf x.2)).map
        (fun e => x.2.getD (Nat.pair (lvlOf x.2 - 1) e) 0) := by
    have hidx : Computable fun y : (List Q × List Q) × ℕ =>
        Nat.pair (lvlOf y.1.2 - 1) y.2 :=
      Primrec₂.natPair.to_comp.comp (hk.comp Computable.fst) Computable.snd
    have hlook : Computable₂ fun x e =>
        (x : List Q × List Q).2.getD (Nat.pair (lvlOf x.2 - 1) e) 0 :=
      (((Primrec.list_getD (α := Q) 0).to_comp.comp
        (Computable.snd.comp Computable.fst) hidx).to₂).of_eq fun _ => rfl
    exact Computable.list_map hl hlook
  have hrevVals : Computable fun x : List Q × List Q =>
      ((Denumerable.ofNat (List ℕ) (cOf x.2)).map
        (fun e => x.2.getD (Nat.pair (lvlOf x.2 - 1) e) 0)).reverse :=
    Computable.list_reverse.comp hvals
  have hfoldStep : Computable₂ fun (x : List Q × List Q) (p : Q × Q) =>
      p.2 + x.1.getD (lvlOf x.2 - 1) 0 * p.1 := by
    have hxget : Computable fun y : (List Q × List Q) × (Q × Q) =>
        y.1.1.getD (lvlOf y.1.2 - 1) 0 :=
      have hxs : Computable fun y : (List Q × List Q) × (Q × Q) => y.1.1 :=
        Computable.fst.comp
          (Computable.fst : Computable (fun y : (List Q × List Q) × (Q × Q) => y.1))
      (Primrec.list_getD (α := Q) 0).to_comp.comp hxs (hk.comp Computable.fst)
    have hmul : Computable fun y : (List Q × List Q) × (Q × Q) =>
        y.1.1.getD (lvlOf y.1.2 - 1) 0 * y.2.1 :=
      ComputableRing.computable_mul.comp hxget
        (Computable.fst.comp Computable.snd)
    exact (ComputableRing.computable_add.comp
      (Computable.snd.comp Computable.snd) hmul).to₂
  have hsucc : Computable fun x : List Q × List Q =>
      (((Denumerable.ofNat (List ℕ) (cOf x.2)).map
        (fun e => x.2.getD (Nat.pair (lvlOf x.2 - 1) e) 0)).reverse).foldl
          (fun acc a => a + x.1.getD (lvlOf x.2 - 1) 0 * acc) 0 :=
    Computable.list_foldl hrevVals (Computable.const 0) hfoldStep
  exact (Computable.cond hzeroTest hbase hsucc).to₂.of_eq fun x => by
    rcases x with ⟨xs, table⟩
    simp [evalCodeStep, lvlOf, cOf]

omit [ComputableRing F] in
theorem computable_evalCode {Q : Type u} [CommRing Q] [Primcodable Q]
    [ComputableRing Q] (φ : F →+* Q) (hφ : Computable φ) :
    Computable₂ (evalCode (F := F) φ) := by
  let f : List Q → ℕ → Q := fun xs N =>
    evalCodeAt (F := F) φ N.unpair.1 xs N.unpair.2
  have H : ∀ xs N,
      evalCodeStep (F := F) φ xs ((List.range N).map (f xs)) = f xs N := by
    intro xs N
    dsimp [f]
    unfold evalCodeStep
    rw [List.length_map, List.length_range]
    cases hn : N.unpair.1 with
    | zero =>
        simp [hn, evalCodeAt]
    | succ k =>
        let c := N.unpair.2
        let l := Denumerable.ofNat (List ℕ) c
        have hpair : Nat.pair (k + 1) c = N := by
          dsimp [c]
          simpa [hn] using (Nat.pair_unpair N)
        have hmap :
            (l.map fun e =>
              (Option.map (fun i : ℕ =>
                evalCodeAt (F := F) φ i.unpair.1 xs i.unpair.2)
                (List.range N)[Nat.pair k e]?).getD 0) =
            l.map fun e => evalCodeAt (F := F) φ k xs e := by
          apply List.map_congr_left
          intro e he
          have hlt : Nat.pair k e < N := by
            exact lt_of_lt_of_eq (pair_mem_lt (n := k) (c := c) he) hpair
          have hlookup :
              ((List.range N).map (f xs)).getD (Nat.pair k e) 0 =
                f xs (Nat.pair k e) :=
            table_getD (d := 0) hlt
          simpa [List.getD_eq_getElem?_getD, f, Nat.unpair_pair] using hlookup
        have hfold :
            ((l.map fun e => evalCodeAt (F := F) φ k xs e).reverse).foldl
              (fun acc a => a + xs.getD k 0 * acc) 0 =
            (l.map fun e => evalCodeAt (F := F) φ k xs e).foldr
              (fun a acc => a + xs.getD k 0 * acc) 0 := by
          simp [List.foldl_reverse]
        simp [hn, evalCodeAt, l, c, hmap]
  have hg : Computable₂ fun xs table =>
      some (evalCodeStep (F := F) φ xs table) := by
    exact Computable.option_some.comp₂ (computable_evalCodeStep (F := F) φ hφ)
  exact (Computable.nat_strong_rec
    (fun xs N => evalCodeAt (F := F) φ N.unpair.1 xs N.unpair.2)
    hg (fun xs N => congrArg some (H xs N))).of_eq fun _ => rfl

lemma liftIter_add (a b n c : ℕ) :
    liftIter (F := F) (a + b) n c =
      liftIter (F := F) b (n + a) (liftIter (F := F) a n c) := by
  induction a generalizing n c with
  | zero =>
      simp [liftIter]
  | succ a ih =>
      rw [show a + 1 + b = a + b + 1 by omega]
      rw [show n + (a + 1) = n + 1 + a by omega]
      rw [liftIter]
      exact ih (n + 1) (liftOnce (F := F) n c)

set_option maxHeartbeats 5000000 in
-- The primitive-recursive iterator proof builds a nested `Nat.rec` state over encoded pairs.
theorem computable_liftTo_code :
    Computable fun x : ℕ × ℕ × ℕ => liftTo (F := F) x.1 x.2.1 x.2.2 := by
  have hzeroRec : Primrec (zeroCodeRec (F := F)) := by
    refine (Primrec.ite
      ((@Primrec.eq ℕ _).comp Primrec.id (Primrec.const 0))
      (Primrec.const (Encodable.encode (0 : F))) (Primrec.const 0)).of_eq ?_
    intro n
    cases n <;> rfl
  have hliftOnce : Primrec fun s : ℕ × ℕ => liftOnce (F := F) s.1 s.2 := by
    have htest : PrimrecPred fun s : ℕ × ℕ => s.2 = zeroCodeRec (F := F) s.1 :=
      (@Primrec.eq ℕ _).comp Primrec.snd (hzeroRec.comp Primrec.fst)
    have hsuccPair : Primrec fun s : ℕ × ℕ => Nat.succ (Nat.pair s.2 0) :=
      Primrec.succ.comp (Primrec₂.natPair.comp Primrec.snd (Primrec.const 0))
    exact (Primrec.ite htest (Primrec.const 0) hsuccPair).of_eq fun s => by
      rw [liftOnce, zeroCodeRec_eq_zeroCode]
  have hfuel : Primrec fun x : ℕ × ℕ × ℕ => x.1 - x.2.1 :=
    Primrec.nat_sub.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hinit : Primrec fun x : ℕ × ℕ × ℕ => (x.2.1, x.2.2) :=
    Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hstep : Primrec₂ fun (_x : ℕ × ℕ × ℕ) (p : ℕ × (ℕ × ℕ)) =>
      (p.2.1 + 1, liftOnce (F := F) p.2.1 p.2.2) := by
    have hlvl : Primrec fun y : (ℕ × ℕ × ℕ) × (ℕ × (ℕ × ℕ)) => y.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have hcode : Primrec fun y : (ℕ × ℕ × ℕ) × (ℕ × (ℕ × ℕ)) => y.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have hnextLvl : Primrec fun y : (ℕ × ℕ × ℕ) × (ℕ × (ℕ × ℕ)) => y.2.2.1 + 1 :=
      Primrec.succ.comp hlvl
    have hnextCode : Primrec fun y : (ℕ × ℕ × ℕ) × (ℕ × (ℕ × ℕ)) =>
        liftOnce (F := F) y.2.2.1 y.2.2.2 :=
      hliftOnce.comp (Primrec.pair hlvl hcode)
    exact (Primrec.pair hnextLvl hnextCode).to₂
  have hrec : Primrec fun x : ℕ × ℕ × ℕ =>
      Nat.rec (motive := fun _ => ℕ × ℕ) (x.2.1, x.2.2)
        (fun _ s => (s.1 + 1, liftOnce (F := F) s.1 s.2)) (x.1 - x.2.1) :=
    Primrec.nat_rec' hfuel hinit hstep
  exact (Primrec.snd.comp hrec).to_comp.of_eq fun x => by
    rcases x with ⟨m, n, c⟩
    unfold liftTo
    change (Nat.rec (motive := fun _ => ℕ × ℕ) (n, c)
      (fun _ s => (s.1 + 1, liftOnce (F := F) s.1 s.2)) (m - n)).2 =
        liftIter (F := F) (m - n) n c
    have hiter : ∀ fuel n c,
        Nat.rec (motive := fun _ => ℕ × ℕ) (n, c)
          (fun _ s => (s.1 + 1, liftOnce (F := F) s.1 s.2)) fuel =
        (n + fuel, liftIter (F := F) fuel n c) := by
      intro fuel
      induction fuel with
      | zero =>
          intro n c
          rfl
      | succ fuel ih =>
          intro n c
          change
            ((Nat.rec (motive := fun _ => ℕ × ℕ) (n, c)
              (fun _ s => (s.1 + 1, liftOnce (F := F) s.1 s.2)) fuel).1 + 1,
              liftOnce (F := F)
                (Nat.rec (motive := fun _ => ℕ × ℕ) (n, c)
                  (fun _ s => (s.1 + 1, liftOnce (F := F) s.1 s.2)) fuel).1
                (Nat.rec (motive := fun _ => ℕ × ℕ) (n, c)
                  (fun _ s => (s.1 + 1, liftOnce (F := F) s.1 s.2)) fuel).2) =
            (n + (fuel + 1), liftIter (F := F) (fuel + 1) n c)
          rw [liftIter]
          rw [ih n c]
          have hcomp := liftIter_add (F := F) fuel 1 n c
          apply Prod.ext
          · omega
          · simpa [liftIter, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcomp.symm
    exact congrArg Prod.snd (hiter (m - n) n c)

set_option maxHeartbeats 5000000 in
-- The canonical descent proof packages a computable state iterator over decoded coefficient lists.
theorem computable_canonDown_code :
    Computable fun x : ℕ × ℕ => canonDown (F := F) x.1 x.2 := by
  have hzeroRec : Computable (zeroCodeRec (F := F)) := by
    have htest : Computable fun n : ℕ => decide (n = 0) :=
      (@Primrec.eq ℕ _).decide.to_comp.comp Computable.id (Computable.const 0)
    exact (Computable.cond htest
      (Computable.const (Encodable.encode (0 : F)))
      (Computable.const 0)).of_eq fun n => by
        cases n <;> rfl
  have hstepFun : Computable fun s : ℕ × ℕ => canonDownStep (F := F) s := by
    let lOf : ℕ × ℕ → List ℕ := fun s => Denumerable.ofNat (List ℕ) s.2
    have hl : Computable lOf := (Primrec.ofNat (List ℕ)).to_comp.comp Computable.snd
    have hpredLvl : Computable fun s : ℕ × ℕ => s.1 - 1 :=
      Primrec.nat_sub.to_comp.comp Computable.fst (Computable.const 1)
    have hzeroLvl : Computable fun s : ℕ × ℕ => decide (s.1 = 0) :=
      (@Primrec.eq ℕ _).decide.to_comp.comp Computable.fst (Computable.const 0)
    have hlen : Computable fun s : ℕ × ℕ => (lOf s).length :=
      Computable.list_length.comp hl
    have hlen0 : Computable fun s : ℕ × ℕ => decide ((lOf s).length = 0) :=
      (@Primrec.eq ℕ _).decide.to_comp.comp hlen (Computable.const 0)
    have hlen1 : Computable fun s : ℕ × ℕ => decide ((lOf s).length = 1) :=
      (@Primrec.eq ℕ _).decide.to_comp.comp hlen (Computable.const 1)
    have hhead : Computable fun s : ℕ × ℕ => (lOf s).headD 0 := by
      have hget : Computable fun s : ℕ × ℕ => (lOf s).getD 0 0 :=
        (Primrec.list_getD (α := ℕ) 0).to_comp.comp hl (Computable.const 0)
      exact hget.of_eq fun s => by cases lOf s <;> rfl
    have hzeroBranch : Computable fun s : ℕ × ℕ => (0, s.2) :=
      Computable.pair (Computable.const 0) Computable.snd
    have hemptyBranch : Computable fun s : ℕ × ℕ =>
        (s.1 - 1, zeroCodeRec (F := F) (s.1 - 1)) :=
      Computable.pair hpredLvl (hzeroRec.comp hpredLvl)
    have hsingleBranch : Computable fun s : ℕ × ℕ => (s.1 - 1, (lOf s).headD 0) :=
      Computable.pair hpredLvl hhead
    have hlongBranch : Computable fun s : ℕ × ℕ => (s.1, s.2) :=
      Computable.id
    have hsuccBranch : Computable fun s : ℕ × ℕ =>
        if (lOf s).length = 0 then (s.1 - 1, zeroCodeRec (F := F) (s.1 - 1))
        else if (lOf s).length = 1 then (s.1 - 1, (lOf s).headD 0)
        else (s.1, s.2) :=
      (Computable.cond hlen0 hemptyBranch
        (Computable.cond hlen1 hsingleBranch hlongBranch)).of_eq fun s => by
          by_cases h0 : (lOf s).length = 0 <;>
            by_cases h1 : (lOf s).length = 1 <;> simp [h0, h1]
    exact (Computable.cond hzeroLvl hzeroBranch hsuccBranch).of_eq fun s => by
      rcases s with ⟨lvl, c⟩
      cases lvl with
      | zero =>
          rfl
      | succ lvl =>
          simp [canonDownStep, lOf, zeroCodeRec_eq_zeroCode]
  have hstep : Computable₂ fun (_x : ℕ × ℕ) (p : ℕ × (ℕ × ℕ)) =>
      canonDownStep (F := F) p.2 := by
    exact (hstepFun.comp (Computable.snd.comp Computable.snd)).to₂
  have hrec : Computable fun x : ℕ × ℕ =>
      Nat.rec (motive := fun _ => ℕ × ℕ) (x.1, x.2)
        (fun _ s => canonDownStep (F := F) s) x.1 :=
    Computable.nat_rec Computable.fst Computable.id hstep
  exact hrec.of_eq fun x => by
    rcases x with ⟨m, c⟩
    unfold canonDown
    have haux : ∀ fuel (s : ℕ × ℕ),
        Nat.rec (motive := fun _ => ℕ × ℕ) s
          (fun _ s => canonDownStep (F := F) s) fuel =
        canonDownAux (F := F) fuel s := by
      have hcomm : ∀ fuel (s : ℕ × ℕ),
          canonDownAux (F := F) fuel (canonDownStep (F := F) s) =
            canonDownStep (F := F) (canonDownAux (F := F) fuel s) := by
        intro fuel
        induction fuel with
        | zero =>
            intro s
            rfl
        | succ fuel ih =>
            intro s
            rw [canonDownAux_succ, ih (canonDownStep (F := F) s)]
            rfl
      intro fuel
      induction fuel with
      | zero =>
          intro s
          rfl
      | succ fuel ih =>
          intro s
          rw [canonDownAux_succ]
          change canonDownStep (F := F)
              (Nat.rec (motive := fun _ => ℕ × ℕ) s
                (fun _ s => canonDownStep (F := F) s) fuel) =
            canonDownAux (F := F) fuel (canonDownStep (F := F) s)
          rw [ih s]
          exact (hcomm fuel s).symm
    exact haux m (m, c)

set_option maxHeartbeats 8000000 in
-- The final `of_eq` grinds ~10⁶ concrete reduction steps through the
-- `Encodable`/`Nat.unpair` chains when matching the composed code function
-- against `mvNatAddCode`; the computation is finite but needs a raised
-- heartbeat budget.
theorem computable_mvNatAddCode :
    Computable₂ (mvNatAddCode (F := F)) := by
  have hn₁ : Computable fun p : ℕ × ℕ => p.1.unpair.1 :=
    ((Primrec.fst (β := ℕ)).comp (Primrec.unpair.comp Primrec.fst)).to_comp
  have hc₁ : Computable fun p : ℕ × ℕ => p.1.unpair.2 :=
    ((Primrec.snd (α := ℕ)).comp (Primrec.unpair.comp Primrec.fst)).to_comp
  have hn₂ : Computable fun p : ℕ × ℕ => p.2.unpair.1 :=
    ((Primrec.fst (β := ℕ)).comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hc₂ : Computable fun p : ℕ × ℕ => p.2.unpair.2 :=
    ((Primrec.snd (α := ℕ)).comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hm : Computable fun p : ℕ × ℕ => max p.1.unpair.1 p.2.unpair.1 :=
    (Primrec.nat_max.comp
      ((Primrec.fst (β := ℕ)).comp (Primrec.unpair.comp Primrec.fst))
      ((Primrec.fst (β := ℕ)).comp (Primrec.unpair.comp Primrec.snd))).to_comp
  -- untyped composition chain: no `have`-type unification against the big
  -- recursive code functions (that unification is what explodes)
  have hlift₁ := (computable_liftTo_code (F := F)).comp (hm.pair (hn₁.pair hc₁))
  have hlift₂ := (computable_liftTo_code (F := F)).comp (hm.pair (hn₂.pair hc₂))
  have haddraw := (computable_addCode (F := F)).comp
    (Primrec₂.natPair.to_comp.comp hm (Primrec₂.natPair.to_comp.comp hlift₁ hlift₂))
  have hcanon := (computable_canonDown_code (F := F)).comp (hm.pair haddraw)
  have hfinal := Primrec₂.natPair.to_comp.comp
    (Computable.fst.comp hcanon) (Computable.snd.comp hcanon)
  -- pin the target function explicitly so `of_eq` has no open metavariable
  have key : Computable fun p : ℕ × ℕ => mvNatAddCode (F := F) p.1 p.2 := by
    refine hfinal.of_eq fun p => ?_
    show Nat.pair _ _ = mvNatAddCode (F := F) p.1 p.2
    rw [mvNatAddCode, addCode, Nat.unpair_pair, Nat.unpair_pair]
  exact key.to₂

set_option maxHeartbeats 8000000 in
-- The final `of_eq` follows the same large composition pattern as
-- `computable_mvNatAddCode`.
theorem computable_mvNatMulCode :
    Computable₂ (mvNatMulCode (F := F)) := by
  have hn₁ : Computable fun p : ℕ × ℕ => p.1.unpair.1 :=
    ((Primrec.fst (β := ℕ)).comp (Primrec.unpair.comp Primrec.fst)).to_comp
  have hc₁ : Computable fun p : ℕ × ℕ => p.1.unpair.2 :=
    ((Primrec.snd (α := ℕ)).comp (Primrec.unpair.comp Primrec.fst)).to_comp
  have hn₂ : Computable fun p : ℕ × ℕ => p.2.unpair.1 :=
    ((Primrec.fst (β := ℕ)).comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hc₂ : Computable fun p : ℕ × ℕ => p.2.unpair.2 :=
    ((Primrec.snd (α := ℕ)).comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hm : Computable fun p : ℕ × ℕ => max p.1.unpair.1 p.2.unpair.1 :=
    (Primrec.nat_max.comp
      ((Primrec.fst (β := ℕ)).comp (Primrec.unpair.comp Primrec.fst))
      ((Primrec.fst (β := ℕ)).comp (Primrec.unpair.comp Primrec.snd))).to_comp
  have hlift₁ := (computable_liftTo_code (F := F)).comp (hm.pair (hn₁.pair hc₁))
  have hlift₂ := (computable_liftTo_code (F := F)).comp (hm.pair (hn₂.pair hc₂))
  have hmulraw := (computable_mulCode (F := F)).comp
    (Primrec₂.natPair.to_comp.comp hm (Primrec₂.natPair.to_comp.comp hlift₁ hlift₂))
  have hcanon := (computable_canonDown_code (F := F)).comp (hm.pair hmulraw)
  have hfinal := Primrec₂.natPair.to_comp.comp
    (Computable.fst.comp hcanon) (Computable.snd.comp hcanon)
  have key : Computable fun p : ℕ × ℕ => mvNatMulCode (F := F) p.1 p.2 := by
    refine hfinal.of_eq fun p => ?_
    show Nat.pair _ _ = mvNatMulCode (F := F) p.1 p.2
    rw [mvNatMulCode, mulCode, Nat.unpair_pair, Nat.unpair_pair]
  exact key.to₂

theorem addNatCode_correct (p q : MvPolynomial ℕ F) :
    mvNatAddCode (F := F) (Encodable.encode p) (Encodable.encode q) =
      Encodable.encode (p + q) := by
  unfold mvNatAddCode
  rw [encode_eq_pair (F := F) p, encode_eq_pair (F := F) q]
  simp only [Nat.unpair_pair]
  let n₁ := level (F := F) p
  let c₁ := Encodable.encode (restrictLevel (F := F) n₁ p)
  let n₂ := level (F := F) q
  let c₂ := Encodable.encode (restrictLevel (F := F) n₂ q)
  let m := max n₁ n₂
  have hp_le : n₁ ≤ m := le_max_left _ _
  have hq_le : n₂ ≤ m := le_max_right _ _
  have hp_lift :
      liftTo (F := F) m n₁ c₁ =
        Encodable.encode (restrictLevel (F := F) m p) := by
    exact liftTo_encode_restrict (F := F) hp_le p le_rfl
  have hq_lift :
      liftTo (F := F) m n₂ c₂ =
        Encodable.encode (restrictLevel (F := F) m q) := by
    exact liftTo_encode_restrict (F := F) hq_le q le_rfl
  rw [hp_lift, hq_lift]
  rw [addCodeAt_encode (F := F) m
    (restrictLevel (F := F) m p) (restrictLevel (F := F) m q)]
  rw [← map_add]
  rw [canonDown_encode_pair (F := F) m
    (restrictLevel (F := F) m (p + q))]
  rw [incl_restrictLevel_of_level_le (F := F)]
  exact level_add_le (F := F) p q

theorem mulNatCode_correct (p q : MvPolynomial ℕ F) :
    mvNatMulCode (F := F) (Encodable.encode p) (Encodable.encode q) =
      Encodable.encode (p * q) := by
  unfold mvNatMulCode
  rw [encode_eq_pair (F := F) p, encode_eq_pair (F := F) q]
  simp only [Nat.unpair_pair]
  let n₁ := level (F := F) p
  let c₁ := Encodable.encode (restrictLevel (F := F) n₁ p)
  let n₂ := level (F := F) q
  let c₂ := Encodable.encode (restrictLevel (F := F) n₂ q)
  let m := max n₁ n₂
  have hp_le : n₁ ≤ m := le_max_left _ _
  have hq_le : n₂ ≤ m := le_max_right _ _
  have hp_lift :
      liftTo (F := F) m n₁ c₁ =
        Encodable.encode (restrictLevel (F := F) m p) := by
    exact liftTo_encode_restrict (F := F) hp_le p le_rfl
  have hq_lift :
      liftTo (F := F) m n₂ c₂ =
        Encodable.encode (restrictLevel (F := F) m q) := by
    exact liftTo_encode_restrict (F := F) hq_le q le_rfl
  rw [hp_lift, hq_lift]
  rw [mulCodeAt_encode (F := F) m
    (restrictLevel (F := F) m p) (restrictLevel (F := F) m q)]
  rw [← map_mul]
  rw [canonDown_encode_pair (F := F) m
    (restrictLevel (F := F) m (p * q))]
  rw [incl_restrictLevel_of_level_le (F := F)]
  exact level_mul_le (F := F) p q

theorem evalNatCode_correct {Q : Type u} [CommRing Q] (φ : F →+* Q)
    (xs : List Q) (p : MvPolynomial ℕ F) :
    evalCodeAt (F := F) φ (Encodable.encode p).unpair.1 xs
        (Encodable.encode p).unpair.2 =
      MvPolynomial.eval₂ φ (fun i : ℕ => xs.getD i 0) p := by
  rw [encode_eq_pair (F := F) p]
  simp only [Nat.unpair_pair]
  rw [evalCodeAt_encode (F := F) φ (level (F := F) p) xs
    (restrictLevel (F := F) (level (F := F) p) p)]
  calc
    MvPolynomial.eval₂ φ
        (fun i : Fin (level (F := F) p) => xs.getD i 0)
        (restrictLevel (F := F) (level (F := F) p) p)
        =
      MvPolynomial.eval₂ φ (fun i : ℕ => xs.getD i 0)
        (inclLevel (F := F) (level (F := F) p)
          (restrictLevel (F := F) (level (F := F) p) p)) := by
        rw [inclLevel, MvPolynomial.eval₂_rename]
        rfl
    _ = MvPolynomial.eval₂ φ (fun i : ℕ => xs.getD i 0) p := by
      rw [incl_restrictLevel_level (F := F) p]

/-! ## Countable-variable operations

Rabin's admissibility assertion (`rabin.tex`:357, "Since `F` is computable,
`i_R` is an admissible indexing of `R`") requires computability of the ring
operations.  This phase supplies the public countable-variable API for
addition, multiplication, and evaluation.  The `ComputableRing` instance is
the formal admissibility of the indexing `i_R` of `R = F[x₁,x₂,…]`.
-/

/-- Constants are computable for the least-level tower coding of
`MvPolynomial ℕ F`. -/
theorem computable_mvPolynomialNat_C :
    Computable fun a : F => (MvPolynomial.C a : MvPolynomial ℕ F) := by
  refine Computable.encode_iff.mp ?_
  have hpair : Computable fun a : F => Nat.pair 0 (Encodable.encode a) :=
    Primrec₂.natPair.to_comp.comp (Computable.const 0) Computable.encode
  refine hpair.of_eq ?_
  intro a
  symm
  rw [encode_eq_pair]
  have hlevel : level (F := F) (MvPolynomial.C a : MvPolynomial ℕ F) = 0 := by
    simp [level]
  rw [hlevel]
  change Nat.pair 0
      (Encodable.encode (restrictLevel (F := F) 0 (MvPolynomial.C a))) =
    Nat.pair 0 (Encodable.encode a)
  congr 1
  rw [encode_fin_zero_eq_encode_coeff]
  simp [restrictLevel]

/-- Variables are computable for the least-level tower coding of
`MvPolynomial ℕ F`.  The nontrivial hypothesis is used by the explicit
variable-code formula; fields satisfy it. -/
theorem computable_mvPolynomialNat_X [Nontrivial F] :
    Computable fun i : ℕ => (MvPolynomial.X i : MvPolynomial ℕ F) := by
  refine Computable.encode_iff.mp ?_
  have hzeroRec : Computable (zeroCodeRec (F := F)) := by
    have htest : Computable fun n : ℕ => decide (n = 0) :=
      (@Primrec.eq ℕ _).decide.to_comp.comp Computable.id (Computable.const 0)
    exact (Computable.cond htest
      (Computable.const (Encodable.encode (0 : F)))
      (Computable.const 0)).of_eq fun n => by
        cases n <;> rfl
  have honeRec : Computable (oneCodeRec (F := F)) := by
    have hstep : Computable₂ fun (_ : ℕ) (p : ℕ × ℕ) =>
        Nat.succ (Nat.pair p.2 0) := by
      have hprev : Computable fun x : ℕ × (ℕ × ℕ) => x.2.2 :=
        Computable.snd.comp Computable.snd
      exact (Primrec.succ.to_comp.comp
        (Primrec₂.natPair.to_comp.comp hprev (Computable.const 0))).to₂
    exact (Computable.nat_rec Computable.id
      (Computable.const (Encodable.encode (1 : F))) hstep).of_eq fun n => by
        induction n with
        | zero => rfl
        | succ n ih =>
            rw [oneCodeRec]
            exact congrArg (fun c => Nat.succ (Nat.pair c 0)) ih
  have hinner : Computable fun i : ℕ =>
      Nat.succ (Nat.pair (zeroCodeRec (F := F) i)
        (Nat.succ (Nat.pair (oneCodeRec (F := F) i) 0))) := by
    have htail : Computable fun i : ℕ =>
        Nat.succ (Nat.pair (oneCodeRec (F := F) i) 0) :=
      Primrec.succ.to_comp.comp
        (Primrec₂.natPair.to_comp.comp honeRec (Computable.const 0))
    exact Primrec.succ.to_comp.comp
      (Primrec₂.natPair.to_comp.comp hzeroRec htail)
  have hcode : Computable fun i : ℕ =>
      Nat.pair (i + 1)
        (Nat.succ (Nat.pair (zeroCodeRec (F := F) i)
          (Nat.succ (Nat.pair (oneCodeRec (F := F) i) 0)))) := by
    have hlevel : Computable fun i : ℕ => i + 1 :=
      Primrec.succ.to_comp
    exact Primrec₂.natPair.to_comp.comp hlevel hinner
  exact hcode.of_eq fun i => by
    rw [encode_mvPolynomialNat_X (F := F) i]
    rw [zeroCodeRec_eq_zeroCode (F := F) i, oneCodeRec_eq_oneCode (F := F) i]
    rfl

/-- Countable-variable polynomial addition is computable for the canonical
least-level tower coding.

This is the `+` half of Rabin's admissible indexing claim for
`R = F[x₁,x₂,…]` (`rabin.tex`:357).  Multiplication is Phase D1b. -/
theorem computable₂_mvPolynomialNat_add :
    Computable₂
      ((· + ·) : MvPolynomial ℕ F → MvPolynomial ℕ F → MvPolynomial ℕ F) := by
  refine Computable.encode_iff.mp ?_
  have hcode : Computable fun x : MvPolynomial ℕ F × MvPolynomial ℕ F =>
      mvNatAddCode (F := F) (Encodable.encode x.1) (Encodable.encode x.2) :=
    (computable_mvNatAddCode (F := F)).comp
      (Computable.encode.comp Computable.fst)
      (Computable.encode.comp Computable.snd)
  exact hcode.of_eq fun x => by
    exact addNatCode_correct (F := F) x.1 x.2

/-- Countable-variable polynomial multiplication is computable for the
canonical least-level tower coding.

Together with addition, this completes Rabin's admissible indexing claim for
`R = F[x₁,x₂,…]` (`rabin.tex`:357). -/
theorem computable₂_mvPolynomialNat_mul :
    Computable₂
      ((· * ·) : MvPolynomial ℕ F → MvPolynomial ℕ F → MvPolynomial ℕ F) := by
  refine Computable.encode_iff.mp ?_
  have hcode : Computable fun x : MvPolynomial ℕ F × MvPolynomial ℕ F =>
      mvNatMulCode (F := F) (Encodable.encode x.1) (Encodable.encode x.2) :=
    (computable_mvNatMulCode (F := F)).comp
      (Computable.encode.comp Computable.fst)
      (Computable.encode.comp Computable.snd)
  exact hcode.of_eq fun x => by
    exact mulNatCode_correct (F := F) x.1 x.2

instance instComputableRingMvPolynomialNat : ComputableRing (MvPolynomial ℕ F) :=
  { computable_add := computable₂_mvPolynomialNat_add (F := F)
    computable_mul := computable₂_mvPolynomialNat_mul (F := F) }

/-- Uniform countable-variable `eval₂` into a fixed computable ring.

The point is read from a list as `i ↦ xs.getD i 0`, and coefficients are mapped
through the computable ring homomorphism `φ`.  This is the form needed later
with `Q = Polynomial F` and `φ = Polynomial.C`, and also specializes to plain
evaluation using `RingHom.id`. -/
theorem computable₂_mvPolynomialNat_eval {Q : Type u} [CommRing Q] [Primcodable Q]
    [ComputableRing Q] (φ : F →+* Q) (hφ : Computable φ) :
    Computable₂ fun (xs : List Q) (p : MvPolynomial ℕ F) =>
      MvPolynomial.eval₂ φ (fun i : ℕ => xs.getD i 0) p := by
  have h : Computable fun x : List Q × MvPolynomial ℕ F =>
      evalCodeAt (F := F) φ (Encodable.encode x.2).unpair.1 x.1
        (Encodable.encode x.2).unpair.2 := by
    have henc : Computable fun x : List Q × MvPolynomial ℕ F =>
        Encodable.encode x.2 :=
      Computable.encode.comp Computable.snd
    have hN : Computable fun x : List Q × MvPolynomial ℕ F =>
        Nat.pair (Encodable.encode x.2).unpair.1 (Encodable.encode x.2).unpair.2 :=
      Primrec₂.natPair.to_comp.comp
        ((Primrec.fst.comp Primrec.unpair).to_comp.comp henc)
        ((Primrec.snd.comp Primrec.unpair).to_comp.comp henc)
    have heval : Computable fun x : List Q × MvPolynomial ℕ F =>
        evalCode (F := F) φ x.1
          (Nat.pair (Encodable.encode x.2).unpair.1
            (Encodable.encode x.2).unpair.2) :=
      (computable_evalCode (F := F) φ hφ).comp Computable.fst hN
    exact heval.of_eq fun x => by
      simp [evalCode]
  exact h.to₂.of_eq fun x => by
    exact evalNatCode_correct (F := F) φ x.1 x.2

section Examples

/-- Example: countable-variable rational polynomial addition is computable. -/
example : Computable₂
    ((· + ·) : MvPolynomial ℕ ℚ → MvPolynomial ℕ ℚ → MvPolynomial ℕ ℚ) :=
  computable₂_mvPolynomialNat_add (F := ℚ)

/-- Example: countable-variable rational polynomial multiplication is
computable. -/
example : Computable₂
    ((· * ·) : MvPolynomial ℕ ℚ → MvPolynomial ℕ ℚ → MvPolynomial ℕ ℚ) :=
  computable₂_mvPolynomialNat_mul (F := ℚ)

/-- Example: the `ComputableRing` addition projection fires for rational
countable-variable polynomials. -/
example : Computable₂
    ((· + ·) : MvPolynomial ℕ ℚ → MvPolynomial ℕ ℚ → MvPolynomial ℕ ℚ) :=
  ComputableRing.computable_add

/-- Example: the `ComputableRing` multiplication projection fires for rational
countable-variable polynomials. -/
example : Computable₂
    ((· * ·) : MvPolynomial ℕ ℚ → MvPolynomial ℕ ℚ → MvPolynomial ℕ ℚ) :=
  ComputableRing.computable_mul

/-- Example: countable-variable rational polynomial evaluation is computable. -/
example : Computable₂ fun (xs : List ℚ) (p : MvPolynomial ℕ ℚ) =>
    MvPolynomial.eval₂ (RingHom.id ℚ) (fun i : ℕ => xs.getD i 0) p :=
  computable₂_mvPolynomialNat_eval (F := ℚ) (Q := ℚ) (RingHom.id ℚ) Computable.id

/-- Example: rational constants are computable as countable-variable
polynomials. -/
example : Computable fun a : ℚ => (MvPolynomial.C a : MvPolynomial ℕ ℚ) :=
  computable_mvPolynomialNat_C (F := ℚ)

/-- Example: rational countable-variable polynomial variables are computable. -/
example : Computable fun i : ℕ => (MvPolynomial.X i : MvPolynomial ℕ ℚ) :=
  computable_mvPolynomialNat_X (F := ℚ)

end Examples

end CountableInstance

end MvPolynomialNat

end Semicontinuity
