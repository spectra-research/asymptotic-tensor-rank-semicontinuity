/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.ComputableField
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.ListComputable
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Rat.Defs

/-!
# Computable fields: instances

Concrete fields satisfying `ComputableField` (Rabin's computable fields), so
that the algorithm of Theorem 1.1 applies to them:

* **finite fields**: every function between finite `Primcodable` types is
  computable (a finite lookup table), so the field operations of a finite
  `Primcodable` field — e.g. `ZMod p` for `p` prime — are computable for
  free;
* **the rationals** `ℚ`, coded by the (numerator, denominator) pair in lowest
  terms; the field operations are computable because integer arithmetic is
  computable on the sign–magnitude coding of `ℤ`.

For `ℚ` we install an explicitly effective `Primcodable` instance (the
reduced-fraction coding). Mathlib's generic instance
(`Primcodable.ofDenumerable`, priority 10) codes `ℚ` through an abstract
enumeration, against which arithmetic is not directly accessible; instances
declared here take precedence, and all computability statements about `ℚ`
in this development refer to the reduced-fraction coding.
-/

universe u

namespace Semicontinuity

/-! ## Functions on finite types are computable -/

/-- Every function from a finite `Primcodable` type is computable: tabulate
it. -/
theorem _root_.Computable.of_finite {α σ : Type*} [Primcodable α] [Finite α]
    [Primcodable σ] (f : α → σ) : Computable f := by
  classical
  haveI := Fintype.ofFinite α
  have h : Computable fun a : α =>
      ((Finset.univ.toList (α := α)).map f)[(Finset.univ.toList (α := α)).idxOf a]? :=
    Computable.list_getElem?.comp (Computable.const _)
      (Primrec₂.comp Primrec.list_idxOf Primrec.id
        (Primrec.const (Finset.univ.toList (α := α)))).to_comp
  refine Computable.option_some_iff.mp (h.of_eq fun a => ?_)
  have hmem : a ∈ Finset.univ.toList (α := α) := by simp
  have hlt : (Finset.univ.toList (α := α)).idxOf a
      < (Finset.univ.toList (α := α)).length := List.idxOf_lt_length_of_mem hmem
  rw [List.getElem?_eq_getElem (by simpa using hlt)]
  simp [List.getElem_idxOf]

/-! ## Finite fields -/

/-- `ZMod n` is coded as `ℤ` (for `n = 0`) or `Fin n` (for `n > 0`). -/
instance instPrimcodableZMod : ∀ n : ℕ, Primcodable (ZMod n)
  | 0 => inferInstanceAs (Primcodable ℤ)
  | n + 1 => inferInstanceAs (Primcodable (Fin (n + 1)))

/-- **Finite fields are computable fields** (Rabin 1960, §2.1): on a finite
`Primcodable` field every operation is computable by table lookup, whatever
the coding. In particular `ZMod p` for `p` prime. -/
instance instComputableFieldOfFinite (F : Type*) [Field F] [Finite F]
    [Primcodable F] : ComputableField F where
  computable_add := (Computable.of_finite fun x : F × F => x.1 + x.2 : _).to₂
  computable_mul := (Computable.of_finite fun x : F × F => x.1 * x.2 : _).to₂

/-! ## Integer arithmetic is computable

`ℤ` is coded by Mathlib's `Denumerable ℤ` instance: through
`Equiv.intEquivNatSumNat`, a nonnegative `n` is coded as `Sum.inl n` and
`-(n+1)` as `Sum.inr n`. We make this sign–magnitude representation
computable in both directions and transport the arithmetic of `ℕ` along it.
-/

section IntComputable

private lemma encode_int_ofNat (n : ℕ) :
    @Encodable.encode ℤ Primcodable.toEncodable (Int.ofNat n) = 2 * n := by
  rfl

private lemma encode_int_negSucc (n : ℕ) :
    @Encodable.encode ℤ Primcodable.toEncodable (Int.negSucc n) = 2 * n + 1 := by
  rfl

private lemma encode_intEquivNatSumNat (z : ℤ) :
    @Encodable.encode (ℕ ⊕ ℕ) Primcodable.toEncodable (Equiv.intEquivNatSumNat z) =
      @Encodable.encode ℤ Primcodable.toEncodable z := by
  rcases z with n | n <;> rfl

private lemma encode_intEquivNatSumNat_symm (s : ℕ ⊕ ℕ) :
    @Encodable.encode ℤ Primcodable.toEncodable (Equiv.intEquivNatSumNat.symm s) =
      @Encodable.encode (ℕ ⊕ ℕ) Primcodable.toEncodable s := by
  rcases s with n | n <;> rfl

private lemma computable_intEquivNatSumNat :
    Computable fun z : ℤ => Equiv.intEquivNatSumNat z := by
  exact Computable.encode_iff.mp
    (Computable.encode.of_eq fun z => (encode_intEquivNatSumNat z).symm)

private lemma computable_intEquivNatSumNat_symm :
    Computable fun s : ℕ ⊕ ℕ => Equiv.intEquivNatSumNat.symm s := by
  exact Computable.encode_iff.mp
    (Computable.encode.of_eq fun s => (encode_intEquivNatSumNat_symm s).symm)

private def intCodeAdd (c d : ℕ) : ℕ :=
  let a := c / 2
  let b := d / 2
  if c.bodd then
    if d.bodd then 2 * (a + b + 1) + 1
    else if a < b then 2 * (b - a - 1) else 2 * (a - b) + 1
  else
    if d.bodd then if b < a then 2 * (a - b - 1) else 2 * (b - a) + 1
    else 2 * (a + b)

private def intCodeMul (c d : ℕ) : ℕ :=
  let a := c / 2
  let b := d / 2
  if c.bodd then
    if d.bodd then 2 * ((a + 1) * (b + 1))
    else if b = 0 then 0 else 2 * ((a + 1) * b - 1) + 1
  else
    if d.bodd then if a = 0 then 0 else 2 * (a * (b + 1) - 1) + 1
    else 2 * (a * b)

private theorem primrec₂_intCodeAdd : Primrec₂ intCodeAdd := by
  unfold intCodeAdd
  let half₁ : ℕ × ℕ → ℕ := fun p => p.1 / 2
  let half₂ : ℕ × ℕ → ℕ := fun p => p.2 / 2
  have hhalf₁ : Primrec half₁ := Primrec.nat_div.comp Primrec.fst (Primrec.const 2)
  have hhalf₂ : Primrec half₂ := Primrec.nat_div.comp Primrec.snd (Primrec.const 2)
  have hbodd₁ : Primrec fun p : ℕ × ℕ => p.1.bodd := Primrec.nat_bodd.comp Primrec.fst
  have hbodd₂ : Primrec fun p : ℕ × ℕ => p.2.bodd := Primrec.nat_bodd.comp Primrec.snd
  have hbodd₁p : PrimrecPred fun p : ℕ × ℕ => p.1.bodd = true :=
    Primrec.eq.comp hbodd₁ (Primrec.const true)
  have hbodd₂p : PrimrecPred fun p : ℕ × ℕ => p.2.bodd = true :=
    Primrec.eq.comp hbodd₂ (Primrec.const true)
  have hlt₂₁ : PrimrecPred fun p : ℕ × ℕ => half₂ p < half₁ p :=
    Primrec.nat_lt.comp hhalf₂ hhalf₁
  have hlt₁₂ : PrimrecPred fun p : ℕ × ℕ => half₁ p < half₂ p :=
    Primrec.nat_lt.comp hhalf₁ hhalf₂
  have hnn : Primrec fun p : ℕ × ℕ => 2 * (half₁ p + half₂ p) :=
    Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_add.comp hhalf₁ hhalf₂)
  have hnp_pos : Primrec fun p : ℕ × ℕ => 2 * (half₁ p - half₂ p - 1) :=
    Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.nat_sub.comp (Primrec.nat_sub.comp hhalf₁ hhalf₂) (Primrec.const 1))
  have hnp_neg : Primrec fun p : ℕ × ℕ => 2 * (half₂ p - half₁ p) + 1 :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_sub.comp hhalf₂ hhalf₁))
      (Primrec.const 1)
  have hpn_pos : Primrec fun p : ℕ × ℕ => 2 * (half₂ p - half₁ p - 1) :=
    Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.nat_sub.comp (Primrec.nat_sub.comp hhalf₂ hhalf₁) (Primrec.const 1))
  have hpn_neg : Primrec fun p : ℕ × ℕ => 2 * (half₁ p - half₂ p) + 1 :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_sub.comp hhalf₁ hhalf₂))
      (Primrec.const 1)
  have hpp : Primrec fun p : ℕ × ℕ => 2 * (half₁ p + half₂ p + 1) + 1 :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_add.comp (Primrec.nat_add.comp hhalf₁ hhalf₂) (Primrec.const 1)))
      (Primrec.const 1)
  change Primrec fun p : ℕ × ℕ => intCodeAdd p.1 p.2
  refine Primrec.ite hbodd₁p ?_ ?_
  · refine Primrec.ite hbodd₂p hpp ?_
    exact Primrec.ite hlt₁₂ hpn_pos hpn_neg
  · refine Primrec.ite hbodd₂p ?_ hnn
    exact Primrec.ite hlt₂₁ hnp_pos hnp_neg

private theorem primrec₂_intCodeMul : Primrec₂ intCodeMul := by
  unfold intCodeMul
  let half₁ : ℕ × ℕ → ℕ := fun p => p.1 / 2
  let half₂ : ℕ × ℕ → ℕ := fun p => p.2 / 2
  have hhalf₁ : Primrec half₁ := Primrec.nat_div.comp Primrec.fst (Primrec.const 2)
  have hhalf₂ : Primrec half₂ := Primrec.nat_div.comp Primrec.snd (Primrec.const 2)
  have hbodd₁ : Primrec fun p : ℕ × ℕ => p.1.bodd := Primrec.nat_bodd.comp Primrec.fst
  have hbodd₂ : Primrec fun p : ℕ × ℕ => p.2.bodd := Primrec.nat_bodd.comp Primrec.snd
  have hbodd₁p : PrimrecPred fun p : ℕ × ℕ => p.1.bodd = true :=
    Primrec.eq.comp hbodd₁ (Primrec.const true)
  have hbodd₂p : PrimrecPred fun p : ℕ × ℕ => p.2.bodd = true :=
    Primrec.eq.comp hbodd₂ (Primrec.const true)
  have heq₁ : PrimrecPred fun p : ℕ × ℕ => half₁ p = 0 :=
    Primrec.eq.comp hhalf₁ (Primrec.const 0)
  have heq₂ : PrimrecPred fun p : ℕ × ℕ => half₂ p = 0 :=
    Primrec.eq.comp hhalf₂ (Primrec.const 0)
  have hnn : Primrec fun p : ℕ × ℕ => 2 * (half₁ p * half₂ p) :=
    Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_mul.comp hhalf₁ hhalf₂)
  have hnp_zero : Primrec fun _ : ℕ × ℕ => 0 := Primrec.const 0
  have hnp_neg : Primrec fun p : ℕ × ℕ => 2 * (half₁ p * (half₂ p + 1) - 1) + 1 :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_sub.comp
          (Primrec.nat_mul.comp hhalf₁ (Primrec.nat_add.comp hhalf₂ (Primrec.const 1)))
          (Primrec.const 1)))
      (Primrec.const 1)
  have hpn_zero : Primrec fun _ : ℕ × ℕ => 0 := Primrec.const 0
  have hpn_neg : Primrec fun p : ℕ × ℕ => 2 * ((half₁ p + 1) * half₂ p - 1) + 1 :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_sub.comp
          (Primrec.nat_mul.comp (Primrec.nat_add.comp hhalf₁ (Primrec.const 1)) hhalf₂)
          (Primrec.const 1)))
      (Primrec.const 1)
  have hpp : Primrec fun p : ℕ × ℕ => 2 * ((half₁ p + 1) * (half₂ p + 1)) :=
    Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.nat_mul.comp (Primrec.nat_add.comp hhalf₁ (Primrec.const 1))
        (Primrec.nat_add.comp hhalf₂ (Primrec.const 1)))
  change Primrec fun p : ℕ × ℕ => intCodeMul p.1 p.2
  refine Primrec.ite hbodd₁p ?_ ?_
  · refine Primrec.ite hbodd₂p hpp ?_
    exact Primrec.ite heq₂ hpn_zero hpn_neg
  · refine Primrec.ite hbodd₂p ?_ hnn
    exact Primrec.ite heq₁ hnp_zero hnp_neg

set_option linter.flexible false in
private lemma encode_int_add_eq (z w : ℤ) :
    @Encodable.encode ℤ Primcodable.toEncodable (z + w) =
      intCodeAdd (@Encodable.encode ℤ Primcodable.toEncodable z)
        (@Encodable.encode ℤ Primcodable.toEncodable w) := by
  rcases z with a | a <;> rcases w with b | b
  · change @Encodable.encode ℤ Primcodable.toEncodable (Int.ofNat a + Int.ofNat b) =
      intCodeAdd (2 * a) (2 * b)
    rw [show (Int.ofNat a + Int.ofNat b) = Int.ofNat (a + b) by norm_num]
    rw [encode_int_ofNat]
    simp [intCodeAdd]
  · change @Encodable.encode ℤ Primcodable.toEncodable (Int.ofNat a + Int.negSucc b) =
      intCodeAdd (2 * a) (2 * b + 1)
    have hbhalf : (2 * b + 1) / 2 = b := by omega
    simp [intCodeAdd, hbhalf]
    split_ifs with h
    · rw [show ((a : ℤ) + Int.negSucc b) = Int.ofNat (a - b - 1) by
        rw [Int.negSucc_eq]
        norm_num
        omega]
      rw [encode_int_ofNat]
    · rw [show ((a : ℤ) + Int.negSucc b) = Int.negSucc (b - a) by
        rw [Int.negSucc_eq]
        norm_num
        omega]
      rw [encode_int_negSucc]
  · change @Encodable.encode ℤ Primcodable.toEncodable (Int.negSucc a + Int.ofNat b) =
      intCodeAdd (2 * a + 1) (2 * b)
    have hahalf : (2 * a + 1) / 2 = a := by omega
    simp [intCodeAdd, hahalf]
    split_ifs with h
    · rw [show (Int.negSucc a + (b : ℤ)) = Int.ofNat (b - a - 1) by
        rw [Int.negSucc_eq]
        norm_num
        omega]
      rw [encode_int_ofNat]
    · rw [show (Int.negSucc a + (b : ℤ)) = Int.negSucc (a - b) by
        rw [Int.negSucc_eq]
        norm_num
        omega]
      rw [encode_int_negSucc]
  · change @Encodable.encode ℤ Primcodable.toEncodable (Int.negSucc a + Int.negSucc b) =
      intCodeAdd (2 * a + 1) (2 * b + 1)
    have hahalf : (2 * a + 1) / 2 = a := by omega
    have hbhalf : (2 * b + 1) / 2 = b := by omega
    rw [show (Int.negSucc a + Int.negSucc b) = Int.negSucc (a + b + 1) by
      rw [Int.negSucc_eq]
      norm_num
      omega]
    rw [encode_int_negSucc]
    simp [intCodeAdd, hahalf, hbhalf]

set_option linter.flexible false in
private lemma encode_int_mul_eq (z w : ℤ) :
    @Encodable.encode ℤ Primcodable.toEncodable (z * w) =
      intCodeMul (@Encodable.encode ℤ Primcodable.toEncodable z)
        (@Encodable.encode ℤ Primcodable.toEncodable w) := by
  rcases z with a | a <;> rcases w with b | b
  · change @Encodable.encode ℤ Primcodable.toEncodable (Int.ofNat a * Int.ofNat b) =
      intCodeMul (2 * a) (2 * b)
    rw [show (Int.ofNat a * Int.ofNat b) = Int.ofNat (a * b) by norm_num]
    rw [encode_int_ofNat]
    simp [intCodeMul]
  · change @Encodable.encode ℤ Primcodable.toEncodable (Int.ofNat a * Int.negSucc b) =
      intCodeMul (2 * a) (2 * b + 1)
    have hbhalf : (2 * b + 1) / 2 = b := by omega
    simp [intCodeMul, hbhalf]
    split_ifs with h
    · rw [show ((a : ℤ) * Int.negSucc b) = Int.ofNat 0 by simp [h]]
      rw [encode_int_ofNat]
    · rw [show ((a : ℤ) * Int.negSucc b) = Int.negSucc (a * (b + 1) - 1) by
        have hpos : 0 < a * (b + 1) := Nat.mul_pos (Nat.pos_of_ne_zero h) (Nat.succ_pos b)
        have hsub : a * (b + 1) - 1 + 1 = a * (b + 1) := Nat.sub_add_cancel hpos
        simp only [Int.negSucc_eq]
        rw [show -(↑(a * (b + 1) - 1) + 1) = -((a * (b + 1) : ℕ) : ℤ) by
          have hcast : ((a * (b + 1) - 1 : ℕ) : ℤ) + 1 =
              (a * (b + 1) : ℕ) := by exact_mod_cast hsub
          omega]
        simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_one]
        simp [mul_add]]
      rw [encode_int_negSucc]
  · change @Encodable.encode ℤ Primcodable.toEncodable (Int.negSucc a * Int.ofNat b) =
      intCodeMul (2 * a + 1) (2 * b)
    have hahalf : (2 * a + 1) / 2 = a := by omega
    simp [intCodeMul, hahalf]
    split_ifs with h
    · rw [show (Int.negSucc a * (b : ℤ)) = Int.ofNat 0 by simp [h]]
      rw [encode_int_ofNat]
    · rw [show (Int.negSucc a * (b : ℤ)) = Int.negSucc ((a + 1) * b - 1) by
        have hpos : 0 < (a + 1) * b := Nat.mul_pos (Nat.succ_pos a) (Nat.pos_of_ne_zero h)
        have hsub : (a + 1) * b - 1 + 1 = (a + 1) * b := Nat.sub_add_cancel hpos
        simp only [Int.negSucc_eq]
        rw [show -(↑((a + 1) * b - 1) + 1) = -(((a + 1) * b : ℕ) : ℤ) by
          have hcast : (((a + 1) * b - 1 : ℕ) : ℤ) + 1 =
              ((a + 1) * b : ℕ) := by exact_mod_cast hsub
          omega]
        simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_one]
        simp [add_mul]]
      rw [encode_int_negSucc]
  · change @Encodable.encode ℤ Primcodable.toEncodable (Int.negSucc a * Int.negSucc b) =
      intCodeMul (2 * a + 1) (2 * b + 1)
    have hahalf : (2 * a + 1) / 2 = a := by omega
    have hbhalf : (2 * b + 1) / 2 = b := by omega
    rw [show (Int.negSucc a * Int.negSucc b) = Int.ofNat ((a + 1) * (b + 1)) by
      simp [Int.negSucc_eq, mul_add, add_mul]
      ac_rfl]
    rw [encode_int_ofNat]
    simp [intCodeMul, hahalf, hbhalf]

theorem computable₂_int_add : Computable₂ ((· + ·) : ℤ → ℤ → ℤ) := by
  change Computable fun p : ℤ × ℤ => p.1 + p.2
  refine Computable.encode_iff.mp ?_
  have hcode : Computable fun p : ℤ × ℤ =>
      intCodeAdd (@Encodable.encode ℤ Primcodable.toEncodable p.1)
        (@Encodable.encode ℤ Primcodable.toEncodable p.2) :=
    primrec₂_intCodeAdd.to_comp.comp
      (Computable.encode.comp Computable.fst) (Computable.encode.comp Computable.snd)
  exact hcode.of_eq fun p => (encode_int_add_eq p.1 p.2).symm

theorem computable₂_int_mul : Computable₂ ((· * ·) : ℤ → ℤ → ℤ) := by
  change Computable fun p : ℤ × ℤ => p.1 * p.2
  refine Computable.encode_iff.mp ?_
  have hcode : Computable fun p : ℤ × ℤ =>
      intCodeMul (@Encodable.encode ℤ Primcodable.toEncodable p.1)
        (@Encodable.encode ℤ Primcodable.toEncodable p.2) :=
    primrec₂_intCodeMul.to_comp.comp
      (Computable.encode.comp Computable.fst) (Computable.encode.comp Computable.snd)
  exact hcode.of_eq fun p => (encode_int_mul_eq p.1 p.2).symm

theorem primrec_int_natAbs : Primrec Int.natAbs := by
  refine Primrec.encode_iff.mp ?_
  have h : Primrec fun z : ℤ =>
      ((@Encodable.encode ℤ Primcodable.toEncodable z + 1) / 2) :=
    Primrec.nat_div.comp
      (Primrec.nat_add.comp Primrec.encode (Primrec.const 1)) (Primrec.const 2)
  exact h.of_eq fun z => by
    rcases z with n | n
    · change (2 * n + 1) / 2 =
        @Encodable.encode ℕ Primcodable.toEncodable (Int.natAbs (Int.ofNat n))
      change (2 * n + 1) / 2 = n
      omega
    · change (2 * n + 1 + 1) / 2 =
        @Encodable.encode ℕ Primcodable.toEncodable (Int.natAbs (Int.negSucc n))
      change (2 * n + 1 + 1) / 2 = n + 1
      omega

theorem computable_int_ofNat : Computable (fun n : ℕ => (n : ℤ)) := by
  exact computable_intEquivNatSumNat_symm.comp Computable.sumInl

end IntComputable

/-! ## The rationals -/

section RatComputable

private def gcdSearch (m n : ℕ) : ℕ :=
  (m + n).findGreatest fun d => d ∣ m ∧ d ∣ n

private lemma gcd_le_sum (m n : ℕ) : Nat.gcd m n ≤ m + n := by
  by_cases hm : m = 0
  · rw [hm]
    simp
  · exact (Nat.gcd_le_left n (Nat.pos_of_ne_zero hm)).trans (Nat.le_add_right m n)

private lemma gcdSearch_eq (m n : ℕ) : gcdSearch m n = Nat.gcd m n := by
  unfold gcdSearch
  let d := Nat.findGreatest (fun d => d ∣ m ∧ d ∣ n) (m + n)
  change d = Nat.gcd m n
  apply le_antisymm
  · by_cases h0 : d = 0
    · rw [h0]
      exact zero_le _
    · have hdprop : d ∣ m ∧ d ∣ n := Nat.findGreatest_of_ne_zero rfl h0
      have hdg : d ∣ Nat.gcd m n := Nat.dvd_gcd hdprop.1 hdprop.2
      by_cases hm : m = 0
      · by_cases hn : n = 0
        · have hd0 : d = 0 := by simp [d, hm, hn]
          simp [hm, hn, hd0]
        · exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_right m (Nat.pos_of_ne_zero hn)) hdg
      · exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero hm)) hdg
  · exact Nat.le_findGreatest (gcd_le_sum m n)
      ⟨Nat.gcd_dvd_left m n, Nat.gcd_dvd_right m n⟩

/-- `Nat.gcd` is primitive recursive (strong recursion on the first
argument). -/
theorem primrec₂_nat_gcd : Primrec₂ Nat.gcd := by
  have hbound : Primrec fun p : ℕ × ℕ => p.1 + p.2 :=
    Primrec.nat_add.comp Primrec.fst Primrec.snd
  have hfst₂ : Primrec₂ fun (p : ℕ × ℕ) (_d : ℕ) => p.1 :=
    Primrec.fst.comp₂ Primrec₂.left
  have hsnd₂ : Primrec₂ fun (p : ℕ × ℕ) (_d : ℕ) => p.2 :=
    Primrec.snd.comp₂ Primrec₂.left
  have hmod₁ : Primrec₂ fun (p : ℕ × ℕ) (d : ℕ) => p.1 % d :=
    Primrec.nat_mod.comp₂ hfst₂ Primrec₂.right
  have hmod₂ : Primrec₂ fun (p : ℕ × ℕ) (d : ℕ) => p.2 % d :=
    Primrec.nat_mod.comp₂ hsnd₂ Primrec₂.right
  have hdvd₁ : PrimrecRel fun (p : ℕ × ℕ) (d : ℕ) => d ∣ p.1 :=
    (Primrec.eq.comp₂ hmod₁ (Primrec₂.const 0)).of_eq fun p d => by
      exact (Nat.dvd_iff_mod_eq_zero (m := d) (n := p.1)).symm
  have hdvd₂ : PrimrecRel fun (p : ℕ × ℕ) (d : ℕ) => d ∣ p.2 :=
    (Primrec.eq.comp₂ hmod₂ (Primrec₂.const 0)).of_eq fun p d => by
      exact (Nat.dvd_iff_mod_eq_zero (m := d) (n := p.2)).symm
  have hpred : PrimrecRel fun (p : ℕ × ℕ) (d : ℕ) => d ∣ p.1 ∧ d ∣ p.2 :=
    PrimrecPred.and hdvd₁ hdvd₂
  have hsearch : Primrec fun p : ℕ × ℕ => gcdSearch p.1 p.2 := by
    simpa [gcdSearch] using Primrec.nat_findGreatest hbound hpred
  change Primrec fun p : ℕ × ℕ => Nat.gcd p.1 p.2
  exact hsearch.of_eq fun p => gcdSearch_eq p.1 p.2

/-- A rational number is exactly a reduced (numerator, denominator) pair. -/
def ratReducedEquiv :
    ℚ ≃ {p : ℤ × ℕ // p.2 ≠ 0 ∧ p.1.natAbs.Coprime p.2} where
  toFun q := ⟨(q.num, q.den), q.den_nz, q.reduced⟩
  invFun p := ⟨p.1.1, p.1.2, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma primrecPred_ratReduced :
    PrimrecPred fun p : ℤ × ℕ => p.2 ≠ 0 ∧ p.1.natAbs.Coprime p.2 := by
  have hdenZero : PrimrecPred fun p : ℤ × ℕ => p.2 = 0 :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hden : PrimrecPred fun p : ℤ × ℕ => p.2 ≠ 0 :=
    PrimrecPred.not hdenZero
  have hnatAbs : Primrec fun p : ℤ × ℕ => p.1.natAbs :=
    primrec_int_natAbs.comp Primrec.fst
  have hgcd : Primrec fun p : ℤ × ℕ => Nat.gcd p.1.natAbs p.2 :=
    primrec₂_nat_gcd.comp hnatAbs Primrec.snd
  have hcop : PrimrecPred fun p : ℤ × ℕ => p.1.natAbs.Coprime p.2 :=
    (Primrec.eq.comp hgcd (Primrec.const 1)).of_eq fun p => by
      rfl
  exact PrimrecPred.and hden hcop

/-- **The reduced-fraction coding of `ℚ`**: a rational is coded by its
(numerator, denominator) pair in lowest terms. This coding is explicitly
effective; it takes precedence over the abstract enumeration coding
`Primcodable.ofDenumerable` (priority 10). -/
instance instPrimcodableRat : Primcodable ℚ :=
  haveI : Primcodable {p : ℤ × ℕ // p.2 ≠ 0 ∧ p.1.natAbs.Coprime p.2} :=
    Primcodable.subtype primrecPred_ratReduced
  Primcodable.ofEquiv _ ratReducedEquiv

theorem computable_rat_num : Computable Rat.num := by
  letI : Primcodable {p : ℤ × ℕ // p.2 ≠ 0 ∧ p.1.natAbs.Coprime p.2} :=
    Primcodable.subtype primrecPred_ratReduced
  have hred :
      @Computable ℚ {p : ℤ × ℕ // p.2 ≠ 0 ∧ p.1.natAbs.Coprime p.2}
        instPrimcodableRat (Primcodable.subtype primrecPred_ratReduced)
        (fun q : ℚ => ratReducedEquiv q) := by
    exact Computable.encode_iff.mp (Computable.encode.of_eq fun q => rfl)
  have hval : Computable fun q : ℚ => (ratReducedEquiv q).val :=
    (Primrec.subtype_val (hp := primrecPred_ratReduced)).to_comp.comp hred
  exact (Computable.fst.comp hval).of_eq fun q => rfl

theorem computable_rat_den : Computable Rat.den := by
  letI : Primcodable {p : ℤ × ℕ // p.2 ≠ 0 ∧ p.1.natAbs.Coprime p.2} :=
    Primcodable.subtype primrecPred_ratReduced
  have hred :
      @Computable ℚ {p : ℤ × ℕ // p.2 ≠ 0 ∧ p.1.natAbs.Coprime p.2}
        instPrimcodableRat (Primcodable.subtype primrecPred_ratReduced)
        (fun q : ℚ => ratReducedEquiv q) := by
    exact Computable.encode_iff.mp (Computable.encode.of_eq fun q => rfl)
  have hval : Computable fun q : ℚ => (ratReducedEquiv q).val :=
    (Primrec.subtype_val (hp := primrecPred_ratReduced)).to_comp.comp hred
  exact (Computable.snd.comp hval).of_eq fun q => rfl

private def mkRatSearchStep (p : ℤ × ℕ) (k : ℕ) : Option ℚ :=
  if p.2 = 0 then
    some 0
  else
    (Encodable.decode (α := ℚ) k).bind fun q =>
      if q.num * (p.2 : ℤ) = p.1 * (q.den : ℤ) then some q else none

private lemma rat_eq_mkRat_of_cross (n : ℤ) {d : ℕ} (hd : d ≠ 0) (q : ℚ)
    (h : q.num * (d : ℤ) = n * (q.den : ℤ)) : q = mkRat n d := by
  rw [Rat.mkRat_eq_divInt]
  rw [← Rat.num_divInt_den q]
  exact (Rat.divInt_eq_divInt_iff (by exact_mod_cast q.den_nz) (by exact_mod_cast hd)).2 h

private lemma mkRat_cross (n : ℤ) {d : ℕ} (hd : d ≠ 0) :
    (mkRat n d).num * (d : ℤ) = n * ((mkRat n d).den : ℤ) := by
  rw [← Rat.divInt_eq_divInt_iff (by exact_mod_cast (mkRat n d).den_nz)
    (by exact_mod_cast hd)]
  rw [Rat.num_divInt_den]
  exact Rat.mkRat_eq_divInt n d

private theorem computable₂_mkRatSearchStep : Computable₂ mkRatSearchStep := by
  let X := (ℤ × ℕ) × ℕ
  have hdenZero : Computable fun x : X => x.1.2 == 0 :=
    Primrec.beq.to_comp.comp (Primrec.snd.to_comp.comp Computable.fst) (Computable.const 0)
  have hsomeZero : Computable fun _ : X => (some 0 : Option ℚ) :=
    Computable.const (some 0)
  have hdecode : Computable fun x : X => Encodable.decode (α := ℚ) x.2 :=
    Computable.decode.comp Computable.snd
  have hnum : Computable fun y : X × ℚ => y.2.num :=
    computable_rat_num.comp Computable.snd
  have hdenNat : Computable fun y : X × ℚ => y.2.den :=
    computable_rat_den.comp Computable.snd
  have hdenInt : Computable fun y : X × ℚ => (y.2.den : ℤ) :=
    computable_int_ofNat.comp hdenNat
  have hinputDenInt : Computable fun y : X × ℚ => (y.1.1.2 : ℤ) :=
    computable_int_ofNat.comp (Primrec.snd.to_comp.comp (Primrec.fst.to_comp.comp
      (Computable.fst : Computable fun y : X × ℚ => y.1)))
  have hinputNum : Computable fun y : X × ℚ => y.1.1.1 :=
    Primrec.fst.to_comp.comp (Primrec.fst.to_comp.comp
      (Computable.fst : Computable fun y : X × ℚ => y.1))
  have hleft : Computable fun y : X × ℚ => y.2.num * (y.1.1.2 : ℤ) :=
    computable₂_int_mul.comp hnum hinputDenInt
  have hright : Computable fun y : X × ℚ => y.1.1.1 * (y.2.den : ℤ) :=
    computable₂_int_mul.comp hinputNum hdenInt
  have htest : Computable fun y : X × ℚ =>
      (y.2.num * (y.1.1.2 : ℤ) == y.1.1.1 * (y.2.den : ℤ)) :=
    Primrec.beq.to_comp.comp hleft hright
  have hsomeQ : Computable fun y : X × ℚ => some y.2 :=
    Computable.option_some.comp Computable.snd
  have hbranch : Computable₂ fun (x : X) (q : ℚ) =>
      if q.num * (x.1.2 : ℤ) = x.1.1 * (q.den : ℤ) then some q else none := by
    refine (Computable.cond htest hsomeQ (Computable.const Option.none)).to₂.of_eq ?_
    rintro ⟨x, q⟩
    dsimp
    by_cases hbeq : (q.num * (x.1.2 : ℤ) == x.1.1 * (q.den : ℤ)) = true
    · have h : q.num * (x.1.2 : ℤ) = x.1.1 * (q.den : ℤ) := beq_iff_eq.mp hbeq
      simp [h]
    · have h : ¬ q.num * (x.1.2 : ℤ) = x.1.1 * (q.den : ℤ) :=
        fun heq => hbeq (beq_iff_eq.mpr heq)
      have hfalse : (q.num * (x.1.2 : ℤ) == x.1.1 * (q.den : ℤ)) = false :=
        Bool.eq_false_iff.mpr hbeq
      simp [hfalse, h]
  have hsearch : Computable fun x : X =>
      (Encodable.decode (α := ℚ) x.2).bind fun q =>
        if q.num * (x.1.2 : ℤ) = x.1.1 * (q.den : ℤ) then some q else none :=
    Computable.option_bind hdecode hbranch
  refine (Computable.cond hdenZero hsomeZero hsearch).to₂.of_eq ?_
  rintro ⟨p, k⟩
  dsimp [mkRatSearchStep]
  by_cases hbeq : (p.2 == 0) = true
  · have h : p.2 = 0 := beq_iff_eq.mp hbeq
    simp [h]
  · have h : ¬p.2 = 0 := fun heq => hbeq (beq_iff_eq.mpr heq)
    have hfalse : (p.2 == 0) = false := Bool.eq_false_iff.mpr hbeq
    simp [hfalse, h]

set_option linter.flexible false in
theorem computable₂_mkRat : Computable₂ mkRat := by
  change Computable fun p : ℤ × ℕ => mkRat p.1 p.2
  refine (Partrec.rfindOpt computable₂_mkRatSearchStep).of_eq_tot fun p => ?_
  by_cases hd : p.2 = 0
  · have hdom : (Nat.rfindOpt (mkRatSearchStep p)).Dom :=
      Nat.rfindOpt_dom.2 ⟨0, 0, by simp [mkRatSearchStep, hd]⟩
    refine ⟨hdom, ?_⟩
    have hget := Nat.rfindOpt_spec (Part.get_mem hdom)
    rcases hget with ⟨k, hk⟩
    simp [mkRatSearchStep, hd] at hk
    simp [hd, hk]
  · have hwit : mkRat p.1 p.2 ∈ mkRatSearchStep p
        (@Encodable.encode ℚ Primcodable.toEncodable (mkRat p.1 p.2)) := by
      simp [mkRatSearchStep, hd, Encodable.encodek, mkRat_cross p.1 hd]
    have hdom : (Nat.rfindOpt (mkRatSearchStep p)).Dom :=
      Nat.rfindOpt_dom.2 ⟨_, _, hwit⟩
    refine ⟨hdom, ?_⟩
    have hget := Nat.rfindOpt_spec (Part.get_mem hdom)
    rcases hget with ⟨k, hk⟩
    simp [mkRatSearchStep, hd] at hk
    rcases hq : Encodable.decode (α := ℚ) k with _ | q
    · simp [hq] at hk
    · simp [hq] at hk
      rw [← hk.2]
      exact rat_eq_mkRat_of_cross p.1 hd q hk.1

/-- **`ℚ` is a computable field** (Rabin 1960, §2.1): the field operations
are computable on the reduced-fraction coding, via
`a + b = mkRat (a.num * b.den + b.num * a.den) (a.den * b.den)` and
`a * b = mkRat (a.num * b.num) (a.den * b.den)`, with computable integer
arithmetic. -/
instance instComputableFieldRat : ComputableField ℚ := by
  refine ⟨?_, ?_⟩
  · change Computable fun p : ℚ × ℚ => p.1 + p.2
    have hnum₁ : Computable fun p : ℚ × ℚ => p.1.num :=
      computable_rat_num.comp Computable.fst
    have hnum₂ : Computable fun p : ℚ × ℚ => p.2.num :=
      computable_rat_num.comp Computable.snd
    have hden₁ : Computable fun p : ℚ × ℚ => p.1.den :=
      computable_rat_den.comp Computable.fst
    have hden₂ : Computable fun p : ℚ × ℚ => p.2.den :=
      computable_rat_den.comp Computable.snd
    have hden₁Int : Computable fun p : ℚ × ℚ => (p.1.den : ℤ) :=
      computable_int_ofNat.comp hden₁
    have hden₂Int : Computable fun p : ℚ × ℚ => (p.2.den : ℤ) :=
      computable_int_ofNat.comp hden₂
    have hterm₁ : Computable fun p : ℚ × ℚ => p.1.num * (p.2.den : ℤ) :=
      computable₂_int_mul.comp hnum₁ hden₂Int
    have hterm₂ : Computable fun p : ℚ × ℚ => p.2.num * (p.1.den : ℤ) :=
      computable₂_int_mul.comp hnum₂ hden₁Int
    have hnum : Computable fun p : ℚ × ℚ =>
        p.1.num * (p.2.den : ℤ) + p.2.num * (p.1.den : ℤ) :=
      computable₂_int_add.comp hterm₁ hterm₂
    have hden : Computable fun p : ℚ × ℚ => p.1.den * p.2.den :=
      Primrec.nat_mul.to_comp.comp hden₁ hden₂
    exact (computable₂_mkRat.comp hnum hden).of_eq fun p => by
      rw [Rat.add_num_den, Rat.mkRat_eq_divInt]
      congr 1
      rw [mul_comm (p.2.num) (p.1.den : ℤ)]
  · change Computable fun p : ℚ × ℚ => p.1 * p.2
    have hnum₁ : Computable fun p : ℚ × ℚ => p.1.num :=
      computable_rat_num.comp Computable.fst
    have hnum₂ : Computable fun p : ℚ × ℚ => p.2.num :=
      computable_rat_num.comp Computable.snd
    have hden₁ : Computable fun p : ℚ × ℚ => p.1.den :=
      computable_rat_den.comp Computable.fst
    have hden₂ : Computable fun p : ℚ × ℚ => p.2.den :=
      computable_rat_den.comp Computable.snd
    have hnum : Computable fun p : ℚ × ℚ => p.1.num * p.2.num :=
      computable₂_int_mul.comp hnum₁ hnum₂
    have hden : Computable fun p : ℚ × ℚ => p.1.den * p.2.den :=
      Primrec.nat_mul.to_comp.comp hden₁ hden₂
    exact (computable₂_mkRat.comp hnum hden).of_eq fun p => by
      exact (Rat.mul_eq_mkRat p.1 p.2).symm

end RatComputable

end Semicontinuity
