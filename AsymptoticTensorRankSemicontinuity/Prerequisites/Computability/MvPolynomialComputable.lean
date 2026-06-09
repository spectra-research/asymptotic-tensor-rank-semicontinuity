/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.PolynomialComputable
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.ComputableFieldInstances
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Computable multivariate polynomials in finitely many variables

For a computable commutative ring `R`, the ring `MvPolynomial (Fin n) R` is
computable by coding it as an iterated univariate polynomial ring.  The tower
peels off the last variable:

`MvPolynomial (Fin (n+1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R)`.

Rabin's definition of a computable ring (Rabin 1960, §1.6, tex:264) asks for
an admissible indexing under which addition and multiplication are computable.
The particular tower coding below is a Lean engineering choice of such an
admissible indexing; the formal content remains exactly the computability of
`+` and `*`.
-/

noncomputable section

universe u

namespace Semicontinuity

open Polynomial

variable {R : Type u}

section Transport

variable {A B : Type u} [CommRing A] [CommRing B]
variable [Primcodable A]

/-- Transport the `Primcodable` coding across a ring equivalence.  With this
coding, `b : B` is encoded by the code of `e b : A`. -/
def primcodableOfRingEquiv (e : B ≃+* A) : Primcodable B :=
  Primcodable.ofEquiv A e.toEquiv

private theorem computable_ringEquiv_apply (e : B ≃+* A) :
    letI : Primcodable B := primcodableOfRingEquiv e
    Computable (e : B → A) := by
  letI : Primcodable B := primcodableOfRingEquiv e
  exact Computable.encode_iff.mp (Computable.encode.of_eq fun _ => rfl)

/-- Transport computability of addition across a ring equivalence whose
codomain already has Rabin's admissible indexing. -/
theorem computable₂_add_of_ringEquiv (e : B ≃+* A) :
    [ComputableRing A] →
    letI : Primcodable B := primcodableOfRingEquiv e
    Computable₂ ((· + ·) : B → B → B) := by
  intro _inst
  letI : ComputableRing A := _inst
  letI : Primcodable B := primcodableOfRingEquiv e
  have he : Computable (e : B → A) := computable_ringEquiv_apply e
  have hmap : Computable fun p : B × B => e p.1 + e p.2 :=
    ComputableRing.computable_add.comp (he.comp Computable.fst) (he.comp Computable.snd)
  have h : Computable fun p : B × B => p.1 + p.2 :=
    (Computable.encode_iff (α := B × B) (σ := B)).mp <|
      (Computable.encode.comp hmap).of_eq fun p => by
        change Encodable.encode (e p.1 + e p.2) = Encodable.encode (e (p.1 + p.2))
        rw [e.map_add]
  exact h.to₂

/-- Transport computability of multiplication across a ring equivalence whose
codomain already has Rabin's admissible indexing. -/
theorem computable₂_mul_of_ringEquiv (e : B ≃+* A) :
    [ComputableRing A] →
    letI : Primcodable B := primcodableOfRingEquiv e
    Computable₂ ((· * ·) : B → B → B) := by
  intro _inst
  letI : ComputableRing A := _inst
  letI : Primcodable B := primcodableOfRingEquiv e
  have he : Computable (e : B → A) := computable_ringEquiv_apply e
  have hmap : Computable fun p : B × B => e p.1 * e p.2 :=
    ComputableRing.computable_mul.comp (he.comp Computable.fst) (he.comp Computable.snd)
  have h : Computable fun p : B × B => p.1 * p.2 :=
    (Computable.encode_iff (α := B × B) (σ := B)).mp <|
      (Computable.encode.comp hmap).of_eq fun p => by
        change Encodable.encode (e p.1 * e p.2) = Encodable.encode (e (p.1 * p.2))
        rw [e.map_mul]
  exact h.to₂

/-- Transport computability of a map into a transported codomain. -/
theorem computable_of_ringEquiv_codomain {Γ : Type u} [Primcodable Γ]
    (e : B ≃+* A) {f : Γ → A} {g : Γ → B}
    (hf : Computable f) (h : ∀ x, e (g x) = f x) :
    letI : Primcodable B := primcodableOfRingEquiv e
    Computable g := by
  letI : Primcodable B := primcodableOfRingEquiv e
  refine (Computable.encode_iff (α := Γ) (σ := B)).mp ?_
  exact (Computable.encode.comp hf).of_eq fun x => by
    change Encodable.encode (f x) = Encodable.encode (e (g x))
    rw [h]

/-- The forward map of a transport equivalence is computable for the transported
coding. -/
theorem computable_ringEquiv_apply_of_transport (e : B ≃+* A) :
    letI : Primcodable B := primcodableOfRingEquiv e
    Computable (e : B → A) :=
  computable_ringEquiv_apply e

end Transport

section FiniteDomain

/-- The value of a `Fin n` index is computable; this is the definitional code of
`Fin n` as a primitive-recursive subtype of `ℕ`. -/
theorem computable_fin_val (n : ℕ) : Computable fun i : Fin n => (i : ℕ) :=
  Computable.encode_iff.mp (Computable.encode.of_eq fun _ => rfl)

/-- Every function from a finite `Fin n` domain to a coded codomain is
computable, by lookup in the fixed finite table `List.ofFn f`. -/
theorem computable_of_fin {β : Type u} [Primcodable β] (n : ℕ) (f : Fin n → β) :
    Computable f := by
  cases n with
  | zero =>
      refine Computable.encode_iff.mp ?_
      exact (Computable.const 0).of_eq fun i => Fin.elim0 i
  | succ n =>
      let l : List β := List.ofFn f
      have hget : Computable fun i : Fin (n + 1) => l.getD i.val (f 0) :=
        (Primrec.list_getD (f 0)).to_comp.comp (Computable.const l) (computable_fin_val (n + 1))
      exact hget.of_eq fun i => by
        dsimp [l]
        have hi : i.val < (List.ofFn f).length := by
          simpa using i.isLt
        rw [List.getD_eq_getElem _ _ hi]
        simpa using List.get_ofFn f ⟨i.val, hi⟩

end FiniteDomain

section Tower

variable (R)

/-- The last-variable tower equivalence
`MvPolynomial (Fin (n+1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R)`.
This peels the last variable, not variable `0`. -/
def towerEquiv [CommRing R] (n : ℕ) :
    MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R) :=
  (MvPolynomial.renameEquiv R finSuccEquivLast).trans
    (MvPolynomial.optionEquivLeft R (Fin n))

private theorem optionEquivLeft_rename_some [CommRing R] {S : Type*}
    (p : MvPolynomial S R) :
    MvPolynomial.optionEquivLeft R S (MvPolynomial.rename some p) = Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      simp
  | add p q hp hq =>
      simp [map_add, hp, hq]
  | mul_X p i hp =>
      simp [map_mul, hp]

/-- Last-variable tower evaluation identity.  This is the algebraic bridge used
to make multivariate evaluation computable for Rabin's Lemma 5 zero tests
(Rabin 1960, Lemma 5, tex:336-351). -/
theorem mvPolynomial_eval_towerEquiv [CommRing R] (n : ℕ)
    (x : Fin (n + 1) → R) (p : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.eval x p =
      Polynomial.eval (x (Fin.last n))
        (Polynomial.map (MvPolynomial.eval fun i : Fin n => x (Fin.castSucc i))
          (towerEquiv R n p)) := by
  let y : Option (Fin n) → R := fun o =>
    Option.elim o (x (Fin.last n)) fun i => x (Fin.castSucc i)
  have hy : y ∘ finSuccEquivLast = x := by
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp [y, finSuccEquivLast_castSucc]
    · simp [y, finSuccEquivLast_last]
  calc
    MvPolynomial.eval x p =
        MvPolynomial.eval y
          (MvPolynomial.rename finSuccEquivLast p) := by
          rw [MvPolynomial.eval_rename]
          exact congr_arg (fun z => MvPolynomial.eval z p) hy.symm
    _ = Polynomial.eval (x (Fin.last n))
        (Polynomial.map (MvPolynomial.eval fun i : Fin n => x (Fin.castSucc i))
          (MvPolynomial.optionEquivLeft R (Fin n)
            (MvPolynomial.rename finSuccEquivLast p))) := by
          simpa [y] using
            (MvPolynomial.optionEquivLeft_elim_eval
              (R := R) (S₁ := Fin n)
              (fun i : Fin n => x (Fin.castSucc i)) (x (Fin.last n))
              (MvPolynomial.rename finSuccEquivLast p))
    _ = Polynomial.eval (x (Fin.last n))
        (Polynomial.map (MvPolynomial.eval fun i : Fin n => x (Fin.castSucc i))
          (towerEquiv R n p)) := by
          rfl

/-- The last-variable tower equivalence commutes with scalar coefficient maps.
This is part of the computable ring-operation infrastructure implicit in
Rabin's admissible indexing (Rabin 1960, §1.6, tex:264). -/
theorem towerEquiv_map [CommRing R] {S : Type u} [CommRing S] (n : ℕ)
    (f : R →+* S) (p : MvPolynomial (Fin (n + 1)) R) :
    towerEquiv S n (MvPolynomial.map f p) =
      Polynomial.map (MvPolynomial.map f) (towerEquiv R n p) := by
  suffices
      (towerEquiv S n).toRingEquiv.toRingHom.comp (MvPolynomial.map f) =
        (Polynomial.mapRingHom (MvPolynomial.map f)).comp
          (towerEquiv R n).toRingEquiv.toRingHom by
    exact DFunLike.congr_fun this p
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [towerEquiv]
  · intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp [towerEquiv, finSuccEquivLast_castSucc]
    · simp [towerEquiv, finSuccEquivLast_last]

theorem towerEquiv_rename_castSucc [CommRing R] (n : ℕ)
    (p : MvPolynomial (Fin n) R) :
    towerEquiv R n (MvPolynomial.rename Fin.castSucc p) = Polynomial.C p := by
  rw [towerEquiv, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_rename]
  have hfun : (finSuccEquivLast ∘ (Fin.castSucc : Fin n → Fin (n + 1))) = some := by
    funext i
    exact finSuccEquivLast_castSucc i
  rw [hfun]
  exact optionEquivLeft_rename_some R p

theorem natDegree_towerEquiv_eq_zero_iff [CommRing R] (n : ℕ)
    (p : MvPolynomial (Fin (n + 1)) R) :
    (towerEquiv R n p).natDegree = 0 ↔
      ∃ q : MvPolynomial (Fin n) R, p = MvPolynomial.rename Fin.castSucc q := by
  constructor
  · intro h
    refine ⟨(towerEquiv R n p).coeff 0, ?_⟩
    apply (towerEquiv R n).injective
    rw [towerEquiv_rename_castSucc]
    exact Polynomial.eq_C_of_natDegree_eq_zero h
  · rintro ⟨q, rfl⟩
    rw [towerEquiv_rename_castSucc]
    exact Polynomial.natDegree_C q

variable [CommRing R] [Primcodable R] [ComputableRing R]

/-- The bundled tower package used to construct the `Primcodable` and
`ComputableRing` instances simultaneously, avoiding competing recursive
instances. -/
structure MvTowerPackage (n : ℕ) where
  /-- The canonical tower coding of `MvPolynomial (Fin n) R`. -/
  prim : Primcodable (MvPolynomial (Fin n) R)
  /-- Rabin admissibility for the canonical tower coding: computable `+` and
  `*` (Rabin 1960, §1.6, tex:264). -/
  ring : @ComputableRing (MvPolynomial (Fin n) R) _ prim
  /-- Constants from the coefficient ring are computable at this level. -/
  C_comp : @Computable R (MvPolynomial (Fin n) R) _ prim fun r => MvPolynomial.C r

/-- The canonical tower package for `MvPolynomial (Fin n) R`.  Rabin's
computable-ring content is only computability of addition and multiplication;
the iterated-polynomial tower is an admissible-indexing engineering choice. -/
def mvTower : (n : ℕ) → MvTowerPackage R n
  | 0 =>
      let eAlg : MvPolynomial (Fin 0) R ≃ₐ[R] R :=
        MvPolynomial.isEmptyAlgEquiv R (Fin 0)
      let e : MvPolynomial (Fin 0) R ≃+* R := eAlg.toRingEquiv
      letI : Primcodable (MvPolynomial (Fin 0) R) := primcodableOfRingEquiv e
      { prim := primcodableOfRingEquiv e
        ring :=
          { computable_add := computable₂_add_of_ringEquiv e
            computable_mul := computable₂_mul_of_ringEquiv e }
        C_comp :=
          computable_of_ringEquiv_codomain e Computable.id (fun r => by
            change eAlg (MvPolynomial.C r) = r
            rw [← MvPolynomial.isEmptyRingEquiv_symm_apply (R := R) (σ := Fin 0) r]
            exact (MvPolynomial.isEmptyRingEquiv R (Fin 0)).apply_symm_apply r) }
  | n + 1 =>
      let prev := mvTower n
      letI : Primcodable (MvPolynomial (Fin n) R) := prev.prim
      letI : ComputableRing (MvPolynomial (Fin n) R) := prev.ring
      letI : Primcodable (Polynomial (MvPolynomial (Fin n) R)) :=
        instPrimcodablePolynomial (R := MvPolynomial (Fin n) R)
      letI : ComputableRing (Polynomial (MvPolynomial (Fin n) R)) :=
        inferInstance
      let eAlg := towerEquiv R n
      let e : MvPolynomial (Fin (n + 1)) R ≃+* Polynomial (MvPolynomial (Fin n) R) :=
        eAlg.toRingEquiv
      letI : Primcodable (MvPolynomial (Fin (n + 1)) R) := primcodableOfRingEquiv e
      { prim := primcodableOfRingEquiv e
        ring :=
          { computable_add := computable₂_add_of_ringEquiv e
            computable_mul := computable₂_mul_of_ringEquiv e }
        C_comp :=
          computable_of_ringEquiv_codomain e
            (computable_poly_C.comp prev.C_comp) (fun r => by
              change towerEquiv R n (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r)
              simp [towerEquiv]) }

/-- Canonical `Primcodable` instance for finitely many multivariate polynomial
variables, using the last-variable iterated-polynomial tower. -/
instance instPrimcodableMvPolynomialFin (n : ℕ) :
    Primcodable (MvPolynomial (Fin n) R) :=
  (mvTower R n).prim

/-- Canonical computable-ring instance for finitely many multivariate polynomial
variables.  This formalizes Rabin §1.6 (tex:264) by providing computable
addition and multiplication for the tower coding. -/
instance instComputableRingMvPolynomialFin (n : ℕ) :
    ComputableRing (MvPolynomial (Fin n) R) :=
  (mvTower R n).ring

/-- Constants from the coefficient ring are computable in
`MvPolynomial (Fin n) R`. -/
theorem computable_mvPolynomial_C (n : ℕ) :
    Computable fun r : R => (MvPolynomial.C r : MvPolynomial (Fin n) R) :=
  (mvTower R n).C_comp

/-- For a fixed variable, `MvPolynomial.X i` is computable as a constant. -/
theorem computable_mvPolynomial_X_const {n : ℕ} (i : Fin n) :
    Computable fun _ : Unit => (MvPolynomial.X i : MvPolynomial (Fin n) R) :=
  Computable.const (MvPolynomial.X i)

/-- The variable map `i ↦ X i` is computable for finitely many variables. -/
theorem computable_mvPolynomial_X (n : ℕ) :
    Computable fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) R) :=
  computable_of_fin n fun i => MvPolynomial.X i

/-- The last-variable level inclusion
`MvPolynomial (Fin n) R → MvPolynomial (Fin (n+1)) R` is computable. -/
theorem computable_mvPolynomial_rename_castSucc (n : ℕ) :
    Computable fun p : MvPolynomial (Fin n) R =>
      (MvPolynomial.rename Fin.castSucc p : MvPolynomial (Fin (n + 1)) R) := by
  let prev := mvTower R n
  letI : Primcodable (MvPolynomial (Fin n) R) := prev.prim
  letI : ComputableRing (MvPolynomial (Fin n) R) := prev.ring
  let eAlg := towerEquiv R n
  let e : MvPolynomial (Fin (n + 1)) R ≃+* Polynomial (MvPolynomial (Fin n) R) :=
    eAlg.toRingEquiv
  change @Computable (MvPolynomial (Fin n) R) (MvPolynomial (Fin (n + 1)) R)
    prev.prim (primcodableOfRingEquiv e) fun p => MvPolynomial.rename Fin.castSucc p
  refine computable_of_ringEquiv_codomain e computable_poly_C (fun p => ?_)
  change towerEquiv R n (MvPolynomial.rename Fin.castSucc p) = Polynomial.C p
  rw [towerEquiv, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_rename]
  have hfun : (finSuccEquivLast ∘ (Fin.castSucc : Fin n → Fin (n + 1))) = some := by
    funext i
    exact finSuccEquivLast_castSucc i
  rw [hfun]
  exact optionEquivLeft_rename_some R p

/-- The forward last-variable tower map is computable for the chosen coding. -/
theorem computable_towerEquiv (n : ℕ) :
    Computable fun p : MvPolynomial (Fin (n + 1)) R => towerEquiv R n p := by
  let prev := mvTower R n
  letI : Primcodable (MvPolynomial (Fin n) R) := prev.prim
  letI : ComputableRing (MvPolynomial (Fin n) R) := prev.ring
  let eAlg := towerEquiv R n
  let e : MvPolynomial (Fin (n + 1)) R ≃+* Polynomial (MvPolynomial (Fin n) R) :=
    eAlg.toRingEquiv
  change @Computable (MvPolynomial (Fin (n + 1)) R)
    (Polynomial (MvPolynomial (Fin n) R)) (primcodableOfRingEquiv e) _ fun p => e p
  exact computable_ringEquiv_apply_of_transport e

/-- Lowering a level by taking the constant coefficient in the last variable is
computable. -/
theorem computable_mvPolynomial_level_lowering (n : ℕ) :
    Computable fun p : MvPolynomial (Fin (n + 1)) R =>
      Polynomial.coeff (towerEquiv R n p) 0 := by
  let prev := mvTower R n
  letI : Primcodable (MvPolynomial (Fin n) R) := prev.prim
  letI : ComputableRing (MvPolynomial (Fin n) R) := prev.ring
  exact (computable₂_poly_coeff.comp (computable_towerEquiv R n) (Computable.const 0))

/-- The level-membership test for the image of the inclusion
`Fin n → Fin (n+1)` is computable: it checks whether the last-variable degree is
zero. -/
theorem computable_mvPolynomial_level_membership (n : ℕ) :
    Computable fun p : MvPolynomial (Fin (n + 1)) R =>
      decide ((towerEquiv R n p).natDegree = 0) := by
  let prev := mvTower R n
  letI : Primcodable (MvPolynomial (Fin n) R) := prev.prim
  letI : ComputableRing (MvPolynomial (Fin n) R) := prev.ring
  have hdeg : Computable fun p : MvPolynomial (Fin (n + 1)) R =>
      (towerEquiv R n p).natDegree :=
    computable_poly_natDegree.comp (computable_towerEquiv R n)
  exact (Primrec.eq.decide.to_comp.comp hdeg (Computable.const 0)).of_eq fun _ => rfl

/-- Scalar coefficient maps of finitely many multivariate polynomials are
computable for computable ring homomorphisms.  This is part of Rabin's
computable ring-operation infrastructure (Rabin 1960, §1.6, tex:264). -/
theorem computable_mvPolynomial_map {S : Type u} [CommRing S] [Primcodable S]
    [ComputableRing S] (n : ℕ) (f : R →+* S) (hf : Computable f) :
    Computable fun p : MvPolynomial (Fin n) R => MvPolynomial.map f p := by
  induction n with
  | zero =>
      let eRAlg : MvPolynomial (Fin 0) R ≃ₐ[R] R :=
        MvPolynomial.isEmptyAlgEquiv R (Fin 0)
      let eR : MvPolynomial (Fin 0) R ≃+* R := eRAlg.toRingEquiv
      let eSAlg : MvPolynomial (Fin 0) S ≃ₐ[S] S :=
        MvPolynomial.isEmptyAlgEquiv S (Fin 0)
      let eS : MvPolynomial (Fin 0) S ≃+* S := eSAlg.toRingEquiv
      change @Computable (MvPolynomial (Fin 0) R) (MvPolynomial (Fin 0) S)
        (primcodableOfRingEquiv eR) (primcodableOfRingEquiv eS)
        fun p => MvPolynomial.map f p
      have heR : Computable (eR : MvPolynomial (Fin 0) R → R) :=
        computable_ringEquiv_apply_of_transport eR
      refine computable_of_ringEquiv_codomain eS (hf.comp heR) (fun p => ?_)
      change eSAlg (MvPolynomial.map f p) = f (eRAlg p)
      induction p using MvPolynomial.induction_on with
      | C r =>
          simp [eRAlg, eSAlg]
      | add p q hp hq =>
          simp [map_add, hp, hq]
      | mul_X p i hp =>
          exact Fin.elim0 i
  | succ n ih =>
      let prevR := mvTower R n
      letI : Primcodable (MvPolynomial (Fin n) R) := prevR.prim
      letI : ComputableRing (MvPolynomial (Fin n) R) := prevR.ring
      let prevS := mvTower S n
      letI : Primcodable (MvPolynomial (Fin n) S) := prevS.prim
      letI : ComputableRing (MvPolynomial (Fin n) S) := prevS.ring
      let eRAlg := towerEquiv R n
      let eR : MvPolynomial (Fin (n + 1)) R ≃+* Polynomial (MvPolynomial (Fin n) R) :=
        eRAlg.toRingEquiv
      let eSAlg := towerEquiv S n
      let eS : MvPolynomial (Fin (n + 1)) S ≃+* Polynomial (MvPolynomial (Fin n) S) :=
        eSAlg.toRingEquiv
      change @Computable (MvPolynomial (Fin (n + 1)) R) (MvPolynomial (Fin (n + 1)) S)
        (primcodableOfRingEquiv eR) (primcodableOfRingEquiv eS)
        fun p => MvPolynomial.map f p
      have hpoly : Computable fun p : MvPolynomial (Fin (n + 1)) R =>
          Polynomial.map (MvPolynomial.map f) (towerEquiv R n p) :=
        (computable_poly_map (R := MvPolynomial (Fin n) R)
          (S := MvPolynomial (Fin n) S) (MvPolynomial.map f) ih).comp
            (computable_towerEquiv R n)
      refine computable_of_ringEquiv_codomain eS hpoly (fun p => ?_)
      exact towerEquiv_map R n f p

/-- Multivariate polynomial evaluation at a list-coded point is computable.
The list `xs` is read as `i ↦ xs.getD i 0`.  This is the workhorse used by
Rabin's Lemma 5 zero tests (Rabin 1960, Lemma 5, tex:336-351). -/
theorem computable₂_mvPolynomial_eval (n : ℕ) :
    Computable₂ fun (xs : List R) (p : MvPolynomial (Fin n) R) =>
      MvPolynomial.eval (fun i : Fin n => xs.getD i 0) p := by
  induction n with
  | zero =>
      let eAlg : MvPolynomial (Fin 0) R ≃ₐ[R] R :=
        MvPolynomial.isEmptyAlgEquiv R (Fin 0)
      let e : MvPolynomial (Fin 0) R ≃+* R := eAlg.toRingEquiv
      change @Computable₂ (List R) (MvPolynomial (Fin 0) R) R _ (primcodableOfRingEquiv e) _
        fun xs p => MvPolynomial.eval (fun i : Fin 0 => xs.getD i 0) p
      have he : Computable (e : MvPolynomial (Fin 0) R → R) :=
        computable_ringEquiv_apply_of_transport e
      have h : Computable fun x : List R × MvPolynomial (Fin 0) R => e x.2 :=
        he.comp Computable.snd
      exact h.to₂.of_eq fun x => by
        rcases x with ⟨xs, p⟩
        change eAlg p = MvPolynomial.eval (fun i : Fin 0 => xs.getD i 0) p
        apply congr_arg (fun y => MvPolynomial.eval y p)
        funext i
        exact Fin.elim0 i
  | succ n ih =>
      let prev := mvTower R n
      letI : Primcodable (MvPolynomial (Fin n) R) := prev.prim
      letI : ComputableRing (MvPolynomial (Fin n) R) := prev.ring
      let eAlg := towerEquiv R n
      let e : MvPolynomial (Fin (n + 1)) R ≃+* Polynomial (MvPolynomial (Fin n) R) :=
        eAlg.toRingEquiv
      change @Computable₂ (List R) (MvPolynomial (Fin (n + 1)) R) R _ (primcodableOfRingEquiv e) _
        fun xs p => MvPolynomial.eval (fun i : Fin (n + 1) => xs.getD i 0) p
      let evalHom : List R → MvPolynomial (Fin n) R →+* R :=
        fun xs => MvPolynomial.eval fun i : Fin n => xs.getD i 0
      have hmap : Computable₂ fun (xs : List R) (q : Polynomial (MvPolynomial (Fin n) R)) =>
          Polynomial.map (evalHom xs) q :=
        computable₂_poly_map_param (R := MvPolynomial (Fin n) R)
          (Γ := List R) (S := R) evalHom ih
      have hlast : Computable fun x : List R × MvPolynomial (Fin (n + 1)) R =>
          x.1.getD n 0 :=
        (Primrec.list_getD (α := R) 0).to_comp.comp Computable.fst (Computable.const n)
      have htower : Computable fun x : List R × MvPolynomial (Fin (n + 1)) R =>
          towerEquiv R n x.2 :=
        (computable_towerEquiv R n).comp Computable.snd
      have hmapped : Computable fun x : List R × MvPolynomial (Fin (n + 1)) R =>
          Polynomial.map (evalHom x.1) (towerEquiv R n x.2) :=
        hmap.comp Computable.fst htower
      have h : Computable fun x : List R × MvPolynomial (Fin (n + 1)) R =>
          Polynomial.eval (x.1.getD n 0)
            (Polynomial.map (evalHom x.1) (towerEquiv R n x.2)) :=
        computable₂_poly_eval.comp hlast hmapped
      have htarget : Computable fun x : List R × MvPolynomial (Fin (n + 1)) R =>
          MvPolynomial.eval (fun i : Fin (n + 1) => x.1.getD i 0) x.2 :=
        h.of_eq fun x => by
        rcases x with ⟨xs, p⟩
        rw [mvPolynomial_eval_towerEquiv R n (fun i : Fin (n + 1) => xs.getD i 0) p]
        rfl
      exact htarget.to₂

end Tower

section Examples

/-- Example: addition of three-variable rational multivariate polynomials is
computable. -/
example : Computable₂
    ((· + ·) : MvPolynomial (Fin 3) ℚ → MvPolynomial (Fin 3) ℚ →
      MvPolynomial (Fin 3) ℚ) :=
  ComputableRing.computable_add

/-- Example: multiplication of three-variable rational multivariate polynomials
is computable. -/
example : Computable₂
    ((· * ·) : MvPolynomial (Fin 3) ℚ → MvPolynomial (Fin 3) ℚ →
      MvPolynomial (Fin 3) ℚ) :=
  ComputableRing.computable_mul

/-- Example: the level inclusion is computable over any computable ring. -/
example [CommRing R] [Primcodable R] [ComputableRing R] (n : ℕ) :
    Computable fun p : MvPolynomial (Fin n) R =>
      (MvPolynomial.rename Fin.castSucc p : MvPolynomial (Fin (n + 1)) R) :=
  computable_mvPolynomial_rename_castSucc R n

/-- Example: evaluating a two-variable rational multivariate polynomial at a
list-coded point is computable. -/
example : Computable₂ fun (xs : List ℚ) (p : MvPolynomial (Fin 2) ℚ) =>
    MvPolynomial.eval (fun i : Fin 2 => xs.getD i 0) p :=
  computable₂_mvPolynomial_eval ℚ 2

/-- Example: scalar coefficient maps on two-variable rational multivariate
polynomials are computable. -/
example : Computable fun p : MvPolynomial (Fin 2) ℚ =>
    MvPolynomial.map (RingHom.id ℚ) p :=
  computable_mvPolynomial_map ℚ 2 (RingHom.id ℚ) Computable.id

/-- Example: finite sums and products of rational elements are computable. -/
example : (Computable fun l : List ℚ => l.sum) ∧ (Computable fun l : List ℚ => l.prod) :=
  ⟨computable_list_sum, computable_list_prod⟩

end Examples

end Semicontinuity
