/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.Algorithm
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.CheckerComputable
import AsymptoticTensorRankSemicontinuity.Prerequisites.Matrix.SubmatrixDet
import Mathlib.Data.List.GetD

/-!
# Theorem 1.1: deciding `asympRank T ≤ r`, uniformly in the format

**Theorem 1.1** of *Asymptotic tensor rank is characterized by polynomials*
(arXiv:2411.15789, tex:296-298): for a computable field `F` and fixed `r`,
there is an algorithm that, **given the format `d` and a `k`-tensor
`T ∈ F^{d₁} ⊗ ⋯ ⊗ F^{d_k}`**, decides whether `asympRank T ≤ r`. The
algorithm is not uniform in `r` but is uniform in the dimensions `d`.

Following the paper's proof (tex:313-318):

* finitely many polynomials cut out the sublevel set on the
  `⌊r⌋ × ⋯ × ⌊r⌋` cube format (`exists_finset_entryPolynomials_asympRank_le`
  from the fixed-format file); they are constants of the algorithm;
* on input `(d, T)` the algorithm determines whether the flattening ranks
  of `T` are at most `⌊r⌋` — they are lower bounds on the asymptotic rank
  (`flatRank_le_asympRank`), so if not, `asympRank T > r`;
* otherwise it computes an embedding `S` of `T` into the cube format and
  evaluates the fixed polynomials on `S`.

The two computations in the last two steps are realized by an unbounded
search (`Nat.rfindOpt`) over coded candidate witnesses: either per-leg
matrices witnessing a mutual restriction `S ∼ T` with `S` on the cube format
(`restrictsCheckList`), or a nonzero `(⌊r⌋+1)`-minor of a flattening
witnessing `flatRank T {j} > ⌊r⌋` (`minorCheckList`). The search always
terminates: a tensor with all flattening ranks `≤ ⌊r⌋` is equivalent to a
tensor on the cube format (`exists_concise_restriction` + re-embedding), and
a flattening of rank `> ⌊r⌋` has a nonzero `(⌊r⌋+1)`-minor
(`exists_submatrix_det_ne_zero_of_le_rank`).
-/

universe u

namespace Semicontinuity

open scoped TensorProduct

variable {F : Type u} [Field F]

/-! ## Coding tensors of arbitrary format

A `k`-tensor of arbitrary format is coded by the pair (format, entry list),
with the entries listed in the little-endian mixed-radix order of
`finPiFinEquiv`. -/

section Coding

variable {k : ℕ}

private lemma primrec_pnat_val : Primrec fun n : ℕ+ => (n : ℕ) :=
  Primrec.encode_iff.mp (Primrec.encode.of_eq fun _ => rfl)

/-- The entries of a `k`-tensor, listed in the little-endian mixed-radix
order of `finPiFinEquiv`. -/
def entriesList {d : Fin k → ℕ+} (T : KTensor F d) : List F :=
  List.ofFn fun p : Fin (∏ i, ((d i : ℕ))) => T (finPiFinEquiv.symm p)

/-- The dimension list of a format. -/
def formatList (d : Fin k → ℕ+) : List ℕ :=
  List.ofFn fun i => ((d i : ℕ))

@[simp] lemma entriesList_length {d : Fin k → ℕ+} (T : KTensor F d) :
    (entriesList T).length = ∏ i, ((d i : ℕ)) := by
  simp [entriesList]

@[simp] lemma formatList_length (d : Fin k → ℕ+) :
    (formatList d).length = k := by
  simp [formatList]

lemma formatList_getD (d : Fin k → ℕ+) (i : Fin k) :
    (formatList d).getD (i : ℕ) 1 = (d i : ℕ) := by
  rw [List.getD_eq_getElem _ _ (by simp [formatList])]
  simp [formatList]

/-- Reading the coded entry at the position of a multi-index returns the
entry of the tensor at that multi-index. -/
lemma entriesList_getD {d : Fin k → ℕ+} (T : KTensor F d)
    (idx : ∀ i : Fin k, Fin (d i)) :
    (entriesList T).getD ((finPiFinEquiv idx : Fin _) : ℕ) 0 = T idx := by
  rw [List.getD_eq_getElem _ _ (by simp [entriesList])]
  simp only [entriesList, List.getElem_ofFn]
  congr 1
  rw [show (⟨((finPiFinEquiv idx : Fin _) : ℕ), _⟩ : Fin (∏ i, ((d i : ℕ))))
      = finPiFinEquiv idx from Fin.ext rfl]
  exact finPiFinEquiv.symm_apply_apply idx

/-- The initial segment of a dimension list. -/
lemma formatList_take (d : Fin k → ℕ+) (i : Fin k) :
    (formatList d).take (i : ℕ)
      = List.ofFn fun j : Fin (i : ℕ) => (d (Fin.castLE i.isLt.le j) : ℕ) := by
  apply List.ext_getElem (by simp [formatList])
  intro n h1 h2
  simp [formatList, List.getElem_take]

/-- `radixDigit` inverts `finPiFinEquiv`: the `i`-th digit of the position
of a multi-index is its `i`-th coordinate. -/
lemma radixDigit_finPiFinEquiv {d : Fin k → ℕ+}
    (idx : ∀ i : Fin k, Fin (d i)) (i : Fin k) :
    radixDigit (formatList d) (i : ℕ) ((finPiFinEquiv idx : Fin _) : ℕ)
      = (idx i : ℕ) := by
  have h := congrArg (fun f : ∀ i : Fin k, Fin ((d i : ℕ)) => ((f i) : ℕ))
    (finPiFinEquiv.symm_apply_apply idx)
  rw [radixDigit, formatList_getD, formatList_take, List.prod_ofFn]
  simpa [finPiFinEquiv, Equiv.ofRightInverseOfCardLE] using h

/-- A `k`-tensor of arbitrary format: the input data of the algorithm of
Theorem 1.1 (tex:297: "given `d ∈ ℤ^k_{≥1}` and any `k`-tensor
`T ∈ F^{d₁} ⊗ ⋯ ⊗ F^{d_k}`"). -/
abbrev FormatTensor (F : Type u) [Field F] (k : ℕ) :=
  Σ d : Fin k → ℕ+, KTensor F d

/-- Tensors of arbitrary format are coded by the pair (format, entry list);
the entry list has length `∏ i, d i`. -/
def formatTensorEquiv (F : Type u) [Field F] (k : ℕ) :
    FormatTensor F k ≃
      {p : (Fin k → ℕ+) × List F // p.2.length = ∏ i, ((p.1 i : ℕ))} where
  toFun x := ⟨(x.1, entriesList x.2), entriesList_length x.2⟩
  invFun p := ⟨p.1.1, fun idx => p.1.2.getD ((finPiFinEquiv idx : Fin _) : ℕ) 0⟩
  left_inv x := by
    obtain ⟨d, T⟩ := x
    exact Sigma.ext rfl (heq_of_eq (funext fun idx => entriesList_getD T idx))
  right_inv p := by
    obtain ⟨⟨d, l⟩, hl⟩ := p
    apply Subtype.ext
    refine Prod.ext rfl ?_
    apply List.ext_getElem (by simpa using hl.symm)
    intro n h1 h2
    simp only [entriesList, List.getElem_ofFn]
    rw [Equiv.apply_symm_apply]
    exact List.getD_eq_getElem l 0 h2

omit [Field F] in
private lemma primrecPred_formatTensor_lengthEq [Primcodable F] :
    PrimrecPred fun p : (Fin k → ℕ+) × List F =>
      p.2.length = ∏ i, ((p.1 i : ℕ)) := by
  have hofn : Primrec fun p : (Fin k → ℕ+) × List F =>
      List.ofFn fun i => ((p.1 i : ℕ)) :=
    Primrec.list_ofFn fun i =>
      primrec_pnat_val.comp (Primrec.fin_app.comp Primrec.fst (Primrec.const i))
  have hprodlist : Primrec (List.prod : List ℕ → ℕ) := by
    have := Primrec.list_foldl (Primrec.id (α := List ℕ))
      (Primrec.const (1 : ℕ))
      ((Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂)
    exact this.of_eq fun l => (List.prod_eq_foldl (l := l)).symm
  have hprod : Primrec fun p : (Fin k → ℕ+) × List F => ∏ i, ((p.1 i : ℕ)) :=
    (hprodlist.comp hofn).of_eq fun p => by simp [List.prod_ofFn]
  exact PrimrecRel.comp Primrec.eq (Primrec.list_length.comp Primrec.snd) hprod

variable [Primcodable F]

/-- Tensors of arbitrary format are coded via `formatTensorEquiv`. -/
noncomputable instance instPrimcodableFormatTensor :
    Primcodable (FormatTensor F k) :=
  haveI : Primcodable
      {p : (Fin k → ℕ+) × List F // p.2.length = ∏ i, ((p.1 i : ℕ))} :=
    Primcodable.subtype primrecPred_formatTensor_lengthEq
  Primcodable.ofEquiv _ (formatTensorEquiv F k)

/-- Reading off the coded data (format, entry list) is computable: the coding
of a `FormatTensor` is by definition the coding of this pair. -/
theorem computable_formatTensor_data :
    Computable fun x : FormatTensor F k =>
      ((formatTensorEquiv F k x : (Fin k → ℕ+) × List F)) :=
  Computable.encode_iff.mp (Computable.encode.of_eq fun _ => rfl)

/-- The entry list of the input tensor is computable from the input. -/
theorem computable_entriesList :
    Computable fun x : FormatTensor F k => entriesList x.2 :=
  (Computable.snd.comp computable_formatTensor_data).of_eq fun _ => rfl

/-- The dimension list of the input tensor is computable from the input. -/
theorem computable_formatList :
    Computable fun x : FormatTensor F k => formatList x.1 := by
  have h1 : Computable fun x : FormatTensor F k => x.1 :=
    (Computable.fst.comp computable_formatTensor_data).of_eq fun _ => rfl
  exact (Computable.list_ofFn fun i =>
    PNat.computable_val.comp (Computable.fin_app.comp h1 (Computable.const i))).of_eq
    fun x => rfl

end Coding

/-! ## Bridging the list-level restriction check to `Restricts` -/

section Bridge

variable {k : ℕ}

private lemma list_sum_map_range {M : Type*} [AddCommMonoid M]
    (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ p ∈ Finset.range n, f p := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append,
        Finset.sum_range_succ, ih]
      simp

private lemma list_prod_map_range {M : Type*} [CommMonoid M]
    (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).prod = ∏ p ∈ Finset.range n, f p := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.prod_append,
        Finset.prod_range_succ, ih]
      simp

/-- Decoding a list of per-leg matrices: the leg-`i` matrix has entry
`(a, b)` at position `a * dT i + b` of `A.getD i []` (row-major). -/
def matsOfList (dS dT : Fin k → ℕ+) (A : List (List F)) :
    ∀ i : Fin k, Matrix (Fin (dS i)) (Fin (dT i)) F :=
  fun i => Matrix.of fun a b =>
    (A.getD (i : ℕ) []).getD ((a : ℕ) * (dT i : ℕ) + (b : ℕ)) 0

/-- The list-level restriction check accepts iff the decoded per-leg matrices
satisfy the defining equation of `Restricts`. -/
lemma restrictsCheckList_eq_true_iff {dS dT : Fin k → ℕ+}
    (S : KTensor F dS) (T : KTensor F dT) (A : List (List F)) :
    restrictsCheckList k (formatList dS) (formatList dT)
        (entriesList S) (entriesList T) A = true ↔
      ∀ jdx : ∀ i : Fin k, Fin (dS i), S jdx =
        ∑ idx : ∀ i : Fin k, Fin (dT i),
          (∏ i, matsOfList dS dT A i (jdx i) (idx i)) * T idx := by
  classical
  have key : ∀ (jdx : ∀ i : Fin k, Fin (dS i)),
      (((List.range (entriesList T).length).map fun q =>
        ((List.range k).map fun i =>
          (A.getD i []).getD
            (radixDigit (formatList dS) i ((finPiFinEquiv jdx : Fin _) : ℕ)
                * (formatList dT).getD i 1
              + radixDigit (formatList dT) i q) 0).prod
        * (entriesList T).getD q 0).sum)
      = ∑ idx : ∀ i : Fin k, Fin (dT i),
          (∏ i, matsOfList dS dT A i (jdx i) (idx i)) * T idx := by
    intro jdx
    rw [entriesList_length, list_sum_map_range, ← Fin.sum_univ_eq_sum_range,
      ← Equiv.sum_comp finPiFinEquiv]
    refine Finset.sum_congr rfl fun idx _ => ?_
    rw [list_prod_map_range, ← Fin.prod_univ_eq_prod_range, entriesList_getD]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [radixDigit_finPiFinEquiv, radixDigit_finPiFinEquiv, formatList_getD]
    rfl
  rw [restrictsCheckList, List.all_eq_true]
  constructor
  · intro h jdx
    have hp := h ((finPiFinEquiv jdx : Fin _) : ℕ)
      (by rw [List.mem_range, entriesList_length]; exact (finPiFinEquiv jdx).isLt)
    rw [decide_eq_true_eq, entriesList_getD, key jdx] at hp
    exact hp
  · intro h p hp
    rw [List.mem_range, entriesList_length] at hp
    have hcoe : p = ((finPiFinEquiv (finPiFinEquiv.symm ⟨p, hp⟩) : Fin _) : ℕ) := by
      simp
    rw [decide_eq_true_eq, hcoe, entriesList_getD,
      key (finPiFinEquiv.symm ⟨p, hp⟩)]
    exact h (finPiFinEquiv.symm ⟨p, hp⟩)

/-- **Soundness** of the restriction check: an accepted check yields a
restriction (via the decoded matrices). -/
lemma restricts_of_restrictsCheckList {dS dT : Fin k → ℕ+}
    {S : KTensor F dS} {T : KTensor F dT} {A : List (List F)}
    (h : restrictsCheckList k (formatList dS) (formatList dT)
      (entriesList S) (entriesList T) A = true) :
    Restricts S T :=
  ⟨matsOfList dS dT A, (restrictsCheckList_eq_true_iff S T A).mp h⟩

/-- Row-major coding of per-leg matrices (a right inverse of `matsOfList`). -/
def matsToList {dS dT : Fin k → ℕ+}
    (A : ∀ i : Fin k, Matrix (Fin (dS i)) (Fin (dT i)) F) : List (List F) :=
  List.ofFn fun i : Fin k =>
    List.ofFn fun x : Fin ((dS i : ℕ) * (dT i : ℕ)) =>
      A i ⟨(x : ℕ) / (dT i : ℕ), (Nat.div_lt_iff_lt_mul (dT i).2).mpr x.isLt⟩
        ⟨(x : ℕ) % (dT i : ℕ), Nat.mod_lt _ (dT i).2⟩

lemma matsOfList_matsToList {dS dT : Fin k → ℕ+}
    (A : ∀ i : Fin k, Matrix (Fin (dS i)) (Fin (dT i)) F) (i : Fin k)
    (a : Fin (dS i)) (b : Fin (dT i)) :
    matsOfList dS dT (matsToList A) i a b = A i a b := by
  have hx : (a : ℕ) * (dT i : ℕ) + (b : ℕ) < (dS i : ℕ) * (dT i : ℕ) := by
    calc (a : ℕ) * (dT i : ℕ) + (b : ℕ)
        < (a : ℕ) * (dT i : ℕ) + (dT i : ℕ) := by
          exact Nat.add_lt_add_left b.isLt _
      _ = ((a : ℕ) + 1) * (dT i : ℕ) := by ring
      _ ≤ (dS i : ℕ) * (dT i : ℕ) :=
          Nat.mul_le_mul_right _ (Nat.succ_le_of_lt a.isLt)
  change (((matsToList A).getD (i : ℕ) []).getD
    ((a : ℕ) * (dT i : ℕ) + (b : ℕ)) 0) = A i a b
  have houter : (matsToList A).getD (i : ℕ) []
      = (matsToList A)[(i : ℕ)]'(by simp [matsToList]) :=
    List.getD_eq_getElem _ _ (by simp [matsToList])
  rw [houter]
  simp only [matsToList, List.getElem_ofFn, Fin.eta]
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hx),
    List.getElem_ofFn]
  have hdiv : ((a : ℕ) * (dT i : ℕ) + (b : ℕ)) / (dT i : ℕ) = (a : ℕ) := by
    have h1 : ((a : ℕ) + 1) * (dT i : ℕ)
        = (a : ℕ) * (dT i : ℕ) + (dT i : ℕ) := by ring
    have h2 : (b : ℕ) < (dT i : ℕ) := b.isLt
    exact Nat.div_eq_of_lt_le (Nat.le_add_right _ _) (by rw [h1]; omega)
  have hmod : ((a : ℕ) * (dT i : ℕ) + (b : ℕ)) % (dT i : ℕ) = (b : ℕ) := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt b.isLt]
  have happ : ∀ (x : Fin (dS i)) (y : Fin (dT i)),
      x = a → y = b → A i x y = A i a b := by
    rintro x y rfl rfl; rfl
  exact happ _ _ (Fin.ext hdiv) (Fin.ext hmod)

/-- **Completeness** of the restriction check: a restriction yields an
accepted check (code the witnessing matrices row-major). -/
lemma exists_restrictsCheckList_of_restricts {dS dT : Fin k → ℕ+}
    {S : KTensor F dS} {T : KTensor F dT} (h : Restricts S T) :
    ∃ A : List (List F),
      restrictsCheckList k (formatList dS) (formatList dT)
        (entriesList S) (entriesList T) A = true := by
  obtain ⟨A, hA⟩ := h
  refine ⟨matsToList A, (restrictsCheckList_eq_true_iff S T _).mpr fun jdx => ?_⟩
  rw [hA jdx]
  refine Finset.sum_congr rfl fun idx _ => ?_
  congr 1
  exact Finset.prod_congr rfl fun i _ => (matsOfList_matsToList A i _ _).symm

end Bridge

/-! ## Bridging the list-level minor check to flattening ranks -/

section MinorBridge

variable {k : ℕ}

private lemma getD_ofFn_lt {β : Type*} {n : ℕ} (f : Fin n → β) (b : β)
    {x : ℕ} (hx : x < n) :
    (List.ofFn f).getD x b = f ⟨x, hx⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hx), List.getElem_ofFn]

/-- `posWithLeg` computes the `finPiFinEquiv` position of the multi-index it
describes. -/
lemma posWithLeg_eq_finPiFinEquiv {d : Fin k → ℕ+}
    (idx : ∀ i : Fin k, Fin (d i)) (j rv : ℕ) (col : List ℕ)
    (hval : ∀ i : Fin k,
      (if (i : ℕ) = j then rv else col.getD (i : ℕ) 0) = (idx i : ℕ)) :
    posWithLeg (formatList d) j rv col
      = ((finPiFinEquiv idx : Fin _) : ℕ) := by
  rw [posWithLeg, formatList_length, list_sum_map_range, finPiFinEquiv_apply,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hval i, formatList_take, List.prod_ofFn]

/-- The assembled minor matrix equals the submatrix of the `{jF}`-flattening
selected by typed rows `f` and columns `g`, whenever the lists code the
values of `f` and `g`. -/
lemma minorMatrixOfLists_eq_submatrix {d : Fin k → ℕ+} (T : KTensor F d)
    (jF : Fin k) {s : ℕ} (rows : List ℕ) (cols : List (List ℕ))
    (f : Fin s → ∀ i : {i : Fin k // i ∈ ({jF} : Finset (Fin k))}, Fin (d i.val))
    (g : Fin s → ∀ i : {i : Fin k // i ∉ ({jF} : Finset (Fin k))}, Fin (d i.val))
    (hf : ∀ a : Fin s, rows.getD (a : ℕ) 0
      = ((f a ⟨jF, Finset.mem_singleton_self jF⟩ : Fin (d jF)) : ℕ))
    (hg : ∀ (b : Fin s) (i : Fin k) (h : i ∉ ({jF} : Finset (Fin k))),
      (cols.getD (b : ℕ) []).getD (i : ℕ) 0 = ((g b ⟨i, h⟩ : Fin (d i)) : ℕ)) :
    minorMatrixOfLists s (formatList d) (entriesList T) (jF : ℕ) rows cols
      = (flattenMatrix T {jF}).submatrix f g := by
  classical
  ext a b
  set idx₀ : ∀ i : Fin k, Fin (d i) := fun i =>
    if h : i ∈ ({jF} : Finset (Fin k)) then f a ⟨i, h⟩ else g b ⟨i, h⟩
    with hidx₀
  have hpos : posWithLeg (formatList d) (jF : ℕ) (rows.getD (a : ℕ) 0)
      (cols.getD (b : ℕ) []) = ((finPiFinEquiv idx₀ : Fin _) : ℕ) := by
    refine posWithLeg_eq_finPiFinEquiv idx₀ _ _ _ fun i => ?_
    by_cases hij : (i : ℕ) = (jF : ℕ)
    · have hijF : i = jF := Fin.ext hij
      subst hijF
      rw [if_pos rfl, hf a, hidx₀]
      simp
    · have hmem : i ∉ ({jF} : Finset (Fin k)) := by
        rw [Finset.mem_singleton]
        exact fun hcon => hij (by rw [hcon])
      rw [if_neg hij, hg b i hmem, hidx₀]
      simp [hmem]
  change (entriesList T).getD
      (posWithLeg (formatList d) (jF : ℕ) (rows.getD (a : ℕ) 0)
        (cols.getD (b : ℕ) [])) 0
    = flattenMatrix T {jF} (f a) (g b)
  rw [hpos, entriesList_getD]
  rfl

/-- **Soundness** of the minor check: an accepted check exhibits a flattening
of rank `≥ s`. -/
lemma exists_le_flatRank_of_minorCheckList {d : Fin k → ℕ+} {T : KTensor F d}
    {s : ℕ} {j : ℕ} {rows : List ℕ} {cols : List (List ℕ)}
    (h : minorCheckList k s (formatList d) (entriesList T) j rows cols
      = true) :
    ∃ jF : Fin k, s ≤ flatRank T {jF} := by
  classical
  rw [minorCheckList] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨hj, hrows⟩, hcols⟩, hdet⟩ := h
  set jF : Fin k := ⟨j, hj⟩ with hjF
  refine ⟨jF, ?_⟩
  set f : Fin s → (∀ i : {i : Fin k // i ∈ ({jF} : Finset (Fin k))},
      Fin (d i.val)) :=
    fun a x => ⟨rows.getD (a : ℕ) 0, by
      have hx : x.val = jF := Finset.mem_singleton.mp x.2
      have hb := hrows (a : ℕ) a.isLt
      rw [show j = (jF : ℕ) from rfl, formatList_getD d jF] at hb
      rw [hx]
      exact hb⟩ with hfdef
  set g : Fin s → (∀ i : {i : Fin k // i ∉ ({jF} : Finset (Fin k))},
      Fin (d i.val)) :=
    fun b x => ⟨(cols.getD (b : ℕ) []).getD ((x.val : ℕ)) 0, by
      have hb := hcols (b : ℕ) b.isLt (x.val : ℕ) x.val.isLt
      rw [formatList_getD d x.val] at hb
      exact hb⟩ with hgdef
  have heq := minorMatrixOfLists_eq_submatrix T jF rows cols f g
    (fun a => rfl) (fun b i hmem => rfl)
  rw [show j = (jF : ℕ) from rfl, heq] at hdet
  have hunit : IsUnit ((flattenMatrix T {jF}).submatrix f g) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  calc s = ((flattenMatrix T {jF}).submatrix f g).rank := by
        rw [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin]
    _ ≤ (flattenMatrix T {jF}).rank := Matrix.rank_submatrix_le' _ f g
    _ = flatRank T {jF} := (flatRank_eq_rank T {jF}).symm

/-- **Completeness** of the minor check: a flattening of rank `> s'` yields
an accepted minor check with minors of size `s' + 1`. -/
lemma exists_minorCheckList_of_lt_flatRank {d : Fin k → ℕ+} (T : KTensor F d)
    (jF : Fin k) {s' : ℕ} (h : s' + 1 ≤ flatRank T {jF}) :
    ∃ (rows : List ℕ) (cols : List (List ℕ)),
      minorCheckList k (s' + 1) (formatList d) (entriesList T) (jF : ℕ)
        rows cols = true := by
  classical
  rw [flatRank_eq_rank] at h
  obtain ⟨fE, gE, hdet⟩ := Matrix.exists_submatrix_det_ne_zero_of_le_rank
    (flattenMatrix T {jF}) s' h
  set rows : List ℕ := List.ofFn fun a : Fin (s' + 1) =>
    ((fE a ⟨jF, Finset.mem_singleton_self jF⟩ : Fin (d jF)) : ℕ) with hrowsdef
  set cols : List (List ℕ) := List.ofFn fun b : Fin (s' + 1) =>
    List.ofFn fun i : Fin k =>
      if h : i ∉ ({jF} : Finset (Fin k)) then ((gE b ⟨i, h⟩ : Fin (d i)) : ℕ)
      else 0 with hcolsdef
  refine ⟨rows, cols, ?_⟩
  have heq := minorMatrixOfLists_eq_submatrix T jF rows cols (⇑fE) (⇑gE)
    (fun a => by rw [hrowsdef, getD_ofFn_lt _ _ a.isLt])
    (fun b i hmem => by
      rw [hcolsdef, getD_ofFn_lt _ _ b.isLt, getD_ofFn_lt _ _ i.isLt,
        dif_pos hmem])
  rw [minorCheckList]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range]
  refine ⟨⟨⟨jF.isLt, fun a ha => ?_⟩, fun b hb i hi => ?_⟩, ?_⟩
  · rw [hrowsdef, getD_ofFn_lt _ _ ha, formatList_getD d jF]
    exact (fE ⟨a, ha⟩ ⟨jF, Finset.mem_singleton_self jF⟩).isLt
  · rw [hcolsdef, getD_ofFn_lt _ _ hb, getD_ofFn_lt _ _ hi,
      formatList_getD d ⟨i, hi⟩]
    by_cases hmem : (⟨i, hi⟩ : Fin k) ∉ ({jF} : Finset (Fin k))
    · rw [dif_pos hmem]
      exact (gE ⟨b, hb⟩ ⟨⟨i, hi⟩, hmem⟩).isLt
    · rw [dif_neg hmem]
      exact (d ⟨i, hi⟩).2
  · rw [heq]
    exact hdet

end MinorBridge

/-! ## Compression into the cube format -/

section Compression

variable {k : ℕ}

/-- The zero tensor of any format restricts to the zero tensor of any other
format (use the zero matrices). -/
lemma restricts_zero_zero {dS dT : Fin k → ℕ+} :
    Restricts (0 : KTensor F dS) (0 : KTensor F dT) :=
  ⟨fun _ => 0, fun jdx => by simp⟩

/-- **Compression** (tex:316-317): a tensor with all flattening ranks `≤ mw`
is equivalent (mutual restriction) to a tensor on the `mw`-cube format. Pass
to a concise equivalent (`exists_concise_restriction`), whose format is then
componentwise `≤ mw`, and re-embed into the cube. -/
lemma exists_cube_equiv_of_flatRank_le {d : Fin k → ℕ+} (T : KTensor F d)
    (mw : ℕ+) (hT : ∀ j, flatRank T {j} ≤ (mw : ℕ)) :
    ∃ S : KTensor F (fun _ : Fin k => mw), Restricts S T ∧ Restricts T S := by
  classical
  by_cases hzero : T = 0
  · subst hzero
    exact ⟨0, restricts_zero_zero, restricts_zero_zero⟩
  · obtain ⟨d', T', hT'T, hTT', hflat⟩ := exists_concise_restriction T hzero
    have hle : ∀ j, (d' j : ℕ) ≤ (((fun _ : Fin k => mw) j : ℕ+) : ℕ) :=
      fun j => by
        rw [hflat j]
        exact le_trans (Restricts.flatRank_le hT'T {j}) (hT j)
    exact ⟨reembed hle T',
      (restricts_reembed hle T').trans hT'T,
      hTT'.trans (reembed_restricts_to hle T')⟩

end Compression

/-! ## Theorem 1.1, uniform in the format -/

section Uniform

variable {k : ℕ}

/-- The candidate witnesses searched by the algorithm: either a cube-format
tensor with coded mutual-restriction matrices, or a leg with a coded minor
selection. -/
private abbrev UniformWitness (F : Type u) [Field F] (k : ℕ) (c : Fin k → ℕ+) :=
  (KTensor F c × List (List F) × List (List F))
    ⊕ (Fin k × List ℕ × List (List ℕ))

/-- One step of the algorithm's search (tex:316-317): a candidate witness is
either accepted as an equivalence of the input with a cube-format tensor `S`
(in which case the answer is the fixed polynomial test on `S`), or accepted
as a nonzero minor of size `s'` of a flattening (in which case the answer is
"no"), or rejected. -/
private noncomputable def uniformCheck (c : Fin k → ℕ+) (s' : ℕ)
    (polyCheck : KTensor F c → Bool) (x : FormatTensor F k)
    (w : UniformWitness F k c) : Option Bool :=
  Sum.elim
    (fun y : KTensor F c × List (List F) × List (List F) =>
      if restrictsCheckList k (formatList c) (formatList x.1)
            (entriesList y.1) (entriesList x.2) y.2.1
          && restrictsCheckList k (formatList x.1) (formatList c)
            (entriesList x.2) (entriesList y.1) y.2.2
        then some (polyCheck y.1)
        else none)
    (fun z : Fin k × List ℕ × List (List ℕ) =>
      if minorCheckList k s' (formatList x.1) (entriesList x.2) (z.1 : ℕ)
          z.2.1 z.2.2
        then some false
        else none) w

variable [Primcodable F] [ComputableField F]

omit [ComputableField F] in
/-- The entry list of a fixed-format tensor is computable. -/
private lemma computable_entriesList_fixed {d : Fin k → ℕ+} :
    Computable fun S : KTensor F d => entriesList S := by
  refine Computable.list_ofFn fun p => ?_
  refine (Computable.fin_app.comp (computable_entriesEquiv (F := F) (d := d))
    (Computable.const (Fintype.equivFin _ (finPiFinEquiv.symm p)))).of_eq
    fun S => ?_
  simp [Equiv.arrowCongr]

private lemma computable_uniformCheck (c : Fin k → ℕ+) (s' : ℕ)
    {polyCheck : KTensor F c → Bool} (hpoly : Computable polyCheck) :
    Computable₂ (uniformCheck (F := F) c s' polyCheck) := by
  let W := UniformWitness F k c
  let WL := KTensor F c × List (List F) × List (List F)
  let WR := Fin k × List ℕ × List (List ℕ)
  let inlBranch : (FormatTensor F k × W) → WL → Option Bool := fun p y =>
    if restrictsCheckList k (formatList c) (formatList p.1.1)
          (entriesList y.1) (entriesList p.1.2) y.2.1
        && restrictsCheckList k (formatList p.1.1) (formatList c)
          (entriesList p.1.2) (entriesList y.1) y.2.2
      then some (polyCheck y.1)
      else none
  let inrBranch : (FormatTensor F k × W) → WR → Option Bool := fun p z =>
    if minorCheckList k s' (formatList p.1.1) (entriesList p.1.2) (z.1 : ℕ)
        z.2.1 z.2.2
      then some false
      else none
  have hleft : Computable₂ inlBranch := by
    have hcheck₁ : Computable fun q : (FormatTensor F k × W) × WL =>
        restrictsCheckList k (formatList c) (formatList q.1.1.1)
          (entriesList q.2.1) (entriesList q.1.1.2) q.2.2.1 :=
      computable_restrictsCheckList (F := F) k
        (Computable.const (formatList c))
        (computable_formatList.comp (Computable.fst.comp (Computable.fst : Computable
          (fun q : (FormatTensor F k × W) × WL => q.1))))
        (computable_entriesList_fixed.comp (Computable.fst.comp (Computable.snd : Computable
          (fun q : (FormatTensor F k × W) × WL => q.2))))
        (computable_entriesList.comp (Computable.fst.comp (Computable.fst : Computable
          (fun q : (FormatTensor F k × W) × WL => q.1))))
        (Computable.fst.comp (Computable.snd.comp (Computable.snd : Computable
          (fun q : (FormatTensor F k × W) × WL => q.2))))
    have hcheck₂ : Computable fun q : (FormatTensor F k × W) × WL =>
        restrictsCheckList k (formatList q.1.1.1) (formatList c)
          (entriesList q.1.1.2) (entriesList q.2.1) q.2.2.2 :=
      computable_restrictsCheckList (F := F) k
        (computable_formatList.comp (Computable.fst.comp (Computable.fst : Computable
          (fun q : (FormatTensor F k × W) × WL => q.1))))
        (Computable.const (formatList c))
        (computable_entriesList.comp (Computable.fst.comp (Computable.fst : Computable
          (fun q : (FormatTensor F k × W) × WL => q.1))))
        (computable_entriesList_fixed.comp (Computable.fst.comp (Computable.snd : Computable
          (fun q : (FormatTensor F k × W) × WL => q.2))))
        (Computable.snd.comp (Computable.snd.comp (Computable.snd : Computable
          (fun q : (FormatTensor F k × W) × WL => q.2))))
    have hcond : Computable fun q : (FormatTensor F k × W) × WL =>
        restrictsCheckList k (formatList c) (formatList q.1.1.1)
            (entriesList q.2.1) (entriesList q.1.1.2) q.2.2.1
          && restrictsCheckList k (formatList q.1.1.1) (formatList c)
            (entriesList q.1.1.2) (entriesList q.2.1) q.2.2.2 :=
      Primrec.and.to_comp.comp hcheck₁ hcheck₂
    have hsome : Computable fun q : (FormatTensor F k × W) × WL =>
        some (polyCheck q.2.1) :=
      Computable.option_some.comp
        (hpoly.comp (Computable.fst.comp (Computable.snd : Computable
          (fun q : (FormatTensor F k × W) × WL => q.2))))
    refine (Computable.cond hcond hsome (Computable.const Option.none)).to₂.of_eq ?_
    rintro ⟨p, y⟩
    dsimp [inlBranch]
    cases restrictsCheckList k (formatList c) (formatList p.1.1)
        (entriesList y.1) (entriesList p.1.2) y.2.1
      <;> cases restrictsCheckList k (formatList p.1.1) (formatList c)
        (entriesList p.1.2) (entriesList y.1) y.2.2
      <;> rfl
  have hright : Computable₂ inrBranch := by
    have hfinVal : Computable fun j : Fin k => (j : ℕ) :=
      Computable.encode_iff.mp (Computable.encode.of_eq fun _ => rfl)
    have hcheck : Computable fun q : (FormatTensor F k × W) × WR =>
        minorCheckList (F := F) k s' (formatList q.1.1.1) (entriesList q.1.1.2)
          (q.2.1 : ℕ) q.2.2.1 q.2.2.2 :=
      computable_minorCheckList (F := F) k s'
        (computable_formatList.comp (Computable.fst.comp (Computable.fst : Computable
          (fun q : (FormatTensor F k × W) × WR => q.1))))
        (computable_entriesList.comp (Computable.fst.comp (Computable.fst : Computable
          (fun q : (FormatTensor F k × W) × WR => q.1))))
        (hfinVal.comp (Computable.fst.comp (Computable.snd : Computable
          (fun q : (FormatTensor F k × W) × WR => q.2))))
        (Computable.fst.comp (Computable.snd.comp (Computable.snd : Computable
          (fun q : (FormatTensor F k × W) × WR => q.2))))
        (Computable.snd.comp (Computable.snd.comp (Computable.snd : Computable
          (fun q : (FormatTensor F k × W) × WR => q.2))))
    have hsome : Computable fun _ : (FormatTensor F k × W) × WR => some false :=
      Computable.const (some false)
    refine (Computable.cond hcheck hsome (Computable.const Option.none)).to₂.of_eq ?_
    rintro ⟨p, z⟩
    dsimp [inrBranch]
    cases minorCheckList (F := F) k s' (formatList p.1.1) (entriesList p.1.2)
        (z.1 : ℕ) z.2.1 z.2.2
      <;> rfl
  have huncurried :=
    Computable.sumCasesOn (Computable.snd : Computable
      (fun p : FormatTensor F k × W => p.2)) hleft hright
  exact huncurried.to₂.of_eq fun xw => by
    rcases xw with ⟨x, w⟩
    cases w <;> rfl

/-- The first value found by `Nat.rfindOpt` is the unique sound answer. -/
private lemma mem_rfindOpt_of_sound {σ : Type*} {f : ℕ → Option σ} {v : σ}
    (hsound : ∀ n b, f n = some b → b = v)
    (htotal : ∃ n b, f n = some b) :
    v ∈ Nat.rfindOpt f := by
  have hdom : (Nat.rfindOpt f).Dom := by
    rw [Nat.rfindOpt_dom]
    obtain ⟨n, b, hb⟩ := htotal
    exact ⟨n, b, hb⟩
  obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp hdom
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hb
  rwa [hsound n b hn] at hb

/-- Decide a predicate by unbounded search over coded witnesses, given that
every accepted witness answers correctly (`hsound`) and every input admits an
accepted witness (`htotal`). -/
private lemma computablePred_of_uniformCheck (c : Fin k → ℕ+) (s' : ℕ)
    {polyCheck : KTensor F c → Bool} (hpoly : Computable polyCheck)
    {p : FormatTensor F k → Prop}
    (hsound : ∀ (x : FormatTensor F k) (w : UniformWitness F k c) (b : Bool),
      uniformCheck c s' polyCheck x w = some b → (b = true ↔ p x))
    (htotal : ∀ x : FormatTensor F k, ∃ (w : UniformWitness F k c) (b : Bool),
      uniformCheck c s' polyCheck x w = some b) :
    ComputablePred p := by
  classical
  refine ⟨fun _ => Classical.propDecidable _, ?_⟩
  have hval : ∀ (x : FormatTensor F k) (w : UniformWitness F k c) (b : Bool),
      uniformCheck c s' polyCheck x w = some b → b = decide (p x) := by
    intro x w b hw
    have h := hsound x w b hw
    rcases Bool.eq_false_or_eq_true b with hb | hb
    · subst hb
      symm
      rw [decide_eq_true_eq]
      exact h.mp rfl
    · subst hb
      symm
      rw [decide_eq_false_iff_not]
      intro hp
      simp [hp] at h
  have hstep :=
    Computable.bind_decode_iff.mpr (computable_uniformCheck (F := F) c s' hpoly)
  have hpart := Partrec.rfindOpt hstep
  refine hpart.of_eq_tot fun x => ?_
  refine mem_rfindOpt_of_sound (fun n b hn => ?_) ?_
  · obtain ⟨w, _, hw2⟩ := Option.bind_eq_some_iff.mp hn
    exact hval x w b hw2
  · obtain ⟨w, b, hw⟩ := htotal x
    refine ⟨@Encodable.encode _ Primcodable.toEncodable w, b, ?_⟩
    rw [@Encodable.encodek _ Primcodable.toEncodable w]
    simpa using hw

/-- **Theorem 1.1** (arXiv:2411.15789, tex:296-298): over a computable field,
for every `r`, there is an algorithm that, given the format `d` and a
`k`-tensor `T ∈ F^{d₁} ⊗ ⋯ ⊗ F^{d_k}`, decides whether `asympRank T ≤ r` —
one algorithm for all formats.

Following the paper's proof (tex:313-318), the algorithm is non-uniform in
`r`: the finitely many polynomials cutting out the sublevel set on the
`⌊r⌋ × ⋯ × ⌊r⌋` cube format are fixed constants of the algorithm. On input
`(d, T)` it searches for either an explicit equivalence of `T` with a
cube-format tensor `S` (then evaluates the polynomials on `S`), or a nonzero
`(⌊r⌋+1)`-minor of a flattening of `T` (then `asympRank T > r` since
flattening ranks lower-bound the asymptotic rank); the search terminates on
every input. -/
theorem computablePred_asympRank_le_uniform (r : ℝ) :
    ComputablePred fun x : FormatTensor F k => asympRank x.2 ≤ r := by
  classical
  by_cases hr : 0 ≤ r
  swap
  · -- `r < 0`: the answer is always "no" since `asympRank ≥ 0`.
    refine ⟨fun _ => Classical.propDecidable _, ?_⟩
    refine (Computable.const false).of_eq fun x => ?_
    symm
    rw [decide_eq_false_iff_not]
    intro hle
    exact hr (le_trans (asympRank_nonneg x.2) hle)
  by_cases hk : 1 ≤ k
  swap
  · -- `k = 0`: `asympRank` is identically `0` and `0 ≤ r`.
    refine ⟨fun _ => Classical.propDecidable _, ?_⟩
    refine (Computable.const true).of_eq fun x => ?_
    have h0 : asympRank x.2 = 0 := by simp [asympRank, hk]
    symm
    rw [decide_eq_true_eq]
    change asympRank x.2 ≤ r
    rw [h0]
    exact hr
  -- Main case. The cube dimension `mw = max 1 ⌊r⌋`, kept abstract: only the
  -- two numeric properties below are used.
  obtain ⟨mw, hmw_floor, hmw_gt⟩ : ∃ mw : ℕ+,
      (∀ n : ℕ, (n : ℝ) ≤ r → n ≤ (mw : ℕ)) ∧ r < ((mw : ℕ) : ℝ) + 1 := by
    refine ⟨⟨max 1 ⌊r⌋₊, by omega⟩, fun n hn => ?_, ?_⟩
    · exact le_trans (Nat.le_floor hn) (le_max_right 1 ⌊r⌋₊)
    · exact lt_of_lt_of_le (Nat.lt_floor_add_one r)
        (by exact_mod_cast Nat.add_le_add_right (le_max_right 1 ⌊r⌋₊) 1)
  -- The fixed polynomials on the cube format (constants of the algorithm).
  obtain ⟨s, hs⟩ := exists_finset_entryPolynomials_asympRank_le (F := F)
    (d := fun _ : Fin k => mw) hk r
  -- The polynomial test, computably.
  obtain ⟨instP, hpolyC⟩ := computablePred_finset_eval_eq_zero (F := F) s
  refine computablePred_of_uniformCheck (fun _ : Fin k => mw) ((mw : ℕ) + 1)
    hpolyC ?_ ?_
  -- Soundness: any accepted witness answers correctly.
  · rintro x (⟨S, A, B⟩ | ⟨j, rows, cols⟩) b hw
    · simp only [uniformCheck, Sum.elim_inl, Bool.and_eq_true,
        Option.ite_none_right_eq_some, Option.some.injEq] at hw
      obtain ⟨⟨hA, hB⟩, hb⟩ := hw
      have hequiv : asympRank S = asympRank x.2 :=
        Restricts.asympRank_eq_of_equiv
          (restricts_of_restrictsCheckList hA)
          (restricts_of_restrictsCheckList hB)
      rw [← hb, decide_eq_true_eq]
      rw [← hequiv, hs S]
    · simp only [uniformCheck, Sum.elim_inr,
        Option.ite_none_right_eq_some, Option.some.injEq] at hw
      obtain ⟨hmc, hb⟩ := hw
      obtain ⟨jF, hjF⟩ := exists_le_flatRank_of_minorCheckList hmc
      rw [← hb]
      refine iff_of_false (by simp) ?_
      intro hle
      have h1 : ((mw : ℕ) : ℝ) + 1 ≤ (flatRank x.2 {jF} : ℝ) := by
        exact_mod_cast hjF
      have h2 : (flatRank x.2 {jF} : ℝ) ≤ asympRank x.2 :=
        flatRank_le_asympRank x.2 jF
      linarith
  -- Totality: every input admits an accepted witness.
  · intro x
    by_cases hflat : ∀ j : Fin k, flatRank x.2 {j} ≤ (mw : ℕ)
    · obtain ⟨S, hST, hTS⟩ := exists_cube_equiv_of_flatRank_le x.2 mw hflat
      obtain ⟨A, hA⟩ := exists_restrictsCheckList_of_restricts hST
      obtain ⟨B, hB⟩ := exists_restrictsCheckList_of_restricts hTS
      refine ⟨Sum.inl (S, A, B),
        decide (∀ q ∈ s, MvPolynomial.eval S q = 0), ?_⟩
      have hcond : (restrictsCheckList k (formatList fun _ : Fin k => mw)
            (formatList x.1) (entriesList S) (entriesList x.2) A
          && restrictsCheckList k (formatList x.1)
            (formatList fun _ : Fin k => mw) (entriesList x.2)
            (entriesList S) B) = true := by
        rw [Bool.and_eq_true]
        exact ⟨hA, hB⟩
      simp only [uniformCheck, Sum.elim_inl, hcond, if_true]
    · push_neg at hflat
      obtain ⟨jF, hjF⟩ := hflat
      obtain ⟨rows, cols, hmc⟩ :=
        exists_minorCheckList_of_lt_flatRank x.2 jF hjF
      refine ⟨Sum.inr (jF, rows, cols), false, ?_⟩
      simp only [uniformCheck, Sum.elim_inr, hmc, if_true]

end Uniform

end Semicontinuity
