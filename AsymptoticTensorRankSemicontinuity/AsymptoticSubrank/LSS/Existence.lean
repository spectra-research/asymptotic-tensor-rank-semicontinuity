/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.LSS.OrderInduction
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.LSS.DVertexBase
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.LSS.Descent
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.LSS.HIndep
import Mathlib.Logic.Equiv.Fintype

/-!
# LSS — the final existence assembly of the GOR theorem

This file is the **headline existence** step of the Lovász–Saks–Schrijver / Gortler–Theran
(GOR) formalization (`thm:main`). It wires together the order-transfer corollary
(`prop:order` ⟹ `detI_phiσ_ne_zero`), the ambient θ-density
(`DVertexBase.dense_paramLocus_of_ne`), and the ℚ-descent (`Descent`).

## Sources (verbatim)

* **Gortler–Theran**, arXiv:2310.11565,
  `the Gortler-Theran GOR proof notes`:
  - `thm:main` / `lem:nonempt1` + `prop:order` (tex:517-537): for ANY ordering `σ`, ALL the
    `D`-subset construction-determinants `det(φσ(I)) ≠ 0` as polynomials. Their product is a
    nonzero polynomial; a generic real point `θ` makes every determinant nonzero, so the
    evaluated rep is an OR (`phiσ_isOR_poly`) in general position (every `D`-subset
    independent). This is the **real GOR**.
* **Vrana–Christandl**, arXiv:1603.03964,
  `the Vrana-Christandl genmamu reference notes`:
  - tex:197 — clearing denominators: a rational GOR yields an integer one (LCM-clear).
  - tex:217 — the ℚ-descent (`Descent.exists_rat_gor_of_exists_real_gor`).

## Main declarations

* `exists_real_gor` — `(n−D)`-connectivity ⟹ a real GOR exists (`∃ f, IsGOR G f`).
* `exists_rat_gor` — `(n−D)`-connectivity ⟹ a **rational** GOR exists (every coordinate
  is the cast of a rational), via `exists_real_gor` + `HIndep` + the `Descent`.

## Status
Proved. No custom axioms.
-/

open scoped InnerProductSpace
open RealInnerProductSpace

namespace LSS

variable {n : ℕ}

/-! ### The per-subset ordering: placing a `D`-subset first.

Given a `D = e+1`-subset `s : Finset (Fin n)` and the canonical reindexing
`e_s : ↥(↑s) ≃ Fin (e+1)`, we build a permutation `subsetOrdering` of `Fin n` whose first `e+1`
positions enumerate `s` *in the order given by `e_s.symm`*. This makes the construction
determinant `det(φσ(Ivtx (subsetOrdering) a) b)` equal — after `eval θ` — to the `gpMatrix`
determinant whose rows are `f` of the vertices of `s` (reindexed by `e_s`). -/

/-- The canonical reindexing of a `D`-subset by `Fin (e+1)`. -/
noncomputable def subsetEquiv {e : ℕ} {s : Finset (Fin n)} (hs : s.card = e + 1) :
    (s : Set (Fin n)) ≃ Fin (e + 1) :=
  Finset.equivFinOfCardEq hs

/-- The "first `e+1` positions" subtype `{x : Fin n // x.val < e+1}` is equivalent to
`Fin (e+1)` (`hn : e+1 ≤ n`). -/
def firstBlockEquiv {e : ℕ} (hn : e + 1 ≤ n) : Fin (e + 1) ≃ { x : Fin n // x.val < e + 1 } where
  toFun a := ⟨⟨a.val, lt_of_lt_of_le a.isLt hn⟩, a.isLt⟩
  invFun x := ⟨x.1.val, x.2⟩
  left_inv a := by simp
  right_inv x := by ext; simp

/-- The subtype equivalence `{x : Fin n // x.val < e+1} ≃ {x : Fin n // x ∈ s}` realizing the
`subsetEquiv` reindexing: send a first-block position to the corresponding element of `s`. -/
noncomputable def blockToSubset {e : ℕ} {s : Finset (Fin n)} (hs : s.card = e + 1)
    (hn : e + 1 ≤ n) : { x : Fin n // x.val < e + 1 } ≃ { x : Fin n // x ∈ s } :=
  (firstBlockEquiv hn).symm.trans
    ((subsetEquiv hs).symm.trans (Equiv.subtypeEquivRight (fun x => by simp)))

/-- The permutation of `Fin n` placing the `D`-subset `s` (in the order `subsetEquiv hs`) at the
first `e+1` positions. Built from `blockToSubset` via `Equiv.extendSubtype`. -/
noncomputable def subsetOrdering {e : ℕ} {s : Finset (Fin n)} (hs : s.card = e + 1)
    (hn : e + 1 ≤ n) : Equiv.Perm (Fin n) :=
  Equiv.extendSubtype (blockToSubset hs hn)

/-- **Key identity.** The `I`-vertex at position `a` of `subsetOrdering hs hn` is exactly the
`a`-th element of `s` in the `subsetEquiv` enumeration: `Ivtx (subsetOrdering hs hn) hn a`
equals `((subsetEquiv hs).symm a : Fin n)`. -/
theorem Ivtx_subsetOrdering {e : ℕ} {s : Finset (Fin n)} (hs : s.card = e + 1) (hn : e + 1 ≤ n)
    (a : Fin (e + 1)) :
    Ivtx (subsetOrdering hs hn) hn a = ((subsetEquiv hs).symm a : Fin n) := by
  classical
  -- The position `⟨a.val, _⟩ : Fin n` satisfies the predicate `· < e+1`.
  have hp : (⟨a.val, lt_of_lt_of_le a.isLt hn⟩ : Fin n).val < e + 1 := a.isLt
  have hkey : subsetOrdering hs hn ⟨a.val, lt_of_lt_of_le a.isLt hn⟩
      = ((subsetEquiv hs).symm a : Fin n) := by
    rw [subsetOrdering, Equiv.extendSubtype_apply_of_mem (blockToSubset hs hn) _ hp]
    -- Unfold `blockToSubset`: `firstBlockEquiv.symm` of `⟨a.val,_⟩` is `a`.
    have hfb : (firstBlockEquiv hn).symm ⟨⟨a.val, lt_of_lt_of_le a.isLt hn⟩, hp⟩ = a := by
      rw [Equiv.symm_apply_eq]
      apply Subtype.ext
      apply Fin.ext
      rfl
    simp only [blockToSubset, Equiv.trans_apply, Equiv.subtypeEquivRight_apply_coe, hfb]
  exact hkey

/-! ### The product of all `D`-subset determinants is a nonzero polynomial. -/

/-- The construction-determinant polynomial of the `D`-subset `s` (placing `s` first via
`subsetOrdering`), under the fixed ambient ordering `σ`. -/
noncomputable def subsetDet (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (σ : Equiv.Perm (Fin n))
    (e : ℕ) (hn : e + 1 ≤ n) (s : { s : Finset (Fin n) // s.card = e + 1 }) : Poly n :=
  Matrix.det (Matrix.of fun (a b : Fin (e + 1)) =>
    phiσ G σ e (Ivtx (subsetOrdering s.2 hn) hn a) b)

/-- **`prop:order` ⟹ every subset-determinant polynomial is nonzero.** -/
theorem subsetDet_ne_zero (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (e : ℕ) (hconn : IsKVertexConnected G (n - (e + 1)))
    (hcard : ∀ (σ : Equiv.Perm (Fin n)) v, (precNonNbrσ G σ v).card ≤ e)
    (σ : Equiv.Perm (Fin n)) (hn : e + 1 ≤ n)
    (s : { s : Finset (Fin n) // s.card = e + 1 }) :
    subsetDet G σ e hn s ≠ 0 :=
  detI_phiσ_ne_zero e hconn hcard σ (subsetOrdering s.2 hn) hn

/-- The product over all `D`-subsets of the construction-determinant polynomials. A product of
nonzero polynomials over the integral domain `Poly n = MvPolynomial _ ℝ`, hence nonzero. -/
noncomputable def bigDet (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (σ : Equiv.Perm (Fin n))
    (e : ℕ) (hn : e + 1 ≤ n) : Poly n :=
  ∏ s : { s : Finset (Fin n) // s.card = e + 1 }, subsetDet G σ e hn s

theorem bigDet_ne_zero (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (e : ℕ) (hconn : IsKVertexConnected G (n - (e + 1)))
    (hcard : ∀ (σ : Equiv.Perm (Fin n)) v, (precNonNbrσ G σ v).card ≤ e)
    (σ : Equiv.Perm (Fin n)) (hn : e + 1 ≤ n) :
    bigDet G σ e hn ≠ 0 := by
  classical
  rw [bigDet, Finset.prod_ne_zero_iff]
  intro s _
  exact subsetDet_ne_zero G e hconn hcard σ hn s

/-! ### The generic real point and its evaluated representation. -/

/-- The evaluated representation at a real point `θ`: vertex `v` is sent to the Euclidean vector
whose `c`-th coordinate is `eval θ (φσ(v) c)`. (This is `realPhi G σ e θ v` packaged into
`EuclideanSpace`.) -/
noncomputable def evalRep (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (σ : Equiv.Perm (Fin n))
    (e : ℕ) (θ : Fin n × ℕ → ℝ) : Fin n → EuclideanSpace ℝ (Fin (e + 1)) :=
  fun v => (EuclideanSpace.equiv (Fin (e + 1)) ℝ).symm
    (fun c => MvPolynomial.eval θ (phiσ G σ e v c))

@[simp] theorem evalRep_coord (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Equiv.Perm (Fin n)) (e : ℕ) (θ : Fin n × ℕ → ℝ) (v : Fin n) (c : Fin (e + 1)) :
    evalRep G σ e θ v c = MvPolynomial.eval θ (phiσ G σ e v c) := rfl

set_option maxHeartbeats 1000000 in
-- `phiσ` is a heavy well-founded recursion; unifying `eval θ (phiσ …)` against the
-- polynomial-OR identity exceeds the default heartbeat budget.
/-- **The evaluated rep is an OR** (`phiσ_isOR_poly` evaluated). -/
theorem evalRep_isOR (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (σ : Equiv.Perm (Fin n))
    (e : ℕ) (θ : Fin n × ℕ → ℝ)
    (hcard : ∀ (σ : Equiv.Perm (Fin n)) v, (precNonNbrσ G σ v).card ≤ e) :
    IsOR G (evalRep G σ e θ) := by
  intro i j hij hadj
  -- The Euclidean inner product is the coordinate sum.
  have hsum : (⟪evalRep G σ e θ i, evalRep G σ e θ j⟫_ℝ : ℝ)
      = ∑ c, (evalRep G σ e θ i c) * (evalRep G σ e θ j c) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [RCLike.inner_apply, conj_trivial]
    rw [mul_comm]
  rw [hsum]
  -- Each coordinate is `eval θ (phiσ …)`; pull `eval θ` out of the sum and use `phiσ_isOR_poly`.
  have hpoly : (∑ c, (phiσ G σ e i c) * (phiσ G σ e j c)) = 0 :=
    phiσ_isOR_poly G σ e hij (fun h => hadj h.symm) hadj (hcard σ j) (hcard σ i)
  calc ∑ c, (evalRep G σ e θ i c) * (evalRep G σ e θ j c)
      = ∑ c, MvPolynomial.eval θ ((phiσ G σ e i c) * (phiσ G σ e j c)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [evalRep_coord, map_mul]
    _ = MvPolynomial.eval θ (∑ c, (phiσ G σ e i c) * (phiσ G σ e j c)) := by
        rw [map_sum]
    _ = MvPolynomial.eval θ (0 : Poly n) := by rw [hpoly]
    _ = 0 := by simp

set_option maxHeartbeats 1000000 in
-- `subsetDet` carries the heavy `phiσ`/`subsetOrdering` term; the `RingHom.map_det` and
-- `gpMatrix` reconciliation exceed the default heartbeat budget.
/-- **The evaluated rep is in general position** when `θ` avoids the zero locus of `bigDet`.
For every `D`-subset `s`, the determinant `eval θ (subsetDet … s)` is nonzero (since it divides
`eval θ (bigDet …) ≠ 0`), and that determinant equals the `gpMatrix` determinant of the rows
`evalRep …` of the vertices of `s`, reindexed by `subsetEquiv`. By
`Descent.linearIndependent_iff_gpMatrix_det_ne_zero`, the family is linearly independent. -/
theorem evalRep_isGP (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (σ : Equiv.Perm (Fin n))
    (e : ℕ) (hn : e + 1 ≤ n) (θ : Fin n × ℕ → ℝ)
    (hθ : MvPolynomial.eval θ (bigDet G σ e hn) ≠ 0) :
    IsGP (evalRep G σ e θ) := by
  classical
  intro s hs
  -- The reindexing of `s` by `Fin (e+1)`.
  set es : (s : Set (Fin n)) ≃ Fin (e + 1) := subsetEquiv hs with hes
  -- Linear independence ↔ the `gpMatrix` determinant is nonzero.
  rw [linearIndependent_iff_gpMatrix_det_ne_zero (evalRep G σ e θ) es]
  -- The subset-determinant polynomial evaluated at `θ` is nonzero (factor of `bigDet`).
  have hbig : MvPolynomial.eval θ (subsetDet G σ e hn ⟨s, hs⟩) ≠ 0 := by
    have hprod : MvPolynomial.eval θ (bigDet G σ e hn)
        = ∏ t : { t : Finset (Fin n) // t.card = e + 1 },
            MvPolynomial.eval θ (subsetDet G σ e hn t) := by
      rw [bigDet, MvPolynomial.eval_prod]
    rw [hprod] at hθ
    intro hzero
    apply hθ
    rw [Finset.prod_eq_zero_iff]
    exact ⟨⟨s, hs⟩, Finset.mem_univ _, hzero⟩
  -- `eval θ (subsetDet …)` = `det` of the real matrix whose row `a` is `evalRep (Ivtx … a)`.
  -- Generalize the row index function so the heavy `phiσ`/`subsetOrdering` term is opaque.
  set g : Fin (e + 1) → Fin n := Ivtx (subsetOrdering hs hn) hn with hg
  have hsubsetDet : subsetDet G σ e hn ⟨s, hs⟩
      = Matrix.det (Matrix.of fun (a b : Fin (e + 1)) => phiσ G σ e (g a) b) := rfl
  have heval : MvPolynomial.eval θ (subsetDet G σ e hn ⟨s, hs⟩)
      = Matrix.det (Matrix.of fun (a b : Fin (e + 1)) => evalRep G σ e θ (g a) b) := by
    rw [hsubsetDet, RingHom.map_det]
    rfl
  rw [heval] at hbig
  -- The `gpMatrix` of `evalRep` (reindexed by `es`) equals that matrix, since
  -- `es.symm a = Ivtx (subsetOrdering hs hn) hn a`.
  have hmat : gpMatrix (evalRep G σ e θ) es
      = Matrix.of fun (a b : Fin (e + 1)) => evalRep G σ e θ (g a) b := by
    funext a b
    simp only [gpMatrix, Matrix.of_apply]
    -- `es.symm a = (subsetEquiv hs).symm a` and `Ivtx_subsetOrdering` gives the value.
    have hval : ((es.symm a : (s : Set (Fin n))) : Fin n) = g a := by
      rw [hes, hg, ← Ivtx_subsetOrdering hs hn a]
    rw [hval]
  rw [hmat]
  exact hbig

/-! ### `exists_real_gor` — the headline existence (`thm:main`). -/

/-- **`exists_real_gor`** (Gortler–Theran `thm:main`, gorProof tex:517-537).
If `G` is `(n − D)`-connected (`D = e+1`) with the predecessor bound `|P_v| ≤ e`, then `G` has a
**real general-position orthogonal representation** in `ℝ^D = ℝ^(e+1)`.

Proof: fix the identity ordering `σ`. By `prop:order` (`detI_phiσ_ne_zero`), every `D`-subset's
construction determinant is a nonzero polynomial; their product `bigDet` is nonzero
(integral domain). By the θ-density `DVertexBase.dense_paramLocus_of_ne`, the non-vanishing locus
of `bigDet` is dense, hence nonempty: there is a real `θ` with `eval θ (bigDet) ≠ 0`. The
evaluated rep `evalRep σ θ` is then an OR (`phiσ_isOR_poly` evaluated, `evalRep_isOR`) and in
general position (`evalRep_isGP`: each `D`-subset's `gpMatrix` determinant `= eval θ (subsetDet)`,
a nonzero factor of `eval θ (bigDet)`, so by `linearIndependent_iff_gpMatrix_det_ne_zero` the
`D`-subset is independent). -/
theorem exists_real_gor {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (e : ℕ)
    (hn : e + 1 ≤ n) (hconn : IsKVertexConnected G (n - (e + 1)))
    (hcard : ∀ (σ : Equiv.Perm (Fin n)) v, (precNonNbrσ G σ v).card ≤ e) :
    ∃ f : Fin n → EuclideanSpace ℝ (Fin (e + 1)), IsGOR G f := by
  classical
  -- Fix the identity ordering.
  set σ : Equiv.Perm (Fin n) := 1 with hσ
  -- The product polynomial is nonzero.
  have hbig : bigDet G σ e hn ≠ 0 := bigDet_ne_zero G e hconn hcard σ hn
  -- Its non-vanishing locus is dense, hence nonempty.
  have hdense : Dense { θ : Fin n × ℕ → ℝ | MvPolynomial.eval θ (bigDet G σ e hn) ≠ 0 } :=
    dense_paramLocus_of_ne hbig
  obtain ⟨θ, hθ⟩ := hdense.nonempty
  -- The evaluated rep is the witness GOR.
  refine ⟨evalRep G σ e θ, ?_, ?_⟩
  · exact evalRep_isOR G σ e θ hcard
  · exact evalRep_isGP G σ e hn θ hθ

/-! ### `exists_rat_gor` — the rational GOR (the ℚ-descent). -/

/-- **`exists_rat_gor`** (Vrana–Christandl genmamu tex:217, the ℚ-descent applied to the GOR).
If `G` is `(n − D)`-connected with the predecessor bound, then `G` has a **rational**
general-position orthogonal representation: every coordinate of every vector is the cast of a
rational. (LCM-clearing, genmamu tex:197, would then give an *integer* GOR; the rational GOR is
the form consumed by the VC continuity argument.)

Proof: `exists_real_gor` produces a real GOR `f`; `HIndep.isKVertexConnected_isGOR_hindep`
supplies the preceding-non-neighbour independence hypothesis `hindep` from connectivity; then
`Descent.exists_rat_gor_of_exists_real_gor` descends to a rational GOR. -/
theorem exists_rat_gor {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (e : ℕ)
    (hn : e + 1 ≤ n) (hconn : IsKVertexConnected G (n - (e + 1)))
    (hcard : ∀ (σ : Equiv.Perm (Fin n)) v, (precNonNbrσ G σ v).card ≤ e) :
    ∃ f : Fin n → EuclideanSpace ℝ (Fin (e + 1)),
      IsGOR G f ∧ (∀ i c, (f i) c ∈ Set.range ((↑) : ℚ → ℝ)) := by
  -- Real GOR.
  obtain ⟨f, hf⟩ := exists_real_gor (G := G) e hn hconn hcard
  -- Connectivity supplies the preceding-non-neighbour independence (`D = e+1 ≤ n`).
  have hindep : ∀ i : Fin n,
      LinearIndependent ℝ (fun j : (precNonNbr G i : Set (Fin n)) => f j.val) := by
    have hconn' : IsKVertexConnected G (n - (e + 1)) := hconn
    exact isKVertexConnected_isGOR_hindep (D := e + 1) hconn' hn f hf
  -- The ℚ-descent.
  exact exists_rat_gor_of_exists_real_gor G ⟨f, hf, hindep⟩

end LSS
