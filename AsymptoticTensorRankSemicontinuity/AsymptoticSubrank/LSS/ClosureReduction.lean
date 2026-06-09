/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.Topology.Algebra.MvPolynomial
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.LSS.OrderTransfer
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.LSS.AmbientDensity
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.LSS.Construction

namespace LSS

variable {n : ℕ}

/-- The **real ambient parameterization point** of the construction `φσ` at a real parameter
`θ`: the ambient output-coordinate vector `q ↦ eval θ (ambSub G σ e q) = eval θ (φσ(q.1)(q.2))`.
Its range (over all `θ`) is the real image `GOR⁺_σ(G)` of the parameterization (pre-closure). -/
noncomputable def ambRealPt (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Equiv.Perm (Fin n)) (e : ℕ) (θ : Fin n × ℕ → ℝ) : Fin n × Fin (e + 1) → ℝ :=
  fun q => MvPolynomial.eval θ (ambSub G σ e q)

/-- Evaluating the pullback `aeval (ambSub σ) p` at a real parameter `θ` equals evaluating the
ambient polynomial `p` at the corresponding image point `ambRealPt σ θ`. This is
`MvPolynomial.comp_aeval`: `eval θ ∘ aeval (ambSub σ) = eval (eval θ ∘ ambSub σ)`. -/
theorem eval_ambSub_aeval {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {e : ℕ}
    (σ : Equiv.Perm (Fin n)) (θ : Fin n × ℕ → ℝ)
    (p : MvPolynomial (Fin n × Fin (e + 1)) ℝ) :
    MvPolynomial.eval θ (MvPolynomial.aeval (ambSub G σ e) p)
      = MvPolynomial.eval (ambRealPt G σ e θ) p := by
  have h := AlgHom.congr_fun
    (MvPolynomial.comp_aeval (R := ℝ) (ambSub G σ e) (MvPolynomial.aeval θ)) p
  simpa [ambRealPt] using h

/-- The σ-kernel as a vanishing ideal: `aeval (ambSub σ) p = 0` (a polynomial identity) iff `p`
vanishes at every image point `ambRealPt σ θ`. A real polynomial is `0` iff all its real
evaluations vanish (`MvPolynomial.funext`), and
`eval θ (aeval (ambSub σ) p) = eval (ambRealPt σ θ) p` (`eval_ambSub_aeval`). -/
theorem aeval_ambSub_eq_zero_iff {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {e : ℕ}
    (σ : Equiv.Perm (Fin n)) (p : MvPolynomial (Fin n × Fin (e + 1)) ℝ) :
    MvPolynomial.aeval (ambSub G σ e) p = 0
      ↔ ∀ θ : Fin n × ℕ → ℝ, MvPolynomial.eval (ambRealPt G σ e θ) p = 0 := by
  constructor
  · intro h θ
    rw [← eval_ambSub_aeval, h, map_zero]
  · intro h
    apply MvPolynomial.funext
    intro θ
    rw [eval_ambSub_aeval, h θ, map_zero]

/-- A polynomial vanishing on a set vanishes on its closure (continuity of `eval`,
`isClosed_eq`). Stated in the ambient `(vertex, coord)`-indexed space. -/
theorem eval_eq_zero_of_mem_closure {e : ℕ}
    {S : Set (Fin n × Fin (e + 1) → ℝ)} {p : MvPolynomial (Fin n × Fin (e + 1)) ℝ}
    (h : ∀ x ∈ S, MvPolynomial.eval x p = 0) {x : Fin n × Fin (e + 1) → ℝ}
    (hx : x ∈ closure S) : MvPolynomial.eval x p = 0 := by
  have hcont : Continuous (fun y : Fin n × Fin (e + 1) → ℝ => MvPolynomial.eval y p) :=
    MvPolynomial.continuous_eval p
  exact (isClosed_eq hcont continuous_const).closure_subset_iff.mpr h hx

/-- **Closure equality ⟹ `Transfers`** (the kernel ↔ closure reduction).
If the two real ambient images have the same Euclidean closure
(`closure (range (ambRealPt σ)) = closure (range (ambRealPt τ))`), then `Transfers G e σ τ` —
the two pullback kernels agree.

Proof: by `aeval_ambSub_eq_zero_iff`, each kernel is the vanishing ideal of its image's RANGE.
A polynomial vanishes on the range iff on its closure (`eval_eq_zero_of_mem_closure` +
`subset_closure`), so equal closures give equal vanishing ideals, hence the kernel iff. -/
theorem transfers_of_closure_eq {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {e : ℕ}
    {σ τ : Equiv.Perm (Fin n)}
    (hcl : closure (Set.range (fun θ => ambRealPt G σ e θ))
         = closure (Set.range (fun θ => ambRealPt G τ e θ))) :
    Transfers G e σ τ := by
  -- A polynomial vanishes on `range (ambRealPt ρ)` iff on its closure.
  have hvan : ∀ (ρ : Equiv.Perm (Fin n)) (p : MvPolynomial (Fin n × Fin (e + 1)) ℝ),
      (∀ θ, MvPolynomial.eval (ambRealPt G ρ e θ) p = 0)
        ↔ (∀ x ∈ closure (Set.range (fun θ => ambRealPt G ρ e θ)),
              MvPolynomial.eval x p = 0) := by
    intro ρ p
    constructor
    · intro h x hx
      refine eval_eq_zero_of_mem_closure (S := Set.range (fun θ => ambRealPt G ρ e θ)) ?_ hx
      rintro y ⟨θ, rfl⟩; exact h θ
    · intro h θ
      exact h _ (subset_closure ⟨θ, rfl⟩)
  intro p
  rw [aeval_ambSub_eq_zero_iff, aeval_ambSub_eq_zero_iff,
    hvan σ p, hvan τ p, hcl]

/-- **The ordering-independent general-position locus `GOR`** (gorProof tex:301-312,
`lem:hasGOR`/`lem:ats1`), as a subset of the ambient output space `Fin n × Fin (e+1) → ℝ`.

A point `g` lies in `GORset` iff the curried representation `f v c := g (v, c)` is a
general-position orthogonal representation of `G`:
* **OR** — non-adjacent distinct vertices map to orthogonal vectors;
* **GP** — any `e+1` vertices have linearly independent images.

This predicate makes NO reference to the ordering `σ`, which is exactly the content of
gorProof tex:313 ("the above lemma did not depend on the ordering"): `GOR` is the COMMON dense
subset of `GOR⁺_σ` and `GOR⁺_τ` used in `lem:ats1`. -/
def GORset (G : SimpleGraph (Fin n)) (e : ℕ) : Set (Fin n × Fin (e + 1) → ℝ) :=
  {g | (∀ u v, u ≠ v → ¬ G.Adj u v → ∑ c, g (u, c) * g (v, c) = 0) ∧
       (∀ s : Finset (Fin n), s.card = e + 1 →
         LinearIndependent ℝ (fun i : (↑s : Set (Fin n)) => fun c => g (i.val, c)))}

end LSS
