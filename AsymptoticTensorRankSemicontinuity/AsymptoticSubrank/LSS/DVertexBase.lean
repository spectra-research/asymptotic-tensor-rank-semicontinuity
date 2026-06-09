/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# LSS D-vertex single-determinant density

This file formalizes the first-`D` density component of
`lem:hasGOR`/`lem:ats1`/`lem:base1` from gorProof tex:301-361.

For the induced subgraph on the first `D = e+1` `ρ`-positions, the general-position
condition is a single determinant: the only `D`-subset is all `D` vertices. That
determinant is non-vanishing by `NonEmpty.detI_phiσ_ne_zero_of_first`
(gorProof tex:308-311, "we can just use the elementary vectors"), so its
non-vanishing locus is Zariski-open, nonempty, and Euclidean-dense by
`AmbientDensity.dense_compl_zeroLocus_real`.

Main declarations:

* `ambDetReal` — the real evaluation `g ↦ eval g (ambDetI e Iv)` of the single
  ambient `I`-determinant.
* `dense_ambDetLocus_of_ne` — Euclidean density of the non-vanishing locus of a
  nonzero ambient polynomial over `Fin n × Fin (e+1)`, transported from
  `AmbientDensity.dense_compl_zeroLocus_real` along
  `(Fin n × Fin (e+1)) ≃ Fin m`.
* `ambDetI_ne_zero_of_first` — `ambDetI e (Ivtx ρ hn) ≠ 0`, from
  `aeval_ambDetI` and `NonEmpty.detI_phiσ_ne_zero_of_first`.
* `dense_ambDetLocus_Ivtx` — Euclidean density of the I-determinant
  non-vanishing locus, the `lem:hasGOR` density for `G⁻`.
* `ambDetLocus_eq_of_ivtx_comp_perm` — ordering-independence of the
  I-determinant locus up to the vertex set: if `Ivtx τ = Ivtx σ ∘ w` for a
  permutation `w` of `Fin (e+1)`, the two loci coincide because the determinant
  differs only by `sign w` (gorProof tex:313-319, `lem:ats1`).

The closure/image part of `lem:hasGOR`/`lem:base1` (gorProof tex:309-361) uses
the same determinant locus together with the shared
`ψ = φ_{ρ_{D+1}} ∘ ⋯ ∘ φ_{ρ_n}` tail of the construction.
-/
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.LSS.OrderTransfer
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.LSS.AmbientDensity
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.LSS.NonEmpty
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.LSS.ClosureReduction

namespace LSS

open MvPolynomial

variable {n : ℕ}

/-! ## The single ambient `I`-determinant, evaluated over `ℝ`. -/

/-- The **real** evaluation of the single ambient `I`-determinant: `g ↦ eval g (ambDetI e Iv)`.
Its non-vanishing locus is the `G⁻`-general-position locus for the first-`D` vertices `Iv`
(the SINGLE determinant — only one `D`-subset for `D` vertices). gorProof tex:302-311. -/
noncomputable def ambDetReal (e : ℕ) (Iv : Fin (e + 1) → Fin n)
    (g : Fin n × Fin (e + 1) → ℝ) : ℝ :=
  MvPolynomial.eval g (ambDetI e Iv)

/-! ## The D-vertex density key.

`AmbientDensity.dense_compl_zeroLocus_real` proves Euclidean-density of the non-vanishing
locus of a nonzero polynomial, but is stated over the index `Fin m`. The ambient ring is
indexed by the FINITE type `Fin n × Fin (e+1)`. We transport along the fintype equiv
`(Fin n × Fin (e+1)) ≃ Fin m` (`Fintype.equivFin`) using `rename`/`eval_rename` and the
homeomorphism `Homeomorph.piCongrLeft` on the evaluation spaces. -/

/-- The Euclidean non-vanishing locus of a nonzero ambient polynomial
`p : MvPolynomial (Fin n × Fin (e+1)) ℝ` is dense in
`Fin n × Fin (e+1) → ℝ`.

Transport of `AmbientDensity.dense_compl_zeroLocus_real` (over `Fin m`) along the fintype
equiv `eqv : (Fin n × Fin (e+1)) ≃ Fin m`: rename `p` to `q := rename eqv p` over `Fin m`
(nonzero since `rename` of a bijection is injective), apply the density there, and pull back
along the homeomorphism `Homeomorph.piCongrLeft eqv : (Fin n × Fin (e+1) → ℝ) ≃ₜ (Fin m → ℝ)`
using `eval_rename`. (gorProof tex:308-311 / `lem:dense` tex:238-254.) -/
theorem dense_ambDetLocus_of_ne {e : ℕ} {p : MvPolynomial (Fin n × Fin (e + 1)) ℝ}
    (hp : p ≠ 0) :
    Dense { g : Fin n × Fin (e + 1) → ℝ | MvPolynomial.eval g p ≠ 0 } := by
  classical
  -- Fintype equiv to a standard `Fin m`.
  let m := Fintype.card (Fin n × Fin (e + 1))
  let eqv : (Fin n × Fin (e + 1)) ≃ Fin m := Fintype.equivFin _
  -- Rename `p` to a polynomial over `Fin m`; it is nonzero.
  let q : MvPolynomial (Fin m) ℝ := rename eqv p
  have hq_ne : q ≠ 0 := by
    intro h
    apply hp
    have := congrArg (rename eqv.symm) h
    simpa [q, rename_rename, Equiv.symm_comp_self] using this
  -- Density over `Fin m`.
  have hdense : Dense { y : Fin m → ℝ | MvPolynomial.eval y q ≠ 0 } :=
    AmbientDensity.dense_compl_zeroLocus_real hq_ne
  -- The homeomorphism on evaluation spaces.
  let h : (Fin n × Fin (e + 1) → ℝ) ≃ₜ (Fin m → ℝ) :=
    Homeomorph.piCongrLeft (Y := fun _ : Fin m => ℝ) eqv
  -- `(h g) ∘ eqv = g`.
  have hcomp : ∀ g : Fin n × Fin (e + 1) → ℝ,
      (h g) ∘ (eqv : Fin n × Fin (e + 1) → Fin m) = g := by
    intro g
    funext i
    change (h.toEquiv g) (eqv i) = g i
    rw [show h.toEquiv = Equiv.piCongrLeft (fun _ : Fin m => ℝ) eqv from rfl,
      Equiv.piCongrLeft_apply_apply]
  -- The locus over `ι` is the preimage of the locus over `Fin m` under `h`.
  have hpre : { g : Fin n × Fin (e + 1) → ℝ | MvPolynomial.eval g p ≠ 0 }
      = h ⁻¹' { y : Fin m → ℝ | MvPolynomial.eval y q ≠ 0 } := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    -- `eval (h g) q = eval (h g) (rename eqv p) = eval ((h g) ∘ eqv) p = eval g p`.
    rw [show q = rename eqv p from rfl, eval_rename, hcomp g]
  rw [hpre]
  exact hdense.preimage h.isOpenMap

/-! ## The single I-determinant is a nonzero polynomial.

The ambient I-determinant `ambDetI e (Ivtx ρ hn)` pulls back, under the ρ-construction, to the
concrete `NonEmpty.detI G ρ e hn` (`aeval_ambDetI` + the `detI` definition). The latter is
nonzero by `NonEmpty.detI_phiσ_ne_zero_of_first` — for `D = e+1` vertices, any ordering places
the `I`-vertices first, so the construction can realize them in general position via the
elementary vectors (gorProof tex:308-311, "we can just use the elementary vectors"). This is
the single `D`-subset determinant. -/

set_option linter.unusedDecidableInType false in
/-- `ambDetI e (Ivtx ρ hn) ≠ 0` as an ambient polynomial.
`aeval (ambSub G ρ e)` sends it to `det (φρ(Ivtx ρ hn a) b) = detI G ρ e hn ≠ 0`
(`NonEmpty.detI_phiσ_ne_zero_of_first`); a polynomial with a nonzero ring-hom image is nonzero.
gorProof tex:308-311 (`lem:hasGOR`). -/
theorem ambDetI_ne_zero_of_first {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (ρ : Equiv.Perm (Fin n)) (e : ℕ) (hn : e + 1 ≤ n) :
    ambDetI e (Ivtx ρ hn) ≠ 0 := by
  intro h
  -- pulling back the zero polynomial gives `0`, but the pullback is `detI ≠ 0`.
  have hpull : MvPolynomial.aeval (ambSub G ρ e) (ambDetI e (Ivtx ρ hn)) = 0 := by
    rw [h]; simp
  rw [aeval_ambDetI] at hpull
  -- `det (φρ (Ivtx ρ hn a) b)` is exactly `detI G ρ e hn`.
  exact detI_phiσ_ne_zero_of_first G ρ e hn hpull

set_option linter.unusedDecidableInType false in
/-- The Euclidean non-vanishing locus of the single I-determinant
`ambDetI e (Ivtx ρ hn)` is dense
in the ambient space `Fin n × Fin (e+1) → ℝ`. Combines `ambDetI_ne_zero_of_first` (nonzero) with
`dense_ambDetLocus_of_ne` (Euclidean density of a nonzero polynomial's non-vanishing locus).
gorProof tex:308-311. -/
theorem dense_ambDetLocus_Ivtx {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (ρ : Equiv.Perm (Fin n)) (e : ℕ) (hn : e + 1 ≤ n) :
    Dense { g : Fin n × Fin (e + 1) → ℝ | ambDetReal e (Ivtx ρ hn) g ≠ 0 } :=
  dense_ambDetLocus_of_ne (ambDetI_ne_zero_of_first (G := G) ρ e hn)

/-! ## θ-space density of the construction-determinant non-vanishing locus.

`lem:hasGOR`'s image-glue (gorProof tex:304-312) needs the non-vanishing locus to be dense in
the construction's real image, not just in the finite ambient space. Push
density to the (infinite-index) parameter space `Fin n × ℕ → ℝ` of the
construction `φρ`: the set `{θ | eval θ q ≠ 0}` for a nonzero parameter polynomial `q` is dense
there, and its image under the continuous parameterization is dense in `range`.

The parameter index `Fin n × ℕ` is INFINITE, so `dense_compl_zeroLocus_real` (over `Fin k`) does
not apply. Instead we prove density directly from `MvPolynomial.funext_set`: a basic open box in
the product topology constrains only FINITELY many coordinates, each to a nonempty open (hence
infinite) set, leaving the rest free over all of `ℝ`; a polynomial vanishing on such a box of
infinite sets is `0`, contradicting `q ≠ 0`. -/

/-- For a nonzero polynomial `q` over the (possibly infinite) index
`Fin n × ℕ`, the Euclidean non-vanishing locus `{θ | eval θ q ≠ 0}` is dense in the product
space `Fin n × ℕ → ℝ`.

Proof: by `dense_iff_inter_open`, given a nonempty open `U` and `θ₀ ∈ U`, `isOpen_pi_iff`
supplies a basic box `(↑I).pi u ⊆ U` with each `u a` (`a ∈ I`) open and containing `θ₀ a`.
Build `s : (Fin n × ℕ) → Set ℝ` equal to `u a` on `I` and `Set.univ` off `I`; each `s a` is
INFINITE (nonempty open ⟹ infinite by `AmbientDensity.isOpen_real_infinite_of_mem`; `univ`
infinite). If `q` vanished on all of `univ.pi s` then `q = 0` by `MvPolynomial.funext_set` —
contradiction. So some `θ ∈ univ.pi s` has `eval θ q ≠ 0`; this `θ` lies in the box (hence in
`U`) and in the locus. -/
theorem dense_paramLocus_of_ne {q : MvPolynomial (Fin n × ℕ) ℝ} (hq : q ≠ 0) :
    Dense { θ : Fin n × ℕ → ℝ | MvPolynomial.eval θ q ≠ 0 } := by
  classical
  rw [dense_iff_inter_open]
  intro U hUopen hUne
  obtain ⟨θ₀, hθ₀⟩ := hUne
  obtain ⟨I, u, hIu, hbox⟩ := isOpen_pi_iff.mp hUopen θ₀ hθ₀
  -- The coordinate-wise constraint set: `u a` on `I`, all of `ℝ` off `I`.
  set s : (Fin n × ℕ) → Set ℝ := fun a => if a ∈ I then u a else Set.univ with hs
  have hs_inf : ∀ a, (s a).Infinite := by
    intro a
    by_cases haI : a ∈ I
    · simp only [hs, if_pos haI]
      exact AmbientDensity.isOpen_real_infinite_of_mem (hIu a haI).1 (hIu a haI).2
    · simp only [hs, if_neg haI]; exact Set.infinite_univ
  -- `q` cannot vanish on the whole box (else `q = 0`).
  have hexists : ∃ θ ∈ Set.univ.pi s, MvPolynomial.eval θ q ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hq (MvPolynomial.funext_set (q := 0) s hs_inf
      (by intro x hx; rw [hall x hx]; simp))
  obtain ⟨θ, hθmem, hθne⟩ := hexists
  refine ⟨θ, ?_, hθne⟩
  -- `θ` lies in the basic box (its `I`-coordinates land in `u`), hence in `U`.
  apply hbox
  intro a haI
  rw [Finset.mem_coe] at haI
  have hmem := hθmem a (Set.mem_univ a)
  rw [hs] at hmem
  simp only at hmem
  rwa [if_pos haI] at hmem

/-! ## The image-glue: the det-locus is dense in the construction's REAL IMAGE.

`lem:hasGOR` (gorProof tex:304-312) says `GOR` (the det non-vanishing locus) is dense in
`GOR⁺_σ = closure (range φσ)`. We obtain this by pushing the θ-space density
(`dense_paramLocus_of_ne`, applied to the nonzero construction-determinant
`NonEmpty.detI G σ e hn`) forward through the parameterization `ambRealPt G σ e`, using the
eval-commutation `ambDetReal (Ivtx σ) (ambRealPt σ θ) = eval θ (detI σ)`. -/

set_option linter.unusedDecidableInType false in
/-- Eval-commutation linking the ambient I-determinant locus to the θ-space
construction-determinant: evaluating `ambDetReal e (Ivtx σ hn)` at the image point
`ambRealPt G σ e θ` equals evaluating the construction determinant `detI G σ e hn` at `θ`.

`ambDetReal e Iv g = eval g (ambDetI e Iv)`; `eval (ambRealPt σ θ) (ambDetI e Iv)
= eval θ (aeval (ambSub σ) (ambDetI e Iv))` (`eval_ambSub_aeval`); and
`aeval (ambSub σ) (ambDetI e (Ivtx σ hn)) = detI G σ e hn` (`aeval_ambDetI` + `detI`). -/
theorem ambDetReal_ambRealPt {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (σ : Equiv.Perm (Fin n)) (e : ℕ) (hn : e + 1 ≤ n) (θ : Fin n × ℕ → ℝ) :
    ambDetReal e (Ivtx σ hn) (ambRealPt G σ e θ) = MvPolynomial.eval θ (detI G σ e hn) := by
  rw [ambDetReal, ← eval_ambSub_aeval, aeval_ambDetI]
  rfl

set_option linter.unusedDecidableInType false in
/-- **`lem:hasGOR` image-glue, gorProof tex:304-312.** The det-locus is dense in
`closure (range (ambRealPt G σ e))`: the points of the closure that lie in the I-determinant
non-vanishing locus `{g | ambDetReal e (Ivtx σ hn) g ≠ 0}` form a dense subset of that closure.

Concretely `range (ambRealPt σ) ∩ L_σ` is dense in `closure (range (ambRealPt σ))`, where
`L_σ` is the det-locus. This is exactly "GOR is dense in GOR⁺_σ" of `lem:hasGOR`.

Proof: the parameterization `φσ : (Fin n × ℕ → ℝ) → (Fin n × Fin (e+1) → ℝ)`, `θ ↦ ambRealPt σ θ`
is continuous (each coordinate is `eval θ` of a fixed polynomial). The θ-set
`S := {θ | eval θ (detI σ) ≠ 0}` is dense (`dense_paramLocus_of_ne`, `detI ≠ 0` by
`detI_phiσ_ne_zero_of_first`). By `AmbientDensity.dense_image_in_closure_range_of_dense`,
`φσ '' S` is dense in `closure (range φσ)`. Finally `φσ '' S ⊆ range φσ ∩ L_σ`: for `θ ∈ S`,
`ambDetReal (Ivtx σ) (φσ θ) = eval θ (detI σ) ≠ 0` (`ambDetReal_ambRealPt`). -/
theorem dense_image_detLocus_in_closure_range
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (σ : Equiv.Perm (Fin n)) (e : ℕ) (hn : e + 1 ≤ n) :
    closure (Set.range (fun θ => ambRealPt G σ e θ))
      ⊆ closure ((Set.range (fun θ => ambRealPt G σ e θ))
          ∩ { g : Fin n × Fin (e + 1) → ℝ | ambDetReal e (Ivtx σ hn) g ≠ 0 }) := by
  -- The parameterization is continuous: each output coordinate is `eval θ` of a fixed
  -- polynomial (`MvPolynomial.continuous_eval`), and the codomain is a pi type.
  have hcont : Continuous (fun θ : Fin n × ℕ → ℝ => ambRealPt G σ e θ) := by
    apply continuous_pi
    intro q
    exact MvPolynomial.continuous_eval (ambSub G σ e q)
  -- The dense θ-set: where the construction determinant is nonzero.
  have hdetI : detI G σ e hn ≠ 0 := detI_phiσ_ne_zero_of_first G σ e hn
  have hSdense : Dense { θ : Fin n × ℕ → ℝ | MvPolynomial.eval θ (detI G σ e hn) ≠ 0 } :=
    dense_paramLocus_of_ne hdetI
  -- Its image under the parameterization is contained in `range ∩ L_σ`.
  have himg_sub : (fun θ => ambRealPt G σ e θ) ''
        { θ : Fin n × ℕ → ℝ | MvPolynomial.eval θ (detI G σ e hn) ≠ 0 }
      ⊆ (Set.range (fun θ => ambRealPt G σ e θ))
          ∩ { g : Fin n × Fin (e + 1) → ℝ | ambDetReal e (Ivtx σ hn) g ≠ 0 } := by
    rintro g ⟨θ, hθ, rfl⟩
    refine ⟨⟨θ, rfl⟩, ?_⟩
    simp only [Set.mem_setOf_eq] at hθ ⊢
    rwa [ambDetReal_ambRealPt]
  -- Push θ-density forward (`Continuous.range_subset_closure_image_dense`, general spaces);
  -- conclude via monotonicity of closure.
  have hrange : Set.range (fun θ => ambRealPt G σ e θ)
      ⊆ closure ((fun θ => ambRealPt G σ e θ) ''
          { θ : Fin n × ℕ → ℝ | MvPolynomial.eval θ (detI G σ e hn) ≠ 0 }) :=
    hcont.range_subset_closure_image_dense hSdense
  calc closure (Set.range (fun θ => ambRealPt G σ e θ))
      ⊆ closure (closure ((fun θ => ambRealPt G σ e θ) ''
          { θ : Fin n × ℕ → ℝ | MvPolynomial.eval θ (detI G σ e hn) ≠ 0 })) :=
        closure_mono hrange
    _ = closure ((fun θ => ambRealPt G σ e θ) ''
          { θ : Fin n × ℕ → ℝ | MvPolynomial.eval θ (detI G σ e hn) ≠ 0 }) := closure_closure
    _ ⊆ closure ((Set.range (fun θ => ambRealPt G σ e θ))
          ∩ { g : Fin n × Fin (e + 1) → ℝ | ambDetReal e (Ivtx σ hn) g ≠ 0 }) :=
        closure_mono himg_sub

set_option linter.unusedDecidableInType false in
/-- **`lem:hasGOR` image-glue as an equality of closures.** The closure of the
real image equals the closure of its intersection with the det-locus:
`closure (range φσ) = closure (range φσ ∩ L_σ)`. The `⊆` is
`dense_image_detLocus_in_closure_range`; the `⊇` is `closure_mono` of `range ∩ L ⊆ range`.

This is the precise sense in which "GOR is dense in GOR⁺_σ" (gorProof tex:304-312): the two sets
have the SAME Euclidean closure, so for the ATS (closure-equality) conclusion one may freely
restrict either image to the det-locus. -/
theorem closure_range_eq_closure_range_inter_detLocus
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (σ : Equiv.Perm (Fin n)) (e : ℕ) (hn : e + 1 ≤ n) :
    closure (Set.range (fun θ => ambRealPt G σ e θ))
      = closure ((Set.range (fun θ => ambRealPt G σ e θ))
          ∩ { g : Fin n × Fin (e + 1) → ℝ | ambDetReal e (Ivtx σ hn) g ≠ 0 }) := by
  apply le_antisymm
  · exact dense_image_detLocus_in_closure_range σ e hn
  · exact closure_mono Set.inter_subset_left

/-! ## The I-determinant locus is ORDERING-INDEPENDENT (gorProof tex:313-319, `lem:ats1`).

"Since the above lemma did not depend on the ordering, using `GOR` as the common dense subset,
we get [`lem:ats1`]." (gorProof tex:313-314.) When `σ`, `τ` share the SAME first-`D` vertex SET
but in a permuted order — `Ivtx τ = Ivtx σ ∘ w` for a permutation `w` of `Fin (e+1)` — the two
I-determinant polynomials differ only by `sign w = ±1` (row permutation), so their non-vanishing
loci coincide. This is the ordering-independence of the `G⁻`-GOR locus. -/

/-- The ambient I-determinant under a row permutation: if `Iv' = Iv ∘ w` for
`w : Perm (Fin (e+1))`, then `ambDetI e Iv' = sign w • ambDetI e Iv` (`Matrix.det_permute`). -/
theorem ambDetI_comp_perm (e : ℕ) (Iv : Fin (e + 1) → Fin n) (w : Equiv.Perm (Fin (e + 1))) :
    ambDetI e (Iv ∘ w) = (Equiv.Perm.sign w : ℝ) • ambDetI e Iv := by
  unfold ambDetI
  have hsub : (Matrix.of fun (a b : Fin (e + 1)) => MvPolynomial.X ((Iv ∘ w) a, b))
      = (Matrix.of fun (a b : Fin (e + 1)) =>
          (MvPolynomial.X (Iv a, b) : MvPolynomial (Fin n × Fin (e + 1)) ℝ)).submatrix w id := by
    ext a b; simp [Matrix.submatrix, Function.comp]
  rw [hsub, Matrix.det_permute, MvPolynomial.smul_eq_C_mul, map_intCast]

set_option linter.unusedDecidableInType false in
/-- **`lem:ats1` ordering-independence, gorProof tex:313-319.** If `σ`, `τ` share
the first-`D` vertex SET in permuted order (`Ivtx τ hn = Ivtx σ hn ∘ w`), their I-determinant
non-vanishing loci COINCIDE. The determinants differ only by the unit `sign w`, so vanishing is
the same. This makes the dense `G⁻`-GOR locus (`dense_ambDetLocus_Ivtx`) a COMMON dense subset
for `σ` and `τ` — the heart of `lem:ats1`. -/
theorem ambDetLocus_eq_of_ivtx_comp_perm {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {e : ℕ} {σ τ : Equiv.Perm (Fin n)} {hn : e + 1 ≤ n} (w : Equiv.Perm (Fin (e + 1)))
    (hIv : Ivtx τ hn = Ivtx σ hn ∘ w) :
    { g : Fin n × Fin (e + 1) → ℝ | ambDetReal e (Ivtx τ hn) g ≠ 0 }
      = { g : Fin n × Fin (e + 1) → ℝ | ambDetReal e (Ivtx σ hn) g ≠ 0 } := by
  ext g
  simp only [Set.mem_setOf_eq]
  -- `ambDetReal τ g = sign w * ambDetReal σ g`, and `sign w = ±1` is a unit.
  have key : ambDetReal e (Ivtx τ hn) g
      = (Equiv.Perm.sign w : ℝ) * ambDetReal e (Ivtx σ hn) g := by
    rw [ambDetReal, ambDetReal, hIv, ambDetI_comp_perm, MvPolynomial.smul_eval]
  have hsign : (Equiv.Perm.sign w : ℝ) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign w) with hh | hh <;> rw [hh] <;> norm_num
  rw [key, ne_eq, mul_eq_zero, not_or, ne_eq]
  exact and_iff_right hsign

end LSS
