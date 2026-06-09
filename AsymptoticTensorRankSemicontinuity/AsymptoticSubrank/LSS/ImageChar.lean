/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
/-
# LSS image characterization

Every general-position orthogonal representation arises from the
construction `φσ` by substituting real parameters (LSS Theorem 2.1 proof, tex:185-193).

This is the load-bearing piece flagged in `OrderInduction.transfers_firstD_base`: it supplies
the inclusion `GOR ⊆ range (ambRealPt σ)` — every GP orthogonal representation `f` of `G` is
the `φσ`-image of some real parameter point `θ`.

# Source

The argument is the induction on `n` in the proof of **LSS Theorem 2.1**
(`lovasz-saks-schrijver-orthrep-connectivity.tex` lines 185-193, tex:191) and its
restatement by **Gortler–Theran** (`GOR-LSS-2310.11565-gorProof.tex` lines 213-219).
Summarized: removing a vertex `v` gives a GP representation of `G-v`, realized from
`φ'` by the induction hypothesis; completing `{f(u_1),…,f(u_m)}` to a basis of
`f(v)^⊥` and substituting those basis vectors makes the remaining column parallel to
`f(v)`, so the parameter `y` can be chosen to realize `φ_v = f(v)`.

# Strategy

The single per-vertex realization step is exactly LSS tex:191, formalized as the SURJECTIVITY
lemma `NonEmpty.crossMinors_surj_orthogonal` (`crossMinors (w|x) = c • z` for prescribed
`z ⊥ w`, `z ≠ 0`). The induction on `n` becomes a greedy sweep over the vertices in `σ`-order:
maintaining `realPhi σ θ u = f u` for all `u` at `σ`-position `< p`, we realize the vertex at
position `p` by setting its scalar `y_v = 1/c` and its fresh columns to the basis-completing
vectors `x` from `crossMinors_surj_orthogonal`, applied with `w = f(preceding non-neighbours)`,
`z = f(v)`. Per-vertex-disjoint variable namespacing (`realPhi_congr`) means the new slots do
not disturb the earlier vectors.

This uses the following lemmas from
`NonEmpty.exists_eval_linearIndependent_Ivtx`:
* `eval_phiσ` — eval-commutation `eval θ ∘ phiσ = realPhi θ`;
* `realPhi_congr` — locality of `realPhi` in the per-vertex variable slots;
* `crossMinors_surj_orthogonal` — the per-vertex realization;
* the `θ'` fresh-slot decoding (`/`, `%`) reconstructing the columns `x`.

The hypotheses on `f`:
* `hOR` — `f` is an orthogonal representation: non-adjacent `u v` have `∑ c, f u c * f v c = 0`.
* `hGP` — `f` is in general position: any `e+1` vertices have linearly independent images.

The `hcard : (precNonNbrσ G σ v).card ≤ e` bound is LSS's `m ≤ d-1` (tex:182, "clearly
`m ≤ d-1`"): the preceding non-neighbours fit in the `e = d-1` free columns.

# Contents

* `gp_indep_of_inj` — GP ⟹ any injective family of `≤ e+1` vertices has independent images.
* `gp_ne_zero` — GP ⟹ `f v ≠ 0` for every vertex.
* `exists_realPhi_eq` — the greedy sweep: `∃ θ, ∀ v, realPhi σ θ v = f v`.
* `gor_subset_image` — **headline**: `∃ θ, ∀ v c, eval θ (phiσ σ v c) = f v c`.
* `gor_mem_range_ambRealPt` — the `range (ambRealPt σ)` form that plugs into
  `OrderInduction.transfers_of_closure_eq` (`GOR ⊆ range (ambRealPt σ)`).
-/
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.LSS.Construction
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.LSS.NonEmpty
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.LSS.ClosureReduction

namespace LSS

open Matrix Finset MvPolynomial

variable {n : ℕ}

/-! ## General-position consequences of `f`.

`hGP` says any `e+1` vertices have linearly independent images. We extract two consequences:
a subfamily of `≤ e+1` distinct vertices is independent, and each single `f v ≠ 0`. -/

/-- **GP subfamily independence.** If `f` is in general position (`hGP`: any `e+1` vertices are
independent) and `n ≥ e+1`, then any injective family of `m ≤ e+1` vertices `g : Fin m → Fin n`
has linearly independent images `fun a => f (g a)`.

LSS tex:191 uses exactly this at `m = card{u_1,…,u_m}`: "`f(u_1),…,f(u_m)` are linearly
independent" (a subfamily of the GP rep). -/
theorem gp_indep_of_inj {e : ℕ} (hn : e + 1 ≤ n) (f : Fin n → (Fin (e + 1) → ℝ))
    (hGP : ∀ s : Finset (Fin n), s.card = e + 1 →
      LinearIndependent ℝ (fun i : (↑s : Set (Fin n)) => f i.val))
    {m : ℕ} (hm : m ≤ e + 1) (g : Fin m → Fin n) (hg : Function.Injective g) :
    LinearIndependent ℝ (fun a : Fin m => f (g a)) := by
  classical
  -- The image finset of `g` (card `m` since `g` injective), extended to a card-`(e+1)` set `s`.
  set T : Finset (Fin n) := Finset.image g Finset.univ with hT
  have hTcard : T.card = m := by
    rw [hT, Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin]
  have hTle : T.card ≤ e + 1 := by rw [hTcard]; exact hm
  obtain ⟨s, hTs, hscard⟩ := Finset.exists_superset_card_eq hTle (by
    rw [Fintype.card_fin]; exact hn)
  -- Independence of `f` restricted to the subtype `↑s`.
  have hs := hGP s hscard
  -- The map `Fin m → ↑s`, `a ↦ ⟨g a, _⟩`, is injective; compose.
  have hmem : ∀ a : Fin m, g a ∈ s := by
    intro a; apply hTs; rw [hT]; exact Finset.mem_image_of_mem g (Finset.mem_univ a)
  let ι : Fin m → (↑s : Set (Fin n)) := fun a => ⟨g a, hmem a⟩
  have hιinj : Function.Injective ι := by
    intro a b hab
    apply hg
    exact congrArg Subtype.val hab
  have hcomp := hs.comp ι hιinj
  -- `(fun i : ↑s => f i.val) ∘ ι = fun a => f (g a)`.
  have : (fun i : (↑s : Set (Fin n)) => f i.val) ∘ ι = fun a : Fin m => f (g a) := by
    funext a; rfl
  rwa [this] at hcomp

/-- **GP nonvanishing.** If `f` is in general position and `n ≥ e+1`, then `f v ≠ 0` for every
vertex `v`. LSS tex:191 needs `f(v) ≠ 0` to set `y_v = 1/c` (the cross-product is a nonzero
multiple of `f(v)`). -/
theorem gp_ne_zero {e : ℕ} (hn : e + 1 ≤ n) (f : Fin n → (Fin (e + 1) → ℝ))
    (hGP : ∀ s : Finset (Fin n), s.card = e + 1 →
      LinearIndependent ℝ (fun i : (↑s : Set (Fin n)) => f i.val))
    (v : Fin n) : f v ≠ 0 := by
  have hindep : LinearIndependent ℝ (fun _ : Fin 1 => f v) :=
    gp_indep_of_inj hn f hGP (by omega) (fun _ => v) (by
      intro a b _; exact Subsingleton.elim a b)
  have := hindep.ne_zero (0 : Fin 1)
  simpa using this

/-! ## The greedy sweep realizing `f`.

We build the parameter point `θ` by induction on the `σ`-prefix length `p`: maintaining
`realPhi σ θ u = f u` for all `u` at `σ`-position `< p`. At step `p → p+1` the new vertex
`v` at position `p` is realized by `crossMinors_surj_orthogonal` (LSS tex:191); the earlier
vertices are left fixed by `realPhi_congr` (per-vertex variable namespacing). -/

/-- **The greedy realization (the heart, LSS tex:185-193).** For a graph `G`, ordering `σ`,
dimension `D = e+1 ≤ n`, and a general-position orthogonal representation `f` (`hOR`, `hGP`)
with the preceding-non-neighbour bound `hcard`, there is a real parameter point `θ` whose real
construction `realPhi σ θ` equals `f` at every vertex.

Proof: greedy induction on the `σ`-prefix length, realizing each vertex via
`crossMinors_surj_orthogonal` exactly as `NonEmpty.exists_eval_linearIndependent_Ivtx` realizes
its rows, but onto the PRESCRIBED target `f v` instead of an arbitrary escape vector. -/
theorem exists_realPhi_eq (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Equiv.Perm (Fin n)) (e : ℕ) (hn : e + 1 ≤ n)
    (hcard : ∀ v, (precNonNbrσ G σ v).card ≤ e)
    (f : Fin n → (Fin (e + 1) → ℝ))
    (hOR : ∀ u v, u ≠ v → ¬ G.Adj u v → ∑ c, f u c * f v c = 0)
    (hGP : ∀ s : Finset (Fin n), s.card = e + 1 →
      LinearIndependent ℝ (fun i : (↑s : Set (Fin n)) => f i.val)) :
    ∃ θ : Fin n × ℕ → ℝ, ∀ v : Fin n, realPhi G σ e θ v = f v := by
  classical
  -- Greedy induction on the prefix length `p` (number of vertices placed so far).
  suffices haux : ∀ p : ℕ, ∃ θ : Fin n × ℕ → ℝ,
      ∀ u : Fin n, (σ.symm u).val < p → realPhi G σ e θ u = f u by
    obtain ⟨θ, hθ⟩ := haux n
    exact ⟨θ, fun v => hθ v (by exact (σ.symm v).isLt)⟩
  intro p
  induction p with
  | zero => exact ⟨fun _ => 0, fun u hu => by omega⟩
  | succ p ih =>
      obtain ⟨θ, hθ⟩ := ih
      -- If position `p` is out of range, nothing new to place.
      by_cases hpn : p < n
      · -- The vertex at position `p`.
        set v : Fin n := σ ⟨p, hpn⟩ with hv
        have hvpos : (σ.symm v).val = p := by rw [hv]; simp
        -- The preceding non-neighbour columns of `v`, as a previous-row family.
        set len : ℕ := (precList G σ v).length with hlen
        have hlencard : len = (precNonNbrσ G σ v).card := by
          rw [hlen]; unfold precList; rw [Finset.length_sort]
        have hlen_le_e : len ≤ e := by rw [hlencard]; exact hcard v
        -- every preceding non-neighbour has `σ`-position `< p`.
        have hprec_pos : ∀ u ∈ precList G σ v, (σ.symm u).val < p := by
          intro u hu
          have huP : u ∈ precNonNbrσ G σ v := by
            have : u ∈ (precNonNbrσ G σ v).sort (· ≤ ·) := by simpa [precList] using hu
            simpa using (Finset.mem_sort (· ≤ ·)).1 this
          have := precNonNbrσ_lt G σ huP
          rw [hvpos] at this; exact this
        -- the non-neighbour list entries.
        have hget_pos : ∀ j : Fin len, ((σ.symm ((precList G σ v).get j)).val) < p :=
          fun j => hprec_pos _ (List.get_mem _ _)
        -- `w j = f (precList[j])` (= IH-realized previous row, but here directly `f`).
        set pl : Fin len → Fin n := fun j => (precList G σ v).get j with hpl
        have hplinj : Function.Injective pl := by
          intro j₁ j₂ heq
          exact (List.nodup_iff_injective_get.1 (by
            unfold precList; exact Finset.sort_nodup _ _)) heq
        set w : Fin len → (Fin (e + 1) → ℝ) := fun j => f (pl j) with hw
        -- `w` independent (subfamily of the GP `f`).
        have hwindep : LinearIndependent ℝ w := by
          rw [hw]
          exact gp_indep_of_inj hn f hGP (by omega) pl hplinj
        -- `f v ≠ 0` (GP).
        have hfv0 : f v ≠ 0 := gp_ne_zero hn f hGP v
        -- `f v ⊥` each non-neighbour column (OR, since `pl j` are non-neighbours of `v`).
        have hperp : ∀ j : Fin len, ∑ a, (f v) a * w j a = 0 := by
          intro j
          -- `pl j ∈ precNonNbrσ G σ v`, so `¬ G.Adj v (pl j)` and `pl j ≠ v`.
          have hmem : pl j ∈ precList G σ v := List.get_mem _ _
          have huP : pl j ∈ precNonNbrσ G σ v := by
            have : pl j ∈ (precNonNbrσ G σ v).sort (· ≤ ·) := by simpa [precList] using hmem
            simpa using (Finset.mem_sort (· ≤ ·)).1 this
          have hnadj : ¬ G.Adj v (pl j) := ((mem_precNonNbrσ G σ).1 huP).2
          have hne : v ≠ pl j := by
            intro h
            have := precNonNbrσ_lt G σ huP
            rw [← h] at this; exact (lt_irrefl _ this)
          have := hOR v (pl j) hne hnadj
          rw [hw]; exact this
        -- (N1) surjectivity: free columns `x` and a nonzero scale `c` with
        -- `crossMinors (w|x) = c • (f v)`.
        obtain ⟨x, c, hc, hcross⟩ :=
          crossMinors_surj_orthogonal hlen_le_e w hwindep (f v) hfv0 hperp
        -- **Define `θ'`**: `θ` with vertex `v`'s slots overwritten — scalar `y_v = 1/c` and the
        -- fresh columns set to `x`. Slot `1 + (k*(e+1) + ρ)` carries `x_k ρ` (decode via `/`,`%`).
        set θ' : Fin n × ℕ → ℝ :=
          fun q =>
            if q.1 = v then
              (match q.2 with
               | 0 => 1 / c
               | Nat.succ s =>
                   if h : s / (e + 1) < e - len then
                     x ⟨s / (e + 1), h⟩ ⟨s % (e + 1), Nat.mod_lt _ (by omega)⟩
                   else 0)
            else θ q with hθ'
        -- `θ'` differs from `θ` only at vertex `v` (position `p`), so it leaves earlier rows fixed.
        have hreal_fix : ∀ u' : Fin n, (σ.symm u').val < p →
            realPhi G σ e θ' u' = realPhi G σ e θ u' := by
          intro u' hu'
          apply realPhi_congr
          intro w' hw' s
          have hw'ne : w' ≠ v := by
            intro h; rw [h, hvpos] at hw'; omega
          rw [hθ']; simp only [hw'ne, if_false]
        -- the matrix of `realPhi θ' v` equals the (N1) matrix `(w | x)`.
        have hmateq : (Matrix.of fun (a : Fin (e + 1)) (j : Fin e) =>
              match (precList G σ v)[j.val]? with
              | some u =>
                if (σ.symm u).val < (σ.symm v).val then realPhi G σ e θ' u a else 0
              | none => θ' (v, 1 + (((j.val - (precList G σ v).length)) * (e + 1) + a.val)))
            = (Matrix.of fun (a : Fin (e + 1)) (cc : Fin e) =>
                if h : cc.val < len then w ⟨cc.val, h⟩ a
                else x ⟨cc.val - len, by omega⟩ a) := by
          funext a j
          simp only [Matrix.of_apply]
          by_cases hjlen : j.val < len
          · -- column inside `precList`: reads a previous non-neighbour row, fixed by `θ'`.
            have hsome : (precList G σ v)[j.val]? = some ((precList G σ v).get ⟨j.val, hjlen⟩) := by
              rw [List.getElem?_eq_getElem hjlen]; rfl
            rw [hsome]
            have hposu : (σ.symm ((precList G σ v).get ⟨j.val, hjlen⟩)).val < (σ.symm v).val := by
              rw [hvpos]; exact hget_pos ⟨j.val, hjlen⟩
            simp only [hposu, if_true, hjlen, dif_pos]
            rw [hreal_fix _ (by rw [hvpos] at hposu; exact hposu)]
            -- now `realPhi θ (precList[j]) = f (precList[j]) = w ⟨j,_⟩`.
            have hposu' : (σ.symm ((precList G σ v).get ⟨j.val, hjlen⟩)).val < p := by
              rw [hvpos] at hposu; exact hposu
            rw [hθ _ hposu']
          · -- fresh column: reads `θ'` at the decoded slot, which is `x⟨j-len,_⟩ a`.
            have hnone : (precList G σ v)[j.val]? = none := by
              rw [List.getElem?_eq_none_iff]; omega
            rw [hnone]
            simp only [hjlen, dif_neg, not_false_iff]
            rw [hθ']
            simp only [if_true]
            have hs : 1 + ((j.val - len) * (e + 1) + a.val)
                = Nat.succ ((j.val - len) * (e + 1) + a.val) := by omega
            rw [hs]
            have hdiv : ((j.val - len) * (e + 1) + a.val) / (e + 1) = j.val - len := by
              rw [add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < e + 1),
                Nat.div_eq_of_lt a.isLt, zero_add]
            have hmod : ((j.val - len) * (e + 1) + a.val) % (e + 1) = a.val := by
              rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a.isLt]
            have hcond : ((j.val - len) * (e + 1) + a.val) / (e + 1) < e - len := by
              rw [hdiv]; omega
            change (if h : ((j.val - len) * (e + 1) + a.val) / (e + 1) < e - len then
                    x ⟨((j.val - len) * (e + 1) + a.val) / (e + 1), h⟩
                      ⟨((j.val - len) * (e + 1) + a.val) % (e + 1), Nat.mod_lt _ (by omega)⟩
                  else 0) = x ⟨j.val - len, by omega⟩ a
            rw [dif_pos hcond]
            congr 1
            · exact Fin.ext hdiv
            · exact Fin.ext hmod
        -- `θ' (v,0) = 1/c`.
        have hθ'v0 : θ' (v, 0) = 1 / c := by rw [hθ']; simp
        -- Hence `realPhi θ' v = (1/c) • crossMinors(w|x) = (1/c) • (c • f v) = f v`.
        have hrealv : realPhi G σ e θ' v = f v := by
          funext bb
          rw [realPhi_eq]
          rw [hθ'v0]
          -- `crossMinors (realPhi matrix) bb = crossMinors (w|x) bb = (c • f v) bb`.
          -- `hmateq` proves `realPhi matrix = (w|x)` (its LHS is defeq to the goal's matrix).
          have hcross' :
              crossMinors (Matrix.of fun (a : Fin (e + 1)) (cc : Fin e) =>
                if h : cc.val < len then w ⟨cc.val, h⟩ a
                else x ⟨cc.val - len, by omega⟩ a) bb = (c • f v) bb := by
            rw [hcross]
          calc 1 / c * crossMinors (Matrix.of fun (a : Fin (e + 1)) (j : Fin e) =>
                match (precList G σ v)[j.val]? with
                | some u =>
                  if (σ.symm u).val < (σ.symm v).val then realPhi G σ e θ' u a else 0
                | none => θ' (v, 1 + (((j.val - (precList G σ v).length)) * (e + 1) + a.val))) bb
              = 1 / c * (c • f v) bb := by
                rw [congrArg (fun M => crossMinors M bb) hmateq, hcross']
            _ = f v bb := by
                simp only [Pi.smul_apply, smul_eq_mul]; field_simp
      -- assemble `θ'`, realizing all vertices of position `< p+1`.
        refine ⟨θ', ?_⟩
        intro u' hu'
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu' with hlt | heq
        · -- earlier vertex: fixed by `θ'`, realized by IH.
          rw [hreal_fix u' hlt, hθ u' hlt]
        · -- vertex at position `p` is exactly `v`.
          have : u' = v := by
            rw [hv]
            apply σ.symm.injective
            apply Fin.ext
            rw [heq]; simp
          rw [this]; exact hrealv
      · -- `p ≥ n`: positions `< p+1` are the same as positions `< p` (all `< n ≤ p`), use IH.
        refine ⟨θ, ?_⟩
        intro u hu
        exact hθ u (by have := (σ.symm u).isLt; omega)

/-! ## The headline image-characterization. -/

/-- **Theorem 2.1 image-characterization** (LSS tex:185-193, gorProof tex:213-219).
Every general-position orthogonal representation `f` of `G` arises from the construction `φσ`
by substituting real parameters: there is a real point `θ` with
`eval θ (phiσ G σ e v c) = f v c` for all `v, c`.

Hypotheses (exactly LSS's): `hOR` — `f` is an OR (non-adjacent vertices map to orthogonal
vectors); `hGP` — `f` is in general position (any `D = e+1` vertices are linearly independent);
`hcard` — each vertex has `≤ e = D-1` preceding non-neighbours (LSS tex:182 "`m ≤ d-1`");
`hn : e+1 ≤ n` (there are at least `D` vertices, the standing assumption of the `D`-vertex
base; cf. `Ivtx`/`detI`'s `hn`).

Proof: `exists_realPhi_eq` builds `θ` with `realPhi σ θ v = f v`; eval-commutation
`eval_phiσ` turns `realPhi σ θ v` into `fun c => eval θ (phiσ G σ e v c)`. -/
theorem gor_subset_image (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (e : ℕ) (σ : Equiv.Perm (Fin n)) (hn : e + 1 ≤ n)
    (hcard : ∀ v, (precNonNbrσ G σ v).card ≤ e)
    (f : Fin n → (Fin (e + 1) → ℝ))
    (hOR : ∀ u v, u ≠ v → ¬ G.Adj u v → ∑ c, f u c * f v c = 0)
    (hGP : ∀ s : Finset (Fin n), s.card = e + 1 →
      LinearIndependent ℝ (fun i : (↑s : Set (Fin n)) => f i.val)) :
    ∃ θ : Fin n × ℕ → ℝ, ∀ v c, MvPolynomial.eval θ (phiσ G σ e v c) = f v c := by
  obtain ⟨θ, hθ⟩ := exists_realPhi_eq G σ e hn hcard f hOR hGP
  refine ⟨θ, fun v c => ?_⟩
  have := eval_phiσ G σ e θ v
  -- `(fun c => eval θ (phiσ v c)) = realPhi σ θ v = f v`.
  have hpt : (fun c => MvPolynomial.eval θ (phiσ G σ e v c)) = f v := by
    rw [this]; exact hθ v
  exact congrFun hpt c

/-- **`GOR ⊆ range (ambRealPt σ)`** — the form that plugs into
`OrderInduction.transfers_of_closure_eq` (and hence `transfers_firstD_base`). The uncurried
representation `fun q => f q.1 q.2 : Fin n × Fin (e+1) → ℝ` lies in the real ambient image
`range (ambRealPt G σ e)`.

This is exactly the inclusion `GOR ⊆ range (ambRealPt σ)` flagged as the load-bearing piece in
`OrderInduction.transfers_firstD_base`: since `ambRealPt G σ e θ q = eval θ (ambSub G σ e q)
= eval θ (phiσ G σ e q.1 q.2)`, the point `θ` from `gor_subset_image` exhibits `f` (uncurried)
as `ambRealPt G σ e θ`. -/
theorem gor_mem_range_ambRealPt (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (e : ℕ) (σ : Equiv.Perm (Fin n)) (hn : e + 1 ≤ n)
    (hcard : ∀ v, (precNonNbrσ G σ v).card ≤ e)
    (f : Fin n → (Fin (e + 1) → ℝ))
    (hOR : ∀ u v, u ≠ v → ¬ G.Adj u v → ∑ c, f u c * f v c = 0)
    (hGP : ∀ s : Finset (Fin n), s.card = e + 1 →
      LinearIndependent ℝ (fun i : (↑s : Set (Fin n)) => f i.val)) :
    (fun q : Fin n × Fin (e + 1) => f q.1 q.2) ∈
      Set.range (fun θ => ambRealPt G σ e θ) := by
  obtain ⟨θ, hθ⟩ := gor_subset_image G e σ hn hcard f hOR hGP
  refine ⟨θ, ?_⟩
  funext q
  -- `ambRealPt G σ e θ q = eval θ (ambSub G σ e q) = eval θ (phiσ G σ e q.1 q.2) = f q.1 q.2`.
  change MvPolynomial.eval θ (ambSub G σ e q) = f q.1 q.2
  rw [ambSub]
  exact hθ q.1 q.2

end LSS
