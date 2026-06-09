/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import Mathlib.Computability.Halting
import Mathlib.Data.PNat.Basic

/-!
# Computable-level list operations

Mathlib provides `List.foldl`/`List.map`/`List.all` closure lemmas for
`Primrec` (`Primrec.list_foldl` etc.) but not for `Computable`. Over a
computable field the arithmetic operations are only `Computable`, not
`Primrec`, so computable algorithms that sum or compare field elements
stored in lists need the `Computable`-level closures. They follow from
`Computable.nat_rec` by recursion on the list length, reading the entries
off with `Computable.list_getElem?`.

We also provide the `Primcodable ℕ+` instance used to code tensor formats.
-/

namespace Computable

variable {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]

private theorem foldl_concat_eq_append_map {γ δ : Type*} (l : List γ) (f : γ → δ)
    (acc : List δ) :
    l.foldl (fun s b => s ++ [f b]) acc = acc ++ l.map f := by
  induction l generalizing acc with
  | nil => simp
  | cons b l IH =>
      simp [IH, List.append_assoc]

private theorem foldl_and_eq_and_all {γ : Type*} (l : List γ) (p : γ → Bool)
    (acc : Bool) :
    l.foldl (fun s b => s && p b) acc = (acc && l.all p) := by
  induction l generalizing acc with
  | nil => cases acc <;> rfl
  | cons b l IH =>
      cases acc <;> cases p b <;> simp [IH]

private theorem zipWith_eq_map_range_getD {γ δ ε : Type*} (g : γ → δ → ε)
    (l₁ : List γ) (l₂ : List δ) (d₁ : γ) (d₂ : δ) :
    List.zipWith g l₁ l₂ =
      (List.range (min l₁.length l₂.length)).map fun i =>
        g (l₁.getD i d₁) (l₂.getD i d₂) := by
  induction l₁ generalizing l₂ with
  | nil =>
      simp
  | cons a l₁ ih =>
      cases l₂ with
      | nil => simp
      | cons b l₂ =>
          rw [List.zipWith_cons_cons, ih]
          apply List.ext_getElem
          · simp
          · intro n h₁ h₂
            cases n with
            | zero => simp
            | succ n =>
                simp at h₁ h₂ ⊢

/-- `Computable` closure of `List.foldl` (the `Computable` analogue of
`Primrec.list_foldl`): recursion on the list length via `Computable.nat_rec`,
reading entries with `Computable.list_getElem?`. -/
theorem list_foldl {f : α → List β} {g : α → σ} {h : α → σ × β → σ}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable fun a => (f a).foldl (fun s b => h a (s, b)) (g a) := by
  let step : α → ℕ × σ → σ :=
    fun a p => Option.casesOn ((f a)[p.1]?) p.2 (fun b => h a (p.2, b))
  have hstep : Computable₂ step := by
    have hstep' :=
      Computable.option_casesOn
        (o := fun x : α × (ℕ × σ) => (f x.1)[x.2.1]?)
        (f := fun x : α × (ℕ × σ) => x.2.2)
        (g := fun x b => h x.1 (x.2.2, b))
      (Computable.list_getElem?.comp (hf.comp Computable.fst)
        (Computable.fst.comp (Computable.snd : Computable (fun x : α × (ℕ × σ) => x.2))))
      (Computable.snd.comp (Computable.snd : Computable (fun x : α × (ℕ × σ) => x.2)))
      (hh.comp
        (Computable.fst.comp Computable.fst)
        (Computable.pair
          (Computable.snd.comp
            (Computable.snd.comp
              (Computable.fst : Computable (fun x : (α × (ℕ × σ)) × β => x.1))))
          Computable.snd)).to₂
    exact hstep'.to₂.of_eq fun x => by
      rcases x with ⟨a, p⟩
      rfl
  have hrec := Computable.nat_rec (Computable.list_length.comp hf) hg hstep
  refine hrec.of_eq fun a => ?_
  let l := f a
  let x := g a
  let step' : ℕ → σ → σ :=
    fun n s => Option.casesOn (l[n]?) s (fun b => h a (s, b))
  suffices H : ∀ n, Nat.rec x (fun n IH => step' n IH) n =
      (l.take n).foldl (fun s b => h a (s, b)) x by
    simpa [l, x, step', List.take_length] using H l.length
  intro n
  induction n with
  | zero => rfl
  | succ n IH =>
      rw [List.take_add_one, List.foldl_append]
      cases hget : l[n]? with
      | none => simp [step', IH, hget]
      | some b => simp [step', IH, hget]

/-- `Computable` closure of `List.map` (the `Computable` analogue of
`Primrec.list_map`): `List.map` is a `List.foldl` accumulating with
`List.concat`. -/
theorem list_map {f : α → List β} {g : α → β → σ}
    (hf : Computable f) (hg : Computable₂ g) :
    Computable fun a => (f a).map (g a) := by
  have hfold : Computable fun a =>
      (f a).foldl (fun s b => s ++ [g a b]) ([] : List σ) :=
    Computable.list_foldl hf (Computable.const []) <| Computable.to₂ <|
      Computable.list_concat.comp
        (Computable.fst.comp (Computable.snd : Computable (fun x : α × (List σ × β) => x.2)))
        (hg.comp Computable.fst
          (Computable.snd.comp
            (Computable.snd : Computable (fun x : α × (List σ × β) => x.2))))
  refine hfold.of_eq fun a => ?_
  simpa using (foldl_concat_eq_append_map (f a) (g a) ([] : List σ))

/-- `Computable` closure of `List.zipWith`. -/
theorem list_zipWith {γ : Type*} [Primcodable γ] {f : α → List β}
    {g : α → List γ} {h : α → β → γ → σ} (dβ : β) (dγ : γ)
    (hf : Computable f) (hg : Computable g)
    (hh : Computable fun x : α × β × γ => h x.1 x.2.1 x.2.2) :
    Computable fun a => List.zipWith (h a) (f a) (g a) := by
  have hlen : Computable fun a => min (f a).length (g a).length :=
    Primrec.nat_min.to_comp.comp (Computable.list_length.comp hf)
      (Computable.list_length.comp hg)
  have hterm : Computable₂ fun a i => h a ((f a).getD i dβ) ((g a).getD i dγ) := by
    have hleft : Computable fun x : α × ℕ => (f x.1).getD x.2 dβ :=
      (Primrec.list_getD dβ).to_comp.comp (hf.comp Computable.fst) Computable.snd
    have hright : Computable fun x : α × ℕ => (g x.1).getD x.2 dγ :=
      (Primrec.list_getD dγ).to_comp.comp (hg.comp Computable.fst) Computable.snd
    exact (hh.comp
      (Computable.pair Computable.fst (Computable.pair hleft hright))).to₂
  have hmap : Computable fun a =>
      (List.range (min (f a).length (g a).length)).map
        fun i => h a ((f a).getD i dβ) ((g a).getD i dγ) :=
    Computable.list_map (Primrec.list_range.to_comp.comp hlen) hterm
  exact hmap.of_eq fun a => by
    rw [zipWith_eq_map_range_getD (h a) (f a) (g a) dβ dγ]

/-- `Computable` closure of `List.sum`. -/
theorem list_sum {M : Type*} [Primcodable M] [AddMonoid M] {f : α → List M}
    (hadd : Computable₂ ((· + ·) : M → M → M)) (hf : Computable f) :
    Computable fun a => (f a).sum := by
  have hfold : Computable fun a => (f a).foldl (fun s b => s + b) 0 :=
    Computable.list_foldl hf (Computable.const 0) <| Computable.to₂ <|
      hadd.comp
        (Computable.fst.comp (Computable.snd : Computable (fun x : α × (M × M) => x.2)))
        (Computable.snd.comp (Computable.snd : Computable (fun x : α × (M × M) => x.2)))
  exact hfold.of_eq fun a => by
    rw [List.sum_eq_foldl]

/-- `Computable` closure of `List.prod`. -/
theorem list_prod {M : Type*} [Primcodable M] [Monoid M] {f : α → List M}
    (hmul : Computable₂ ((· * ·) : M → M → M)) (hf : Computable f) :
    Computable fun a => (f a).prod := by
  have hfold : Computable fun a => (f a).foldl (fun s b => s * b) 1 :=
    Computable.list_foldl hf (Computable.const 1) <| Computable.to₂ <|
      hmul.comp
        (Computable.fst.comp (Computable.snd : Computable (fun x : α × (M × M) => x.2)))
        (Computable.snd.comp (Computable.snd : Computable (fun x : α × (M × M) => x.2)))
  exact hfold.of_eq fun a => by
    rw [List.prod_eq_foldl]

/-- `Computable` closure of `List.all`. -/
theorem list_all {f : α → List β} {g : α → β → Bool}
    (hf : Computable f) (hg : Computable₂ g) :
    Computable fun a => (f a).all (g a) := by
  have hfold : Computable fun a =>
      (f a).foldl (fun acc b => acc && g a b) true :=
    Computable.list_foldl hf (Computable.const true) <| Computable.to₂ <|
      Primrec.and.to_comp.comp
        (Computable.fst.comp (Computable.snd : Computable (fun x : α × (Bool × β) => x.2)))
        (hg.comp Computable.fst
          (Computable.snd.comp
            (Computable.snd : Computable (fun x : α × (Bool × β) => x.2))))
  refine hfold.of_eq fun a => ?_
  simpa using (foldl_and_eq_and_all (f a) (g a) true)

end Computable

/-- The first value found by `Nat.rfindOpt` is the unique sound answer. -/
theorem mem_rfindOpt_of_sound {σ : Type*} {f : ℕ → Option σ} {v : σ}
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

/-- **Computability by sound, total search**: if a computable trial function
`f a : ℕ → Option σ` only ever returns the value `g a` (soundness) and returns
it for some trial on every input (totality), then `g` is computable. This is
the engine behind all unbounded searches in this development (deciding by
parallel witnesses, computable field inverses, rank/unrank of enumerations). -/
theorem _root_.Computable.of_total_sound_search {α σ : Type*} [Primcodable α]
    [Primcodable σ] {f : α → ℕ → Option σ} {g : α → σ}
    (hf : Computable₂ f)
    (hsound : ∀ a n b, f a n = some b → b = g a)
    (htotal : ∀ a, ∃ n b, f a n = some b) : Computable g := by
  have hpart := Partrec.rfindOpt hf
  exact hpart.of_eq_tot fun a =>
    mem_rfindOpt_of_sound (fun n b hn => hsound a n b hn) (htotal a)

/-- Positive natural numbers are coded as the subtype `{n : ℕ // 0 < n}`
(this is the definition of `ℕ+`); the predicate `0 < n` is primitive
recursive. -/
instance PNat.instPrimcodable : Primcodable ℕ+ :=
  Primcodable.subtype (Primrec.nat_lt.comp (Primrec.const 0) Primrec.id)

/-- The coercion `ℕ+ → ℕ` is computable (it is the subtype projection, which
preserves codes). -/
theorem PNat.computable_val : Computable fun n : ℕ+ => (n : ℕ) := by
  exact Computable.encode_iff.mp (Computable.encode.of_eq fun _ => rfl)
