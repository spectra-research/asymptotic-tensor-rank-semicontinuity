/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
import AsymptoticTensorRankSemicontinuity.ZariskiSublevel
import AsymptoticTensorRankSemicontinuity.SpectrumWellOrdered
import AsymptoticTensorRankSemicontinuity.DiscreteFromBelow
import AsymptoticTensorRankSemicontinuity.EuclideanClosed
import AsymptoticTensorRankSemicontinuity.AsymptoticSubrank.Main
import AsymptoticTensorRankSemicontinuity.AlgorithmUniform
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.ComputableFieldInstances
import AsymptoticTensorRankSemicontinuity.Prerequisites.Computability.AlgebraicClosure

/-!
# Main results

The main results of *Asymptotic tensor rank is characterized by polynomials*
(Christandl, Hoeberechts, Nieuwboer, Vrana, Zuiddam, arXiv:2411.15789).
-/

namespace Semicontinuity.MainResults

universe u v

variable {F : Type u} [Field F]

/-- **Theorem 1.1.** Over a computable field (in the sense of Rabin), for
every `k` and `r` there is an algorithm that, given the format `d` and a
`k`-tensor `T ∈ F^{d₁} ⊗ ⋯ ⊗ F^{d_k}`, decides whether `asympRank T ≤ r`.
The algorithm is uniform in the format `d` (not in `r`). The paper states
the theorem for `k ≥ 3`; the formalized statement has no constraint on `k`
(for `k = 0` it holds trivially, `asympRank` being `0` there by convention). -/
theorem computablePred_asympRank_le {k : ℕ} [Primcodable F] [ComputableField F]
    (r : ℝ) :
    ComputablePred fun x : Σ d : Fin k → ℕ+, KTensor F d =>
      asympRank x.2 ≤ r :=
  Semicontinuity.computablePred_asympRank_le_uniform r

-- Theorem 1.1 applies for example to the rationals. (Over the prime fields
-- the theorem is much easier; that instance is a sanity check.)
example (k : ℕ) (r : ℝ) :
    ComputablePred fun x : Σ d : Fin k → ℕ+, KTensor ℚ d =>
      asympRank x.2 ≤ r :=
  computablePred_asympRank_le r

example (p k : ℕ) [Fact p.Prime] (r : ℝ) :
    ComputablePred fun x : Σ d : Fin k → ℕ+, KTensor (ZMod p) d =>
      asympRank x.2 ≤ r :=
  computablePred_asympRank_le r

/-- **Theorem 1.1 over the algebraic closure of `ℚ`.** Rabin's computable
algebraic closure `ComputableAlgebraicClosure ℚ = ℚ̄` is itself a computable
field (the formalization of Rabin 1960, Theorem 7, `rabin.tex`:388-408), so
Theorem 1.1 applies: asymptotic tensor rank over `ℚ̄` is decidable.  This is
the first algebraically closed field to which the algorithm applies. -/
theorem computablePred_asympRank_le_algClosureRat (k : ℕ) (r : ℝ) :
    ComputablePred fun x : Σ d : Fin k → ℕ+,
        KTensor (Semicontinuity.GreedyIdeal.ComputableAlgebraicClosure ℚ) d =>
      asympRank x.2 ≤ r :=
  computablePred_asympRank_le r

/-- **Theorem 1.1 over the algebraic closure of `𝔽_p`.** For every prime `p`,
Rabin's computable algebraic closure `ComputableAlgebraicClosure (ZMod p) = 𝔽̄_p`
of the prime field is a computable field, so Theorem 1.1 applies: asymptotic
tensor rank over `𝔽̄_p` is decidable — uniformly in `p`. -/
theorem computablePred_asympRank_le_algClosureZMod (p : ℕ) [Fact p.Prime] (k : ℕ) (r : ℝ) :
    ComputablePred fun x : Σ d : Fin k → ℕ+,
        KTensor (Semicontinuity.GreedyIdeal.ComputableAlgebraicClosure (ZMod p)) d =>
      asympRank x.2 ≤ r :=
  computablePred_asympRank_le r

/-- **Theorem 1.2.** Over any field, on any format of order-`k` tensors, the
sublevel set `{T : asympRank T ≤ r}` is Zariski-closed. (The paper states
the theorem for `k ≥ 3`; the formalization proves it for every `k ≥ 1`.) -/
theorem isZariskiClosed_asympRank_sublevel {k : ℕ} {d : Fin k → ℕ+}
    (hk : 1 ≤ k) (r : ℝ) :
    IsZariskiClosed (F := F) { T : KTensor F d | asympRank T ≤ r } :=
  Semicontinuity.isZariskiClosed_asympRank_sublevel hk r

/-- **Corollary 2.4.** Sublevel sets of the regularization of an admissible
functional are Zariski-closed. -/
theorem sublevel_zariski_closed
    {V : Type v} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (Func : AdmissibleFunctional F V) (r : ℝ) :
    IsZariskiClosed (F := F) { T : V | Func.regularize T ≤ r } :=
  Semicontinuity.sublevel_zariski_closed Func r

/-- **Theorem 1.3 / Corollary 2.6.** Over all formats of order-`k` tensors,
the set of asymptotic-rank values is well-ordered (discreteness from
above). -/
theorem asympRank_values_wellOrdered {k : ℕ} (hk : 1 ≤ k) :
    WellFoundedLT
      (⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor F d => asympRank T)) :=
  Semicontinuity.asympRank_values_wellOrdered hk

/-- **Theorem 3.1** (the well-ordering part of Theorem 1.5). The value set of
every spectral point on order-`k` tensors is well-ordered (discreteness from
above). -/
theorem asympSpectrum_values_wellOrdered {k : ℕ} (hk : 2 ≤ k)
    (φ : SpectralPoint k F) :
    WellFoundedLT
      (⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor F d => φ T)) :=
  Semicontinuity.asympSpectrum_values_wellOrdered hk φ

/-- **Theorem 1.6 / Theorem 3.2.** For a `k`-tensor `T` and a cut
`I ⊆ [k]` with `1 ≤ |I| ≤ k-1`, if `|F| > flatRank_I(T)` then the product of
the pair subranks across the cut is at least the flattening rank:
`∏_{i ∈ I, j ∉ I} subrank_{i,j}(T) ≥ flatRank_I(T)`. -/
theorem subrankPair_prod_ge_flatRank {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (I : Finset (Fin k))
    (hI : 1 ≤ I.card) (hI' : I.card ≤ k - 1)
    (hF : ((flatRank T I : ℕ) : Cardinal) < Cardinal.mk F) :
    flatRank T I ≤
      ∏ p ∈ I ×ˢ ((Finset.univ : Finset (Fin k)) \ I),
        subrankPair T p.1 p.2 :=
  Semicontinuity.subrankPair_prod_ge_flatRank T I hI hI' hF

/-- **Corollary 3.5.** The asymptotic subrank of a `k`-tensor is at least the
minimum flattening rank over all bipartition cuts, raised to the power
`2/(k(k-1))`. -/
theorem minCut_flatRank_le_asympSubrank {k : ℕ} {d : Fin k → ℕ+} (T : KTensor F d)
    (hk : 2 ≤ k) :
    ((MinCut.admissibleCuts k).inf' (MinCut.admissibleCuts_nonempty (by omega))
        (fun I => (flatRank T I : ℝ))) ^ ((2 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)))
      ≤ asympSubrank T :=
  Semicontinuity.minCut_flatRank_le_asympSubrank T hk

/-- **Corollary 4.6** (the Euclidean-closedness part of Theorem 1.5). Over
`ℂ`, the value set of every spectral point on order-`k` tensors is
Euclidean-closed in `ℝ`. -/
theorem asympSpectrum_values_euclidean_closed {k : ℕ} (hk : 2 ≤ k)
    (φ : SpectralPoint k ℂ) :
    IsClosed
      (⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor ℂ d => φ T)) :=
  Semicontinuity.asympSpectrum_values_euclidean_closed hk φ

/-- **Theorem 1.4 / Theorem 4.1.** Over `ℂ`, the set of asymptotic-rank
values over all formats of order-`k` tensors is Euclidean-closed: the limit
of any converging sequence of asymptotic ranks is an asymptotic rank. -/
theorem asympRank_values_euclidean_closed {k : ℕ} :
    IsClosed
      (⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor ℂ d => asympRank T)) :=
  Semicontinuity.asympRank_values_euclidean_closed

/-- **Corollary 4.8.** Over `ℂ`, the set of asymptotic-rank values on a fixed
format is discrete if and only if each level set is Zariski-open in its
sublevel set. -/
theorem asympRank_discreteFromBelow_iff {k : ℕ} (d : Fin k → ℕ+) :
    IsDiscrete (Set.range fun T : KTensor ℂ d => asympRank T)
      ↔
    (∀ r : ℝ,
      IsZariskiOpenIn
        { T : KTensor ℂ d | asympRank T = r }
        { T : KTensor ℂ d | asympRank T ≤ r }) :=
  Semicontinuity.asympRank_discreteFromBelow_iff d

end Semicontinuity.MainResults
