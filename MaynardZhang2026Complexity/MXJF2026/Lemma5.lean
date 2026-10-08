/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.MXJF2026.Setting
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Lemma 5: sub-Gaussian error of the least-squares estimator of Adjacent-BAI

In a run of Adjacent-BAI with `1`-sub-Gaussian noise, `zᵀ(θ̂_T - θ̄_T)` is
`3 ‖z‖_{(∑_t x_t x_tᵀ)⁻¹}`-sub-Gaussian for every `z`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits.Linear Matrix Set
open scoped RealInnerProductSpace

universe u

namespace MaynardZhang2026Complexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Lemma 5** (sub-Gaussian error of the least-squares estimator, Maynard-Zhang, Xiong,
Jamieson, Fazel 2026). In a run of Adjacent-BAI with allocation `x_1, …, x_T` (with invertible
`∑_t x_t x_tᵀ`) and centered `1`-sub-Gaussian noise, for every `z ∈ ℝ^d` the error
`zᵀ(θ̂_T - θ̄_T)` of the least-squares estimator is `3 ‖z‖_{(∑_t x_t x_tᵀ)⁻¹}`-sub-Gaussian.

The bounds `‖x_t‖ ≤ 1` and `‖θ_t‖ ≤ 1` are those of Theorem 2, which the paper's proof uses
(through Lemma 9 with `B = M = 1`) but its statement omits; without them the statement is false
(in dimension `1`, with `x = (1, 2)` and `θ = (-10, 10)` the bias term alone has variance `36 z²`,
above `9 z² / 5`). -/
theorem hasSubgaussianMGF_lsEstimator (𝒳 : Finset (EuclideanSpace ℝ ι))
    [Nonempty (𝒳 : Set (EuclideanSpace ℝ ι))] {T : ℕ} (x : Fin T → (𝒳 : Set (EuclideanSpace ℝ ι)))
    (hx : (allocMatrix x).PosDef) (hx₁ : ∀ t, ‖(x t : EuclideanSpace ℝ ι)‖ ≤ 1)
    (θ : ℕ → EuclideanSpace ℝ ι) (hθ : ∀ t < T, ‖θ t‖ ≤ 1) (ξ : ℕ → Measure ℝ)
    [∀ t, IsProbabilityMeasure (ξ t)] (hξ : ∀ t, HasSubgaussianMGF id 1 (ξ t))
    {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → 𝒳) (Y : ℕ → Ω → ℝ) (out : Ω → 𝒳)
    (h : (adjacentBAI x).IsRun (nonstationaryLinearEnv 𝒳 θ ξ) (fun _ _ ↦ ()) X Y out P)
    (z : EuclideanSpace ℝ ι) :
    HasSubgaussianMGF (fun ω ↦ ⟪z, lsEstimator x (history (fun _ _ ↦ ()) X Y T ω) - avgParam θ T⟫)
      (9 * mahalanobisSq (allocMatrix x)⁻¹ z).toNNReal P := by
  sorry

end MaynardZhang2026Complexity
