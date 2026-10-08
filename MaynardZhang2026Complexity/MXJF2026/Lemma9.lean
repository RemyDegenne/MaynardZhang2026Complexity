/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.MXJF2026.Setting
public import Mathlib.Probability.Moments.SubGaussian
public import MaynardZhang2026Complexity.Mathlib.MeasureTheory.MeasurableSpace.Instances

/-!
# Lemma 9: sub-Gaussianity of a randomly permuted linear statistic

For fixed arms `x_t` and parameters `θ_t` and a uniformly random permutation `π`,
`zᵀ ∑_t A⁻¹ x_t x_tᵀ (θ_{π(t)} - θ̄_T)` is `√8 M B ‖z‖_{A⁻¹}`-sub-Gaussian.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Matrix
open scoped RealInnerProductSpace

namespace MaynardZhang2026Complexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Lemma 9** (Maynard-Zhang, Xiong, Jamieson, Fazel 2026). Let `x_1, …, x_T` span `ℝ^d` with
`‖x_t‖ ≤ B`, `θ_1, …, θ_T` with `‖θ_t‖ ≤ M`, `θ̄_T = (1/T) ∑_t θ_t`, `A = ∑_t x_t x_tᵀ` and
`π` a uniformly random permutation of `[T]`. For every `z ∈ ℝ^d`,
`zᵀ ∑_t A⁻¹ x_t x_tᵀ (θ_{π(t)} - θ̄_T)` is `√8 M B ‖z‖_{A⁻¹}`-sub-Gaussian. -/
theorem hasSubgaussianMGF_sum_perm {T : ℕ} (x θ : Fin T → EuclideanSpace ℝ ι)
    (hspan : Submodule.span ℝ (Set.range x) = ⊤) {B M : ℝ} (hB : ∀ t, ‖x t‖ ≤ B)
    (hM : ∀ t, ‖θ t‖ ≤ M) (z : EuclideanSpace ℝ ι) :
    HasSubgaussianMGF (fun π : Equiv.Perm (Fin T) ↦
        ∑ t, ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ s, outerSelf (x s))⁻¹ (x t)⟫ *
          ⟪x t, θ (π t) - (T : ℝ)⁻¹ • ∑ s, θ s⟫)
      (8 * M ^ 2 * B ^ 2 * mahalanobisSq (∑ s, outerSelf (x s))⁻¹ z).toNNReal
      (PMF.uniformOfFintype (Equiv.Perm (Fin T))).toMeasure := by
  sorry

end MaynardZhang2026Complexity
