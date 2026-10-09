/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.MXJF2026.Setting
public import Mathlib.Probability.Moments.SubGaussian
public import MaynardZhang2026Complexity.Mathlib.MeasureTheory.MeasurableSpace.Instances
public import MaynardZhang2026Complexity.Mathlib.Probability.Moments.SamplingWithoutReplacement
public import MaynardZhang2026Complexity.LeanMachineLearning.DesignMatrix

/-!
# Lemma 9: sub-Gaussianity of a randomly permuted linear statistic

For fixed arms `x_t` and parameters `θ_t` and a uniformly random permutation `π`,
`zᵀ ∑_t A⁻¹ x_t x_tᵀ (θ_{π(t)} - θ̄_T)` is `√8 M B ‖z‖_{A⁻¹}`-sub-Gaussian.

The statistic is `∑_t ⟪a_t, θ_{π(t)} - θ̄_T⟫` with `a_t = ⟪z, A⁻¹ x_t⟫ x_t`, to which sampling
without replacement (`ProbabilityTheory.hasSubgaussianMGF_sum_inner_perm`) applies; then
`∑_t ‖a_t - ā‖² ≤ ∑_t ‖a_t‖² ≤ B² ∑_t ⟪z, A⁻¹ x_t⟫² = B² ‖z‖²_{A⁻¹}`. The paper's assumption
that the `x_t` span `ℝ^d` is not needed (if `A` is singular, `A⁻¹ = 0` and both sides vanish).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Matrix
open scoped RealInnerProductSpace

namespace MaynardZhang2026Complexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Lemma 9** (Maynard-Zhang, Xiong, Jamieson, Fazel 2026). Let `x_1, …, x_T` in `ℝ^d` with
`‖x_t‖ ≤ B`, `θ_1, …, θ_T` with `‖θ_t‖ ≤ M`, `θ̄_T = (1/T) ∑_t θ_t`, `A = ∑_t x_t x_tᵀ` and
`π` a uniformly random permutation of `[T]`. For every `z ∈ ℝ^d`,
`zᵀ ∑_t A⁻¹ x_t x_tᵀ (θ_{π(t)} - θ̄_T)` is `√8 M B ‖z‖_{A⁻¹}`-sub-Gaussian.

The paper assumes that the `x_t` span `ℝ^d`; this is not needed. -/
theorem hasSubgaussianMGF_sum_perm {T : ℕ} (x θ : Fin T → EuclideanSpace ℝ ι) {B M : ℝ}
    (hB : ∀ t, ‖x t‖ ≤ B) (hM : ∀ t, ‖θ t‖ ≤ M) (z : EuclideanSpace ℝ ι) :
    HasSubgaussianMGF (fun π : Equiv.Perm (Fin T) ↦
        ∑ t, ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ s, outerSelf (x s))⁻¹ (x t)⟫ *
          ⟪x t, θ (π t) - (T : ℝ)⁻¹ • ∑ s, θ s⟫)
      (8 * M ^ 2 * B ^ 2 * mahalanobisSq (∑ s, outerSelf (x s))⁻¹ z).toNNReal
      (PMF.uniformOfFintype (Equiv.Perm (Fin T))).toMeasure := by
  set c : Fin T → ℝ := fun t ↦
    ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ s, outerSelf (x s))⁻¹ (x t)⟫
  have h := hasSubgaussianMGF_sum_inner_perm (fun t ↦ c t • x t) θ hM
  simp_rw [real_inner_smul_left] at h
  refine h.mono (Real.toNNReal_le_toNNReal ?_)
  rw [mul_assoc (8 * M ^ 2)]
  gcongr
  rw [sum_norm_sub_mean_sq, ← sum_inner_toEuclideanCLM_inv_sum_outerSelf_sq, Finset.mul_sum]
  refine (sub_le_self _ (by positivity)).trans (Finset.sum_le_sum fun t _ ↦ ?_)
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, mul_comm]
  gcongr
  exact hB t

end MaynardZhang2026Complexity
