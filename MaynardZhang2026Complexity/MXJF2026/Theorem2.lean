/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.MXJF2026.Setting
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Theorem 2: error probability of Adjacent-BAI

With unit-norm arms and parameters, min-gap `Δ > 0` and `1`-sub-Gaussian noise,
Adjacent-BAI run on an allocation satisfying the rounding guarantee errs with probability at most
`|ℐ^{x⋆}| exp(-T / (36 H_Adjacent(𝒳, Δ)))`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits.Linear Matrix Real Set
open scoped RealInnerProductSpace

universe u

namespace MaynardZhang2026Complexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Theorem 2** (error probability of Adjacent-BAI, Maynard-Zhang, Xiong, Jamieson, Fazel
2026). Let `𝒳 ⊆ ℝ^d` finite with `‖x‖ ≤ 1` for all arms, and `θ_1, …, θ_T` with
`‖θ_t‖ ≤ 1` and min-gap at least `Δ > 0`, with best arm `x⋆`. For an allocation `x_1, …, x_T`
satisfying the rounding guarantee, every run of Adjacent-BAI with centered `1`-sub-Gaussian noise
outputs `x̂ ≠ x⋆` with probability at most `|ℐ^{x⋆}| exp(-T / (36 H_Adjacent(𝒳, Δ)))`.

The paper's assumption `T ≥ d²` is the condition under which the rounding procedure yields an
allocation with the rounding guarantee (`IsAdjacentRounding`); with the guarantee as hypothesis it
is not needed. -/
theorem prob_ne_bestArm_le (𝒳 : Finset (EuclideanSpace ℝ ι))
    [Nonempty (𝒳 : Set (EuclideanSpace ℝ ι))] (hnorm : ∀ x ∈ 𝒳, ‖x‖ ≤ 1) {T : ℕ}
    (x : Fin T → (𝒳 : Set (EuclideanSpace ℝ ι)))
    (hx : IsAdjacentRounding (𝒳 : Set (EuclideanSpace ℝ ι)) x) (θ : ℕ → EuclideanSpace ℝ ι)
    (hθ : ∀ t < T, ‖θ t‖ ≤ 1)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : MinGapGE 𝒳 θ T Δ) {xstar : EuclideanSpace ℝ ι}
    (hstar : IsBestArm 𝒳 θ T xstar) (ξ : ℕ → Measure ℝ) [∀ t, IsProbabilityMeasure (ξ t)]
    (hξ : ∀ t, HasSubgaussianMGF id 1 (ξ t))
    {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → 𝒳) (Y : ℕ → Ω → ℝ) (out : Ω → 𝒳)
    (h : (adjacentBAI x).IsRun (nonstationaryLinearEnv 𝒳 θ ξ) (fun _ _ ↦ ()) X Y out P) :
    P.real {ω | (out ω : EuclideanSpace ℝ ι) ≠ xstar} ≤
      (adjacentTo (𝒳 : Set (EuclideanSpace ℝ ι)) xstar).ncard *
        exp (-(T / (36 * hAdjacent (𝒳 : Set (EuclideanSpace ℝ ι)) Δ))) := by
  sorry

end MaynardZhang2026Complexity
