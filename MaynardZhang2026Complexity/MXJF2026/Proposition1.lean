/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.MXJF2026.Setting

/-!
# Proposition 1: the fixed-confidence complexity only depends on the adjacent arms

In the stationary fixed-confidence setting, the instance-optimal sample complexity
`min_λ max_{x ≠ x⋆} ‖x⋆ - x‖²_{A(λ)⁻¹} / ⟪x⋆ - x, θ⟫²` equals the same quantity with the maximum
restricted to the vertices adjacent to `x⋆`.
-/

@[expose] public section

open Learning Matrix Set
open scoped RealInnerProductSpace

namespace MaynardZhang2026Complexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Proposition 1** (Maynard-Zhang, Xiong, Jamieson, Fazel 2026). For a finite
`𝒳 ⊆ ℝ^d`, `θ ∈ ℝ^d` with unique best arm `x⋆`,
`min_λ max_{x ∈ 𝒳 ∖ {x⋆}} ‖x⋆ - x‖²_{A(λ)⁻¹} / ⟪x⋆ - x, θ⟫²
  = min_λ max_{x ∈ ℐ^{x⋆}} ‖x⋆ - x‖²_{A(λ)⁻¹} / ⟪x⋆ - x, θ⟫²`,
the minima being over designs with positive definite design matrix. The paper's standing
assumption that `𝒳` spans `ℝ^d` is not needed (without it both sides are `0`, infima over no
designs). -/
theorem iInf_iSup_ratio_eq (𝒳 : Finset (EuclideanSpace ℝ ι))
    (θ : EuclideanSpace ℝ ι)
    {xstar : EuclideanSpace ℝ ι} (hstar : xstar ∈ 𝒳)
    (hmax : ∀ y ∈ 𝒳, y ≠ xstar → ⟪y, θ⟫ < ⟪xstar, θ⟫) :
    (⨅ w : PosDefDesign (𝒳 : Set (EuclideanSpace ℝ ι)), ⨆ x : {x // x ∈ 𝒳 ∧ x ≠ xstar},
        mahalanobisSq (designMatrix (w : EuclideanSpace ℝ ι →₀ ℝ))⁻¹ (xstar - x) /
          ⟪xstar - x, θ⟫ ^ 2) =
      ⨅ w : PosDefDesign (𝒳 : Set (EuclideanSpace ℝ ι)),
        ⨆ x : adjacentTo (𝒳 : Set (EuclideanSpace ℝ ι)) xstar,
          mahalanobisSq (designMatrix (w : EuclideanSpace ℝ ι →₀ ℝ))⁻¹ (xstar - x) /
            ⟪xstar - x, θ⟫ ^ 2 := by
  sorry

end MaynardZhang2026Complexity
