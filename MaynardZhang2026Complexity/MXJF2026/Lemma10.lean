/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.MXJF2026.Setting

/-!
# Lemma 10: the worst normalized distance to the best arm is attained at an adjacent vertex

For positive definite `M` and the best arm `x⋆` of `θ`, the ratio `‖x⋆ - x‖²_M / ⟪x⋆ - x, θ⟫²`
over `x ∈ 𝒳 ∖ {x⋆}` is maximized over the vertices adjacent to `x⋆`.
-/

@[expose] public section

open Learning Matrix Set
open scoped RealInnerProductSpace

namespace MaynardZhang2026Complexity

variable {ι : Type*} [Fintype ι]

/-- **Lemma 10** (Maynard-Zhang, Xiong, Jamieson, Fazel 2026). Let `θ ∈ ℝ^d`, `M ≻ 0` and
`x⋆ = argmax_{x ∈ 𝒳} ⟪x, θ⟫` (unique). For every `x ∈ 𝒳 ∖ {x⋆}`,
`‖x⋆ - x‖²_M / ⟪x⋆ - x, θ⟫² ≤ max_{x' ∈ ℐ^{x⋆}} ‖x⋆ - x'‖²_M / ⟪x⋆ - x', θ⟫²`. -/
theorem ratio_le_iSup_adjacentTo (𝒳 : Finset (EuclideanSpace ℝ ι)) (θ : EuclideanSpace ℝ ι)
    {M : Matrix ι ι ℝ} (hM : M.PosDef) {xstar : EuclideanSpace ℝ ι} (hstar : xstar ∈ 𝒳)
    (hmax : ∀ y ∈ 𝒳, y ≠ xstar → ⟪y, θ⟫ < ⟪xstar, θ⟫) {x : EuclideanSpace ℝ ι} (hx : x ∈ 𝒳)
    (hne : x ≠ xstar) :
    mahalanobisSq M (xstar - x) / ⟪xstar - x, θ⟫ ^ 2 ≤
      ⨆ x' : adjacentTo (𝒳 : Set (EuclideanSpace ℝ ι)) xstar,
        mahalanobisSq M (xstar - x') / ⟪xstar - x', θ⟫ ^ 2 := by
  sorry

end MaynardZhang2026Complexity
