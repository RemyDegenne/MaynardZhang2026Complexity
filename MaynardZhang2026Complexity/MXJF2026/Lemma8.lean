/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.MXJF2026.Setting

/-!
# Lemma 8: upper bound on the inner optimization problem for adjacent pairs

For a positive definite `A` and an adjacent pair `(x, x')`, the inner optimization problem has
value at most `4 Δ² / ‖x - x'‖²_{A⁻¹}`.
-/

@[expose] public section

open Learning Matrix Set
open scoped RealInnerProductSpace

namespace MaynardZhang2026Complexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Lemma 8** (Maynard-Zhang, Xiong, Jamieson, Fazel 2026). For a positive definite matrix
`A` and an adjacent pair `(x, x')`,
`min {vᵀ A v | (θ, v) feasible for (x, x')} ≤ 4 Δ² / ‖x - x'‖²_{A⁻¹}`.

The paper assumes `Δ > 0`; the bound holds for every `Δ`. -/
theorem pairValue_le (𝒳 : Finset (EuclideanSpace ℝ ι)) (Δ : ℝ)
    {A : Matrix ι ι ℝ} (hA : A.PosDef)
    {x x' : EuclideanSpace ℝ ι} (hadj : IsAdjacent (𝒳 : Set (EuclideanSpace ℝ ι)) x x') :
    pairValue 𝒳 Δ A x x' ≤ 4 * Δ ^ 2 / mahalanobisSq A⁻¹ (x - x') := by
  sorry

end MaynardZhang2026Complexity
