/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.MXJF2026.Setting

/-!
# Lemma 7: lower bound on the inner optimization problem

For a positive definite `A` and any pair of distinct vertices `(x, x')`, the inner
optimization problem has value at least `4 Δ² / ‖x - x'‖²_{A⁻¹}`.
-/

@[expose] public section

open Learning Matrix Set
open scoped RealInnerProductSpace

namespace MaynardZhang2026Complexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Lemma 7** (Maynard-Zhang, Xiong, Jamieson, Fazel 2026). For a positive definite matrix
`A` and a pair of distinct vertices `(x, x')`,
`min {vᵀ A v | (θ, v) feasible for (x, x')} ≥ 4 Δ² / ‖x - x'‖²_{A⁻¹}`. -/
theorem le_pairValue (𝒳 : Finset (EuclideanSpace ℝ ι)) {Δ : ℝ} (hΔ : 0 < Δ)
    {A : Matrix ι ι ℝ} (hA : A.PosDef)
    {x x' : EuclideanSpace ℝ ι} (hxx' : (x, x') ∈ vertexPairs (𝒳 : Set (EuclideanSpace ℝ ι))) :
    4 * Δ ^ 2 / mahalanobisSq A⁻¹ (x - x') ≤ pairValue 𝒳 Δ A x x' := by
  sorry

end MaynardZhang2026Complexity
