/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.MXJF2026.Lemma7
public import MaynardZhang2026Complexity.MXJF2026.Lemma8

/-!
# Lemma 4: closed form of the inner optimization problem for adjacent pairs

For a design with positive definite design matrix and an adjacent pair `(x, x')`, the inner
optimization problem has value `4 Δ² / ‖x - x'‖²_{A(λ)⁻¹}`: Lemmas 7 and 8.
-/

@[expose] public section

open Learning Matrix Set
open scoped RealInnerProductSpace

namespace MaynardZhang2026Complexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Lemma 4** (Maynard-Zhang, Xiong, Jamieson, Fazel 2026). For a positive definite matrix `A`
and an adjacent pair `(x, x')`,
`min {vᵀ A v | (θ, v) feasible for (x, x')} = 4 Δ² / ‖x - x'‖²_{A⁻¹}`.

The paper states it for the design matrices `A = A(λ)` of full rank; the proof holds for every
positive definite `A`. -/
theorem pairValue_eq (𝒳 : Finset (EuclideanSpace ℝ ι)) {Δ : ℝ} (hΔ : 0 < Δ)
    {A : Matrix ι ι ℝ} (hA : A.PosDef)
    {x x' : EuclideanSpace ℝ ι} (hadj : IsAdjacent (𝒳 : Set (EuclideanSpace ℝ ι)) x x') :
    pairValue 𝒳 Δ A x x' = 4 * Δ ^ 2 / mahalanobisSq A⁻¹ (x - x') :=
  le_antisymm (pairValue_le 𝒳 Δ hA hadj)
    (le_pairValue 𝒳 hΔ hA (adjacentPairs_subset_vertexPairs (mem_adjacentPairs_iff.2 hadj)))

end MaynardZhang2026Complexity
