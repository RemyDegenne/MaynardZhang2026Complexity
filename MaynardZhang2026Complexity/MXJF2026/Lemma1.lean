/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.MXJF2026.Setting

/-!
# Lemma 1: the adjacency lemma

For a vertex `x` of `conv 𝒳` and any `θ`, some arm of `𝒳` beats `x` for `θ` if and only if some
vertex adjacent to `x` does.
-/

@[expose] public section

open Learning Set
open scoped RealInnerProductSpace

namespace MaynardZhang2026Complexity

variable {ι : Type*} [Fintype ι]

/-- **Lemma 1** (adjacency lemma, Maynard-Zhang, Xiong, Jamieson, Fazel 2026). Let `𝒳 ⊆ ℝ^d` be
finite and `θ ∈ ℝ^d`. For any vertex `x` of `conv 𝒳`, there is `y ∈ 𝒳` with `⟪y - x, θ⟫ > 0` if
and only if there is `z` adjacent to `x` with `⟪z - x, θ⟫ > 0`. -/
theorem exists_pos_inner_iff (𝒳 : Finset (EuclideanSpace ℝ ι)) (θ : EuclideanSpace ℝ ι)
    {x : EuclideanSpace ℝ ι} (hx : x ∈ vertices (𝒳 : Set (EuclideanSpace ℝ ι))) :
    (∃ y ∈ 𝒳, 0 < ⟪y - x, θ⟫) ↔
      ∃ z ∈ adjacentTo (𝒳 : Set (EuclideanSpace ℝ ι)) x, 0 < ⟪z - x, θ⟫ := by
  sorry

end MaynardZhang2026Complexity
