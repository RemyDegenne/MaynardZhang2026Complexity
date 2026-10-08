/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.MXJF2026.Setting
public import MaynardZhang2026Complexity.Mathlib.Analysis.Convex.Vertices

/-!
# Lemma 10: the worst normalized distance to the best arm is attained at an adjacent vertex

For positive definite `M` and the best arm `x⋆` of `θ`, the ratio `‖x⋆ - x‖²_M / ⟪x⋆ - x, θ⟫²`
over `x ∈ 𝒳 ∖ {x⋆}` is maximized over the vertices adjacent to `x⋆`.
-/

@[expose] public section

open Learning Matrix Set
open scoped MatrixOrder RealInnerProductSpace

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
  classical
  -- the ratio of `y` is `‖√M u_y‖²` for `u_y = (x⋆ - y) / ⟪x⋆ - y, θ⟫`
  set L := toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt M)
  have hratio : ∀ y, mahalanobisSq M (xstar - y) / ⟪xstar - y, θ⟫ ^ 2 =
      ‖L (⟪xstar - y, θ⟫⁻¹ • (xstar - y))‖ ^ 2 := fun y ↦ by
    rw [norm_toEuclideanCLM_sqrt_sq hM.posSemidef, mahalanobisSq_smul, inv_pow, div_eq_inv_mul]
  -- `u_x` is in the convex hull of the `u_z`, `z` adjacent to `x⋆`, and `‖L ·‖` is convex
  have hcone := 𝒳.finite_toSet.smul_mem_convexHull_image_adjacentTo (Finset.mem_coe.2 hstar)
    hmax (Finset.mem_coe.2 hx) hne
  obtain ⟨_, ⟨z, hz, rfl⟩, hle⟩ :=
    (convexOn_univ_norm.comp_linearMap L.toLinearMap).exists_ge_of_mem_convexHull
      (subset_univ _) hcone
  have := 𝒳.finite_toSet.finite_adjacentTo (x := xstar) |>.to_subtype
  refine le_ciSup_of_le (Set.finite_range _).bddAbove ⟨z, hz⟩ ?_
  rw [hratio, hratio]
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2

end MaynardZhang2026Complexity
