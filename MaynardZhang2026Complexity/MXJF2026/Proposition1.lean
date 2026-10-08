/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.MXJF2026.Lemma10

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
  refine iInf_congr fun w ↦ ?_
  have hsub : ∀ z ∈ adjacentTo (𝒳 : Set (EuclideanSpace ℝ ι)) xstar, z ∈ 𝒳 ∧ z ≠ xstar :=
    fun z hz ↦ ⟨vertices_subset hz.2.1, hz.2.2.1.symm⟩
  rcases isEmpty_or_nonempty {x // x ∈ 𝒳 ∧ x ≠ xstar} with h | hne
  · -- `𝒳 = {x⋆}`: both suprema are over empty index types
    have : IsEmpty (adjacentTo (𝒳 : Set (EuclideanSpace ℝ ι)) xstar) :=
      ⟨fun z ↦ h.false ⟨z, hsub z z.2⟩⟩
    simp only [Real.iSup_of_isEmpty]
  obtain ⟨y, hy, hyx⟩ := hne.some
  have hxV : xstar ∈ vertices (𝒳 : Set (EuclideanSpace ℝ ι)) :=
    mem_vertices_of_inner_lt (Finset.mem_coe.2 hstar) hmax
  have : Nonempty (adjacentTo (𝒳 : Set (EuclideanSpace ℝ ι)) xstar) :=
    (𝒳.finite_toSet.adjacentTo_nonempty hxV (Finset.mem_coe.2 hy) hyx).to_subtype
  have : Finite {x // x ∈ 𝒳 ∧ x ≠ xstar} :=
    Finite.of_injective (fun x ↦ (⟨x.1, x.2.1⟩ : 𝒳)) fun x y h ↦ by
      ext1
      simpa using congrArg Subtype.val h
  -- `≤` by Lemma 10, `≥` since the adjacent vertices are points of `𝒳 ∖ {x⋆}`
  refine le_antisymm (ciSup_le fun x ↦ ratio_le_iSup_adjacentTo 𝒳 θ w.2.2.inv hstar hmax
    x.2.1 x.2.2) (ciSup_le fun z ↦ ?_)
  exact le_ciSup (f := fun x : {x // x ∈ 𝒳 ∧ x ≠ xstar} ↦
    mahalanobisSq (designMatrix (w : EuclideanSpace ℝ ι →₀ ℝ))⁻¹ (xstar - x) /
      ⟪xstar - x, θ⟫ ^ 2) (Set.finite_range _).bddAbove ⟨z, hsub z z.2⟩

end MaynardZhang2026Complexity
