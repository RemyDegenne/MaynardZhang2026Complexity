/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.MXJF2026.PairValue

/-!
# Lemma 8: upper bound on the inner optimization problem for adjacent pairs

For a positive definite `A` and an adjacent pair `(x, x')`, the inner optimization problem has
value at most `4 Δ² / ‖x - x'‖²_{A⁻¹}`.

The paper's explicit feasible point: with `c = ‖x - x'‖²_{A⁻¹}` and `w` a direction for which `x`
and `x'` tie and beat every other vertex (`Set.Finite.isAdjacent_iff_exists_inner`),
`θ = (Δ / c) A⁻¹ (x - x') + α w` and `v = -(2Δ / c) A⁻¹ (x - x')` for `α` large.
-/

@[expose] public section

open Learning Matrix Set
open scoped RealInnerProductSpace

namespace MaynardZhang2026Complexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For an adjacent pair `(x, x')` of a finite set and a positive definite matrix `A`, the inner
problem has a feasible point `(θ, v)` with `vᵀ A v = 4 Δ² / ‖x - x'‖²_{A⁻¹}`. -/
lemma exists_pairFeasible_mahalanobisSq_eq {𝒳 : Set (EuclideanSpace ℝ ι)} (h𝒳 : 𝒳.Finite)
    (Δ : ℝ) {A : Matrix ι ι ℝ} (hA : A.PosDef) {x x' : EuclideanSpace ℝ ι}
    (hadj : IsAdjacent 𝒳 x x') :
    ∃ θ v, PairFeasible 𝒳 Δ x x' θ v ∧
      mahalanobisSq A v = 4 * Δ ^ 2 / mahalanobisSq A⁻¹ (x - x') := by
  obtain ⟨w, hxw, hw⟩ := (h𝒳.isAdjacent_iff_exists_inner hadj.left_mem_vertices
    hadj.right_mem_vertices hadj.ne).1 hadj
  set c := mahalanobisSq A⁻¹ (x - x') with hc_def
  have hc : 0 < c := hA.inv.mahalanobisSq_pos (sub_ne_zero.2 hadj.ne)
  set u := toEuclideanCLM (𝕜 := ℝ) A⁻¹ (x - x') with hu_def
  have hu : ⟪x - x', u⟫ = c := (mahalanobisSq_eq_inner _ _).symm
  have hu' : ⟪x' - x, u⟫ = -c := by rw [← neg_sub, inner_neg_left, hu]
  have hw0 : ⟪x - x', w⟫ = 0 := by rw [inner_sub_left, hxw, sub_self]
  have hww : ∀ y, ⟪x' - y, w⟫ = ⟪x - y, w⟫ := fun y ↦ by rw [inner_sub_left, inner_sub_left, hxw]
  -- the coefficient `α` of `w`
  obtain ⟨α, hα⟩ := ((h𝒳.subset vertices_subset).image fun y ↦
    max (Δ - Δ / c * ⟪x - y, u⟫) (Δ + Δ / c * ⟪x' - y, u⟫) / ⟪x - y, w⟫).bddAbove
  have hαy : ∀ y ∈ vertices 𝒳, y ≠ x → y ≠ x' →
      max (Δ - Δ / c * ⟪x - y, u⟫) (Δ + Δ / c * ⟪x' - y, u⟫) ≤ α * ⟪x - y, w⟫ := by
    intro y hy hyx hyx'
    have hpos : 0 < ⟪x - y, w⟫ := by rw [inner_sub_left, sub_pos]; exact hw y hy hyx hyx'
    rw [← div_le_iff₀ hpos]
    exact hα ⟨y, hy, rfl⟩
  refine ⟨(Δ / c) • u + α • w, -(2 * Δ / c) • u, ⟨fun y hy hyx ↦ ?_, fun y hy hyx' ↦ ?_⟩, ?_⟩
  · rw [inner_add_right, inner_smul_right, inner_smul_right]
    by_cases hyx' : y = x'
    · rw [hyx', hu, hw0, mul_zero, add_zero, div_mul_cancel₀ _ hc.ne']
    · have := (le_max_left _ _).trans (hαy y hy hyx hyx')
      linarith
  · rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, inner_smul_right]
    by_cases hyx : y = x
    · rw [hyx, hu', hww, sub_self, inner_zero_left]
      refine le_of_eq ?_
      field_simp
      ring
    · have := (le_max_right _ _).trans (hαy y hy hyx hyx')
      have h2 : -(2 * Δ / c) * ⟪x' - y, u⟫ = -2 * (Δ / c * ⟪x' - y, u⟫) := by ring
      rw [hww, h2]
      linarith
  · rw [mahalanobisSq_smul, hu_def,
      mahalanobisSq_toEuclideanCLM_inv ((isUnit_iff_isUnit_det A).mp hA.isUnit), ← hc_def]
    field_simp
    ring

/-- **Lemma 8** (Maynard-Zhang, Xiong, Jamieson, Fazel 2026). For a positive definite matrix
`A` and an adjacent pair `(x, x')`,
`min {vᵀ A v | (θ, v) feasible for (x, x')} ≤ 4 Δ² / ‖x - x'‖²_{A⁻¹}`.

The paper assumes `Δ > 0`; the bound holds for every `Δ`. -/
theorem pairValue_le (𝒳 : Finset (EuclideanSpace ℝ ι)) (Δ : ℝ)
    {A : Matrix ι ι ℝ} (hA : A.PosDef)
    {x x' : EuclideanSpace ℝ ι} (hadj : IsAdjacent (𝒳 : Set (EuclideanSpace ℝ ι)) x x') :
    pairValue 𝒳 Δ A x x' ≤ 4 * Δ ^ 2 / mahalanobisSq A⁻¹ (x - x') := by
  obtain ⟨θ, v, h, hv⟩ := exists_pairFeasible_mahalanobisSq_eq 𝒳.finite_toSet Δ hA hadj
  exact hv ▸ pairValue_le_mahalanobisSq hA.posSemidef h

end MaynardZhang2026Complexity
