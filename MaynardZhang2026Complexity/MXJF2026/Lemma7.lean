/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.MXJF2026.PairValue

/-!
# Lemma 7: lower bound on the inner optimization problem

For a positive definite `A` and any pair of distinct vertices `(x, x')`, the inner
optimization problem has value at least `4 Δ² / ‖x - x'‖²_{A⁻¹}`.

Every feasible `(θ, v)` has `2Δ ≤ ⟪x' - x, v⟫` (`PairFeasible.two_mul_le_inner`), and the
Cauchy–Schwarz inequality `⟪x' - x, v⟫² ≤ ‖x - x'‖²_{A⁻¹} ‖v‖²_A` concludes, the inner problem
being feasible.
-/

@[expose] public section

open Learning Matrix Set
open scoped RealInnerProductSpace

namespace MaynardZhang2026Complexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every feasible point `(θ, v)` of the inner problem of a pair of distinct vertices satisfies
`vᵀ A v ≥ 4 Δ² / ‖x - x'‖²_{A⁻¹}` for a positive definite matrix `A` and `Δ ≥ 0`. -/
lemma PairFeasible.div_mahalanobisSq_inv_le {𝒳 : Set (EuclideanSpace ℝ ι)} {Δ : ℝ}
    (hΔ : 0 ≤ Δ) {A : Matrix ι ι ℝ} (hA : A.PosDef) {x x' θ v : EuclideanSpace ℝ ι}
    (hxx' : (x, x') ∈ vertexPairs 𝒳) (h : PairFeasible 𝒳 Δ x x' θ v) :
    4 * Δ ^ 2 / mahalanobisSq A⁻¹ (x - x') ≤ mahalanobisSq A v := by
  have h2 := h.two_mul_le_inner hxx'
  have hpos : 0 < mahalanobisSq A⁻¹ (x - x') := hA.inv.mahalanobisSq_pos (sub_ne_zero.2 hxx'.2.2)
  rw [div_le_iff₀' hpos]
  calc 4 * Δ ^ 2 = (2 * Δ) ^ 2 := by ring
    _ ≤ ⟪x' - x, v⟫ ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
    _ = ⟪x - x', v⟫ ^ 2 := by rw [← neg_sub, inner_neg_left, neg_sq]
    _ ≤ mahalanobisSq A⁻¹ (x - x') * mahalanobisSq A v :=
      hA.inner_sq_le_mahalanobisSq_inv_mul _ _

/-- **Lemma 7** (Maynard-Zhang, Xiong, Jamieson, Fazel 2026). For a positive definite matrix
`A` and a pair of distinct vertices `(x, x')`,
`min {vᵀ A v | (θ, v) feasible for (x, x')} ≥ 4 Δ² / ‖x - x'‖²_{A⁻¹}`. -/
theorem le_pairValue (𝒳 : Finset (EuclideanSpace ℝ ι)) {Δ : ℝ} (hΔ : 0 < Δ)
    {A : Matrix ι ι ℝ} (hA : A.PosDef)
    {x x' : EuclideanSpace ℝ ι} (hxx' : (x, x') ∈ vertexPairs (𝒳 : Set (EuclideanSpace ℝ ι))) :
    4 * Δ ^ 2 / mahalanobisSq A⁻¹ (x - x') ≤ pairValue 𝒳 Δ A x x' :=
  le_pairValue_of_forall (exists_pairFeasible_of_finite 𝒳.finite_toSet Δ hxx')
    fun _ _ h ↦ h.div_mahalanobisSq_inv_le hΔ.le hA hxx'

end MaynardZhang2026Complexity
