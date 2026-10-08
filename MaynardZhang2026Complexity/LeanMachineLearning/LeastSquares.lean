/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.LeanMachineLearning.DesignMatrix
public import MaynardZhang2026Complexity.Mathlib.Analysis.InnerProductSpace.Mahalanobis

/-!
# The Gram matrix of a finite allocation and its inverse

For points `x_0, …, x_{T-1}` of `EuclideanSpace ℝ ι` and their Gram matrix `A = ∑_t x_t x_tᵀ`,
the facts about `A⁻¹` used by least-squares estimators.

## Main statements

* `Matrix.inner_toEuclideanCLM_comm`: `⟪z, M v⟫ = ⟪M z, v⟫` for a symmetric matrix `M`;
* `Learning.sum_inner_toEuclideanCLM_inv_sum_outerSelf_sq`: `∑_t ⟪z, A⁻¹ x_t⟫² = zᵀ A⁻¹ z`;
* `Learning.inner_eq_sum_inner_toEuclideanCLM_inv_mul`: `⟪z, θ⟫ = ∑_t ⟪z, A⁻¹ x_t⟫ ⟪x_t, θ⟫`
  for invertible `A`;
* `Learning.span_range_eq_top_of_posDef`: if `A` is positive definite, the `x_t` span the space.
-/

@[expose] public section

open Matrix Finset
open scoped RealInnerProductSpace

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For a symmetric matrix `M`, `⟪z, M v⟫ = ⟪M z, v⟫`. -/
lemma inner_toEuclideanCLM_comm {M : Matrix ι ι ℝ} (hM : Mᵀ = M) (z v : EuclideanSpace ℝ ι) :
    ⟪z, toEuclideanCLM (𝕜 := ℝ) M v⟫ = ⟪toEuclideanCLM (𝕜 := ℝ) M z, v⟫ := by
  rw [real_inner_comm v, inner_toEuclideanCLM, inner_toEuclideanCLM, dotProduct_mulVec,
    ← mulVec_transpose, hM, dotProduct_comm]

end Matrix

namespace Learning

/-- If `A = ∑_t x_t x_tᵀ` is positive definite, the `x_t` span the space. -/
lemma span_range_eq_top_of_posDef {ι : Type*} [Finite ι] {T : ℕ}
    (x : Fin T → EuclideanSpace ℝ ι) (hA : (∑ s, outerSelf (x s)).PosDef) :
    Submodule.span ℝ (Set.range x) = ⊤ := by
  have := Fintype.ofFinite ι
  rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
  intro v hv
  by_contra hv0
  have h0 : ∀ t, ⟪v, x t⟫ = 0 := fun t ↦ by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_range_self t)) hv
  have hpos := hA.mahalanobisSq_pos hv0
  rw [mahalanobisSq_apply, sum_mulVec, dotProduct_sum] at hpos
  simp [dotProduct_outerSelf_mulVec, h0] at hpos

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℕ}

/-- For `A = ∑_t x_t x_tᵀ`, `∑_t ⟪z, A⁻¹ x_t⟫² = zᵀ A⁻¹ z` (both sides vanish if `A` is not
invertible, `A⁻¹` being `0`). -/
lemma sum_inner_toEuclideanCLM_inv_sum_outerSelf_sq (x : Fin T → EuclideanSpace ℝ ι)
    (z : EuclideanSpace ℝ ι) :
    ∑ t, ⟪z, toEuclideanCLM (𝕜 := ℝ) (∑ s, outerSelf (x s))⁻¹ (x t)⟫ ^ 2
      = mahalanobisSq (∑ s, outerSelf (x s))⁻¹ z := by
  set A := ∑ s, outerSelf (x s) with hA
  have hsymm : (A⁻¹)ᵀ = A⁻¹ := by rw [transpose_nonsing_inv, hA, transpose_sum_outerSelf]
  set w := toEuclideanCLM (𝕜 := ℝ) A⁻¹ z with hw
  have h1 (t : Fin T) : ⟪z, toEuclideanCLM (𝕜 := ℝ) A⁻¹ (x t)⟫ ^ 2
      = WithLp.ofLp w ⬝ᵥ outerSelf (x t) *ᵥ WithLp.ofLp w := by
    rw [inner_toEuclideanCLM_comm hsymm, dotProduct_outerSelf_mulVec]
  simp_rw [h1]
  rw [← dotProduct_sum, ← sum_mulVec, ← hA, hw, ofLp_toEuclideanCLM, mulVec_mulVec]
  by_cases hdet : IsUnit A.det
  · rw [mul_nonsing_inv A hdet, one_mulVec, dotProduct_comm, mahalanobisSq_apply]
  · rw [nonsing_inv_apply_not_isUnit A hdet]
    simp [mahalanobisSq_apply]

/-- For an invertible `A = ∑_t x_t x_tᵀ`, `⟪z, θ⟫ = ∑_t ⟪z, A⁻¹ x_t⟫ ⟪x_t, θ⟫`: the
least-squares estimator is exact on noiseless observations. -/
lemma inner_eq_sum_inner_toEuclideanCLM_inv_mul (x : Fin T → EuclideanSpace ℝ ι)
    (hA : IsUnit (∑ s, outerSelf (x s)).det) (z θ : EuclideanSpace ℝ ι) :
    ⟪z, θ⟫ = ∑ t, ⟪z, toEuclideanCLM (𝕜 := ℝ) (∑ s, outerSelf (x s))⁻¹ (x t)⟫ * ⟪x t, θ⟫ := by
  have h : θ = toEuclideanCLM (𝕜 := ℝ) (∑ s, outerSelf (x s))⁻¹
      (toEuclideanCLM (𝕜 := ℝ) (∑ s, outerSelf (x s)) θ) := by
    apply WithLp.ofLp_injective
    rw [ofLp_toEuclideanCLM, ofLp_toEuclideanCLM, mulVec_mulVec, nonsing_inv_mul _ hA,
      one_mulVec]
  conv_lhs => rw [h]
  rw [toEuclideanCLM_sum_outerSelf_apply, map_sum, inner_sum]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [map_smul, real_inner_smul_right, mul_comm]

end Learning
