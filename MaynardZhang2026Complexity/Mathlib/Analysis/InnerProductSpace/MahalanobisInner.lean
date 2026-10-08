/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.Mathlib.Analysis.InnerProductSpace.Mahalanobis

/-!
# Inner products and squared Mahalanobis norms

Facts relating the squared Mahalanobis norm `‖x‖_A² = xᵀ A x` (`Matrix.mahalanobisSq`) to the
inner product of `EuclideanSpace ℝ ι` and to the Loewner order.

## Main statements

* `Matrix.mahalanobisSq_eq_inner`: `‖x‖_A² = ⟪x, A x⟫`;
* `Matrix.mahalanobisSq_toEuclideanCLM_inv`: `‖A⁻¹ x‖_A² = ‖x‖_{A⁻¹}²` for invertible `A`;
* `Matrix.PosDef.inner_sq_le_mahalanobisSq_inv_mul`: the Cauchy–Schwarz inequality
  `⟪x, y⟫² ≤ ‖x‖_{A⁻¹}² ‖y‖_A²` for a positive definite matrix `A`;
* `Matrix.mahalanobisSq_le_of_le`: `A ≤ B` in the Loewner order implies `‖x‖_A² ≤ ‖x‖_B²`;
* `Matrix.mahalanobisSq_sum_left`: the squared Mahalanobis norm is additive in the matrix.
-/

@[expose] public section

open scoped RealInnerProductSpace MatrixOrder

namespace Matrix

variable {ι : Type*} [Fintype ι] {A B : Matrix ι ι ℝ}

/-- The squared Mahalanobis norm of a sum of matrices is the sum of the squared Mahalanobis
norms. -/
lemma mahalanobisSq_sum_left {κ : Type*} (s : Finset κ) (A : κ → Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) :
    mahalanobisSq (∑ k ∈ s, A k) x = ∑ k ∈ s, mahalanobisSq (A k) x := by
  simp [mahalanobisSq, sum_mulVec, dotProduct_sum]

/-- The squared Mahalanobis norm is monotone in the matrix for the Loewner order. -/
lemma mahalanobisSq_le_of_le (h : A ≤ B) (x : EuclideanSpace ℝ ι) :
    mahalanobisSq A x ≤ mahalanobisSq B x := by
  simpa [mahalanobisSq] using dotProduct_mulVec_le_of_le h (WithLp.ofLp x)

variable [DecidableEq ι]

/-- `‖x‖_A² = ⟪x, A x⟫`. -/
lemma mahalanobisSq_eq_inner (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    mahalanobisSq A x = ⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫ := by
  rw [mahalanobisSq_apply, EuclideanSpace.inner_eq_star_dotProduct, ofLp_toEuclideanCLM,
    star_trivial, dotProduct_comm]

/-- `‖A⁻¹ x‖_A² = ‖x‖_{A⁻¹}²` for an invertible matrix `A`. -/
lemma mahalanobisSq_toEuclideanCLM_inv (hA : IsUnit A.det) (x : EuclideanSpace ℝ ι) :
    mahalanobisSq A (toEuclideanCLM (𝕜 := ℝ) A⁻¹ x) = mahalanobisSq A⁻¹ x := by
  rw [mahalanobisSq_apply, mahalanobisSq_apply, ofLp_toEuclideanCLM, mulVec_mulVec,
    mul_nonsing_inv A hA, one_mulVec, dotProduct_comm]

/-- **Cauchy–Schwarz inequality** for the squared Mahalanobis norms of a positive definite matrix
and of its inverse: `⟪x, y⟫² ≤ ‖x‖_{A⁻¹}² ‖y‖_A²`. -/
lemma PosDef.inner_sq_le_mahalanobisSq_inv_mul (hA : A.PosDef) (x y : EuclideanSpace ℝ ι) :
    ⟪x, y⟫ ^ 2 ≤ mahalanobisSq A⁻¹ x * mahalanobisSq A y := by
  rw [← norm_toEuclideanCLM_sqrt_inv_sq hA, ← norm_toEuclideanCLM_sqrt_sq hA.posSemidef,
    ← mul_pow, ← real_inner_comm x y, ← inner_toEuclideanCLM_sqrt_sqrt_inv hA y x, mul_comm]
  exact sq_le_sq' (neg_le_of_abs_le (abs_real_inner_le_norm _ _)) (real_inner_le_norm _ _)

end Matrix
