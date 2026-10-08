/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.Mathlib.Analysis.Matrix.MeasurableSpace
public import MaynardZhang2026Complexity.Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The squared Mahalanobis norm

For a matrix `A : Matrix ι ι ℝ` and `x : EuclideanSpace ℝ ι`, `Matrix.mahalanobisSq A x = xᵀ A x`
is the squared Mahalanobis (semi)norm `‖x‖_A²`, nonnegative when `A` is positive semidefinite.
It is the quadratic form `Matrix.toQuadraticForm' A` of Mathlib evaluated at the coordinates of `x`
(`Matrix.mahalanobisSq_eq_toQuadraticForm'`), written on the Euclidean space where the vectors of
the learning problems live.

## Main definitions

* `Matrix.mahalanobisSq A x = xᵀ A x`;
* `Matrix.pinvMahalanobisSq A s = sup_θ (2 ⟪θ, s⟫ - θᵀ A θ)`, the squared norm `sᵀ A† s` for the
  Moore–Penrose pseudo-inverse, in variational form.

## Main statements

* `Matrix.PosSemidef.mahalanobisSq_nonneg`, `Matrix.PosDef.mahalanobisSq_pos`;
* `Matrix.mahalanobisSq_one`: `‖x‖_1² = ‖x‖²`;
* `Matrix.norm_toEuclideanCLM_sqrt_sq`: `‖√A x‖² = ‖x‖_A²` for `A` positive semidefinite;
* `Continuous.mahalanobisSq`, `Measurable.mahalanobisSq` (`@[fun_prop]`),
  `Matrix.continuous_mahalanobisSq`, `Matrix.bddAbove_range_mahalanobisSq` (bounded on compact
  sets).
-/

@[expose] public section

open Matrix

namespace Matrix

variable {ι : Type*} [Fintype ι]

/-- The squared Mahalanobis norm `‖x‖_A² = xᵀ A x`. -/
def mahalanobisSq (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  WithLp.ofLp x ⬝ᵥ A *ᵥ WithLp.ofLp x

lemma mahalanobisSq_apply (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    mahalanobisSq A x = WithLp.ofLp x ⬝ᵥ A *ᵥ WithLp.ofLp x := rfl

lemma mahalanobisSq_eq_toQuadraticForm' [DecidableEq ι] (A : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) :
    mahalanobisSq A x = A.toQuadraticForm' (WithLp.ofLp x) := by
  simp [mahalanobisSq, Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply']

@[simp]
lemma mahalanobisSq_zero_right (A : Matrix ι ι ℝ) : mahalanobisSq A 0 = 0 := by
  simp [mahalanobisSq]

@[simp]
lemma mahalanobisSq_zero_left (x : EuclideanSpace ℝ ι) : mahalanobisSq 0 x = 0 := by
  simp [mahalanobisSq]

@[simp]
lemma mahalanobisSq_neg (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    mahalanobisSq A (-x) = mahalanobisSq A x := by
  simp [mahalanobisSq, mulVec_neg]

lemma mahalanobisSq_smul (A : Matrix ι ι ℝ) (c : ℝ) (x : EuclideanSpace ℝ ι) :
    mahalanobisSq A (c • x) = c ^ 2 * mahalanobisSq A x := by
  simp [mahalanobisSq, mulVec_smul, dotProduct_smul, smul_dotProduct, sq, mul_assoc]

lemma mahalanobisSq_add_left (A B : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    mahalanobisSq (A + B) x = mahalanobisSq A x + mahalanobisSq B x := by
  simp [mahalanobisSq, add_mulVec, dotProduct_add]

lemma mahalanobisSq_smul_left (c : ℝ) (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    mahalanobisSq (c • A) x = c * mahalanobisSq A x := by
  simp [mahalanobisSq, smul_mulVec, dotProduct_smul]

/-- For the identity matrix, the squared Mahalanobis norm is the squared Euclidean norm. -/
@[simp]
lemma mahalanobisSq_one [DecidableEq ι] (x : EuclideanSpace ℝ ι) :
    mahalanobisSq 1 x = ‖x‖ ^ 2 := by
  rw [mahalanobisSq_apply, one_mulVec, ← real_inner_self_eq_norm_sq,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp

lemma PosSemidef.mahalanobisSq_nonneg {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (x : EuclideanSpace ℝ ι) : 0 ≤ mahalanobisSq A x := by
  simpa [mahalanobisSq] using hA.dotProduct_mulVec_nonneg (WithLp.ofLp x)

lemma PosDef.mahalanobisSq_pos {A : Matrix ι ι ℝ} (hA : A.PosDef) {x : EuclideanSpace ℝ ι}
    (hx : x ≠ 0) : 0 < mahalanobisSq A x := by
  simpa [mahalanobisSq] using hA.dotProduct_mulVec_pos (x := WithLp.ofLp x) (by simpa using hx)

section Sqrt

open scoped MatrixOrder

variable [DecidableEq ι] {A : Matrix ι ι ℝ}

/-- `‖√A x‖ ^ 2 = xᵀ A x` for a positive semidefinite matrix `A`: the Mahalanobis norm is the
Euclidean norm after the linear map `√A`. -/
lemma norm_toEuclideanCLM_sqrt_sq (hA : A.PosSemidef) (x : EuclideanSpace ℝ ι) :
    ‖toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A) x‖ ^ 2 = mahalanobisSq A x := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
    ofLp_toEuclideanCLM, dotProduct_mulVec, ← mulVec_transpose, transpose_sqrt, mulVec_mulVec,
    hA.sqrt_mul_sqrt, dotProduct_comm, mahalanobisSq_apply]

/-- `‖√(A⁻¹) x‖ ^ 2 = xᵀ A⁻¹ x` for a positive definite matrix `A`. -/
lemma norm_toEuclideanCLM_sqrt_inv_sq (hA : A.PosDef) (x : EuclideanSpace ℝ ι) :
    ‖toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A⁻¹) x‖ ^ 2 = mahalanobisSq A⁻¹ x :=
  norm_toEuclideanCLM_sqrt_sq hA.inv.posSemidef x

end Sqrt

end Matrix

section Regularity

variable {X ι : Type*} [Fintype ι]

@[fun_prop]
lemma Continuous.mahalanobisSq [TopologicalSpace X] {A : X → Matrix ι ι ℝ}
    {v : X → EuclideanSpace ℝ ι} (hA : Continuous A) (hv : Continuous v) :
    Continuous fun x ↦ mahalanobisSq (A x) (v x) := by
  simp only [mahalanobisSq_apply]
  fun_prop

@[fun_prop]
lemma Measurable.mahalanobisSq [MeasurableSpace X] {A : X → Matrix ι ι ℝ}
    {v : X → EuclideanSpace ℝ ι} (hA : Measurable A) (hv : Measurable v) :
    Measurable fun x ↦ mahalanobisSq (A x) (v x) := by
  simp only [mahalanobisSq_apply]
  fun_prop

lemma Matrix.continuous_mahalanobisSq (A : Matrix ι ι ℝ) : Continuous (mahalanobisSq A) :=
  continuous_const.mahalanobisSq continuous_id

/-- The squared Mahalanobis norm is bounded on a compact set. -/
lemma Matrix.bddAbove_range_mahalanobisSq {𝒳 : Set (EuclideanSpace ℝ ι)} (h𝒳 : IsCompact 𝒳)
    (A : Matrix ι ι ℝ) : BddAbove (Set.range fun x : 𝒳 ↦ mahalanobisSq A x) := by
  refine (h𝒳.image (continuous_mahalanobisSq A)).bddAbove.mono ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨x, x.2, rfl⟩

end Regularity

/-! ### Quadratic form of the pseudo-inverse -/

namespace Matrix

variable {ι : Type*} [Fintype ι]

open scoped RealInnerProductSpace in
/-- The squared norm `‖s‖²_{A†} = sᵀ A† s` of `s` for the Moore–Penrose pseudo-inverse of a positive
semidefinite matrix `A`, in variational form: `sup_θ (2 ⟪θ, s⟫ - θᵀ A θ)`. For `A` positive
semidefinite and `s` in the range of `A` this is `sᵀ A† s` (and `sᵀ A⁻¹ s` when `A` is
invertible); it is `0` (junk) when the supremum is not bounded, i.e. `s ∉ range A`. -/
noncomputable def pinvMahalanobisSq (A : Matrix ι ι ℝ) (s : EuclideanSpace ℝ ι) : ℝ :=
  ⨆ θ : EuclideanSpace ℝ ι, 2 * ⟪θ, s⟫ - mahalanobisSq A θ

lemma pinvMahalanobisSq_nonneg (A : Matrix ι ι ℝ) (s : EuclideanSpace ℝ ι) :
    0 ≤ pinvMahalanobisSq A s := by
  unfold pinvMahalanobisSq
  by_cases h : BddAbove (Set.range fun θ : EuclideanSpace ℝ ι ↦ 2 * inner ℝ θ s - mahalanobisSq A θ)
  · refine le_trans ?_ (le_ciSup h 0)
    simp
  · rw [Real.iSup_of_not_bddAbove h]

end Matrix
