/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.LeanMachineLearning.Design
public import MaynardZhang2026Complexity.Mathlib.Analysis.InnerProductSpace.MahalanobisInner

/-!
# Quadratic forms of design matrices

The squared Mahalanobis norm `vᵀ A(λ) v` of the design matrix `A(λ) = ∑ₓ λₓ x xᵀ` of weights `λ`
is `∑ₓ λₓ ⟪x, v⟫²`.

## Main statements

* `Learning.mahalanobisSq_outerSelf`: `vᵀ (y yᵀ) v = ⟪y, v⟫²`;
* `Learning.mahalanobisSq_designMatrix`: `vᵀ A(λ) v = ∑ₓ λₓ ⟪x, v⟫²`;
* `Learning.IsDesign.posSemidef_designMatrix`: the design matrix of a design is positive
  semidefinite;
* `Learning.IsDesign.mahalanobisSq_designMatrix_le`: for a design on a finite set `s`,
  `vᵀ A(λ) v ≤ ∑_{y ∈ s} ⟪y, v⟫²`, a bound uniform in the design;
* `Learning.mahalanobisSq_inv_card_smul_sum_outerSelf`: the quadratic form of the design matrix
  of the uniform design on a finite set.
-/

@[expose] public section

open Matrix
open scoped RealInnerProductSpace

namespace Learning

variable {ι : Type*} [Fintype ι] {𝒳 : Set (EuclideanSpace ℝ ι)} {w : EuclideanSpace ℝ ι →₀ ℝ}

/-- `vᵀ (y yᵀ) v = ⟪y, v⟫²`. -/
lemma mahalanobisSq_outerSelf (y v : EuclideanSpace ℝ ι) :
    mahalanobisSq (outerSelf y) v = ⟪y, v⟫ ^ 2 := by
  rw [mahalanobisSq_apply, dotProduct_outerSelf_mulVec, real_inner_comm]

/-- The quadratic form of a design matrix: `vᵀ A(λ) v = ∑ₓ λₓ ⟪x, v⟫²`. -/
lemma mahalanobisSq_designMatrix (w : EuclideanSpace ℝ ι →₀ ℝ) (v : EuclideanSpace ℝ ι) :
    mahalanobisSq (designMatrix w) v = ∑ y ∈ w.support, w y * ⟪y, v⟫ ^ 2 := by
  rw [designMatrix_apply, mahalanobisSq_sum_left]
  simp_rw [mahalanobisSq_smul_left, mahalanobisSq_outerSelf]

omit [Fintype ι] in
/-- The design matrix of a design is positive semidefinite. -/
lemma IsDesign.posSemidef_designMatrix [Finite ι] (hw : IsDesign 𝒳 w) :
    (designMatrix w).PosSemidef :=
  posSemidef_of_mem_designSet hw.designMatrix_mem_designSet

/-- For a design on a finite set `s`, `vᵀ A(λ) v ≤ ∑_{y ∈ s} ⟪y, v⟫²`. -/
lemma IsDesign.mahalanobisSq_designMatrix_le {s : Finset (EuclideanSpace ℝ ι)}
    (hw : IsDesign (s : Set (EuclideanSpace ℝ ι)) w) (v : EuclideanSpace ℝ ι) :
    mahalanobisSq (designMatrix w) v ≤ ∑ y ∈ s, ⟪y, v⟫ ^ 2 := by
  rw [mahalanobisSq_designMatrix]
  calc ∑ y ∈ w.support, w y * ⟪y, v⟫ ^ 2
      ≤ ∑ y ∈ w.support, w y * ∑ z ∈ s, ⟪z, v⟫ ^ 2 := by
        refine Finset.sum_le_sum fun y hy ↦ mul_le_mul_of_nonneg_left ?_ (hw.nonneg y)
        exact Finset.single_le_sum (f := fun z ↦ ⟪z, v⟫ ^ 2) (fun _ _ ↦ sq_nonneg _)
          (hw.mem_of_mem_support hy)
    _ = ∑ z ∈ s, ⟪z, v⟫ ^ 2 := by rw [← Finset.sum_mul, hw.sum_eq_one, one_mul]

/-- The quadratic form of the design matrix `|s|⁻¹ ∑_{y ∈ s} y yᵀ` of the uniform design on a
finite set `s`. -/
lemma mahalanobisSq_inv_card_smul_sum_outerSelf (s : Finset (EuclideanSpace ℝ ι))
    (v : EuclideanSpace ℝ ι) :
    mahalanobisSq ((s.card : ℝ)⁻¹ • ∑ y ∈ s, outerSelf y) v =
      (s.card : ℝ)⁻¹ * ∑ y ∈ s, ⟪y, v⟫ ^ 2 := by
  simp_rw [mahalanobisSq_smul_left, mahalanobisSq_sum_left, mahalanobisSq_outerSelf]

end Learning
