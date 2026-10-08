/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.LeanMachineLearning.DesignMatrix
public import MaynardZhang2026Complexity.Mathlib.Analysis.InnerProductSpace.Mahalanobis
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Design distributions

A *design distribution* on an action set `𝒳 ⊆ EuclideanSpace ℝ ι` is a finitely supported
probability vector on points of `𝒳`, encoded as a finitely supported function
`w : EuclideanSpace ℝ ι →₀ ℝ` with `IsDesign 𝒳 w`. Its *design matrix* is
`designMatrix w = ∑ₓ w x • x xᵀ`.

## Main definitions

* `designMatrix`: the linear map `w ↦ ∑ₓ w x • x xᵀ`;
* `IsDesign 𝒳 w`: `w` is a design distribution on `𝒳`;
* `designOfWeights 𝒳 q`: the design on a finite set with prescribed weights.

## Main results

* `exists_isDesign_of_mem_designSet`: Carathéodory's theorem for design matrices: every element
  of `designSet 𝒳` is the design matrix of a design distribution on `𝒳` supported on at most
  `card ι ^ 2 + 1` points; `mem_designSet_iff`: the design set is the set of design matrices of
  design distributions.
* `sum_mul_dotProduct_inv_mulVec`: `∑ₓ w x * xᵀ A(w)⁻¹ x = card ι` when `A(w)` is invertible.
* `mahalanobisSq_designMatrix`: the quadratic form of a design matrix,
  `vᵀ A(w) v = ∑ₓ w x ⟪x, v⟫²`; `IsDesign.mahalanobisSq_designMatrix_le`: for a design on a
  finite set `s`, `vᵀ A(w) v ≤ ∑_{y ∈ s} ⟪y, v⟫²`, a bound uniform in the design.
* `designOfWeights 𝒳 q`: the design on a finite set `𝒳` with weights `q : 𝒳 → ℝ`
  (`isDesign_designOfWeights`, `mahalanobisSq_designMatrix_designOfWeights`).

Ported from the `colt-2026-83` development (the `G`-optimal designs and the Kiefer–Wolfowitz
theorem of that development are not included).
-/

@[expose] public section

open Real Filter Set
open scoped RealInnerProductSpace MatrixOrder Matrix Topology

namespace Learning

variable {ι : Type*} {𝒳 : Set (EuclideanSpace ℝ ι)} {w : EuclideanSpace ℝ ι →₀ ℝ}
  {A : Matrix ι ι ℝ} {x : EuclideanSpace ℝ ι}

/-- The design matrix `∑ₓ w x • x xᵀ` of finitely supported weights `w` on the space. -/
noncomputable def designMatrix : (EuclideanSpace ℝ ι →₀ ℝ) →ₗ[ℝ] Matrix ι ι ℝ :=
  Finsupp.linearCombination ℝ outerSelf

lemma designMatrix_apply (w : EuclideanSpace ℝ ι →₀ ℝ) :
    designMatrix w = ∑ x ∈ w.support, w x • outerSelf x :=
  Finsupp.linearCombination_apply ℝ w

/-- A design distribution on `𝒳`: finitely supported nonnegative weights on points of `𝒳`
summing to one. -/
structure IsDesign (𝒳 : Set (EuclideanSpace ℝ ι)) (w : EuclideanSpace ℝ ι →₀ ℝ) : Prop where
  support_subset : ↑w.support ⊆ 𝒳
  nonneg : ∀ x, 0 ≤ w x
  sum_eq_one : ∑ x ∈ w.support, w x = 1

lemma IsDesign.mono {𝒴 : Set (EuclideanSpace ℝ ι)} (hw : IsDesign 𝒳 w) (h : 𝒳 ⊆ 𝒴) :
    IsDesign 𝒴 w :=
  ⟨hw.support_subset.trans h, hw.nonneg, hw.sum_eq_one⟩

lemma IsDesign.mem_of_mem_support (hw : IsDesign 𝒳 w) (hx : x ∈ w.support) : x ∈ 𝒳 :=
  hw.support_subset hx

lemma IsDesign.pos_of_mem_support (hw : IsDesign 𝒳 w) (hx : x ∈ w.support) : 0 < w x :=
  lt_of_le_of_ne (hw.nonneg x) (Finsupp.mem_support_iff.mp hx).symm

lemma IsDesign.support_nonempty (hw : IsDesign 𝒳 w) : w.support.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  rintro h
  simpa [h] using hw.sum_eq_one

/-- The design matrix of a design distribution on `𝒳` belongs to `designSet 𝒳`. -/
lemma IsDesign.designMatrix_mem_designSet (hw : IsDesign 𝒳 w) : designMatrix w ∈ designSet 𝒳 := by
  rw [designMatrix_apply]
  exact convex_designSet.sum_mem (fun x _ ↦ hw.nonneg x) hw.sum_eq_one
    fun x hx ↦ outerSelf_mem_designSet (hw.mem_of_mem_support hx)

/-- The image of a design distribution on `𝒳` by a map `f` is a design distribution on
`f '' 𝒳`. -/
lemma IsDesign.mapDomain (hw : IsDesign 𝒳 w) (f : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) :
    IsDesign (f '' 𝒳) (Finsupp.mapDomain f w) := by
  classical
  refine ⟨?_, fun y ↦ ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hy)
    exact ⟨x, hw.mem_of_mem_support hx, rfl⟩
  · rw [Finsupp.mapDomain, Finsupp.sum_apply]
    exact Finset.sum_nonneg fun x _ ↦ by
      dsimp only
      rw [Finsupp.single_apply]
      split_ifs <;> simp [hw.nonneg]
  · change (Finsupp.mapDomain f w).sum (fun _ a ↦ a) = 1
    rw [Finsupp.sum_mapDomain_index (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)]
    exact hw.sum_eq_one

variable [Fintype ι]

/-- Carathéodory's theorem for design matrices: every design matrix in `designSet 𝒳` is the
design matrix of a design distribution on `𝒳` supported on at most `card ι ^ 2 + 1` points. -/
lemma exists_isDesign_of_mem_designSet (hA : A ∈ designSet 𝒳) :
    ∃ w, IsDesign 𝒳 w ∧ designMatrix w = A ∧ w.support.card ≤ Fintype.card ι ^ 2 + 1 := by
  classical
  obtain ⟨κ, _, z, v, hz, hind, hv, hv1, rfl⟩ := eq_pos_convex_span_of_mem_convexHull hA
  choose x hx𝒳 hxz using fun i ↦ hz (Set.mem_range_self i)
  have hxinj : Function.Injective x := fun i j h ↦ hind.injective (by rw [← hxz, ← hxz, h])
  set v' : κ →₀ ℝ := Finsupp.equivFunOnFinite.symm v with hv'
  have hv'_apply : ∀ i, v' i = v i := fun i ↦ rfl
  have hsupp : (Finsupp.mapDomain x v').support = v'.support.image x :=
    Finsupp.mapDomain_support_of_injective hxinj _
  refine ⟨Finsupp.mapDomain x v', ⟨?_, fun y ↦ ?_, ?_⟩, ?_, ?_⟩
  · intro y hy
    rw [Finset.mem_coe, hsupp, Finset.mem_image] at hy
    obtain ⟨i, -, rfl⟩ := hy
    exact hx𝒳 i
  · by_cases hy : y ∈ Set.range x
    · obtain ⟨i, rfl⟩ := hy
      rw [Finsupp.mapDomain_apply_of_injective hxinj, hv'_apply]
      exact (hv i).le
    · rw [Finsupp.mapDomain_of_notMem_range _ _ hy]
  · change (Finsupp.mapDomain x v').sum (fun _ a ↦ a) = 1
    rw [Finsupp.sum_mapDomain_index (fun _ ↦ rfl) (fun _ _ _ ↦ rfl), Finsupp.sum_fintype _ _
      fun _ ↦ rfl]
    exact hv1
  · rw [designMatrix, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply,
      Finsupp.sum_fintype _ _ fun _ ↦ by simp]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hv'_apply, Function.comp_apply, hxz]
  · rw [hsupp, Finset.card_image_of_injective _ hxinj]
    calc v'.support.card ≤ Fintype.card κ := Finset.card_le_univ _
      _ ≤ Module.finrank ℝ (Matrix ι ι ℝ) + 1 :=
        hind.card_le_finrank_succ.trans (by gcongr; exact Submodule.finrank_le _)
      _ = Fintype.card ι ^ 2 + 1 := by rw [Module.finrank_matrix, Module.finrank_self, sq]; ring

omit [Fintype ι] in
/-- The design set is the set of design matrices of design distributions. -/
lemma mem_designSet_iff [Finite ι] : A ∈ designSet 𝒳 ↔ ∃ w, IsDesign 𝒳 w ∧ designMatrix w = A := by
  have := Fintype.ofFinite ι
  exact ⟨fun hA ↦ (exists_isDesign_of_mem_designSet hA).imp fun _ h ↦ ⟨h.1, h.2.1⟩,
    fun ⟨_, hw, hA⟩ ↦ hA ▸ hw.designMatrix_mem_designSet⟩

/-! ### Quadratic forms of design matrices -/

section QuadraticForm

open Matrix

/-- `vᵀ (y yᵀ) v = ⟪y, v⟫²`. -/
lemma mahalanobisSq_outerSelf (y v : EuclideanSpace ℝ ι) :
    mahalanobisSq (outerSelf y) v = ⟪y, v⟫ ^ 2 := by
  rw [mahalanobisSq_apply, dotProduct_outerSelf_mulVec, real_inner_comm]

/-- The quadratic form of a design matrix: `vᵀ A(w) v = ∑ₓ w x ⟪x, v⟫²`. -/
lemma mahalanobisSq_designMatrix (w : EuclideanSpace ℝ ι →₀ ℝ) (v : EuclideanSpace ℝ ι) :
    mahalanobisSq (designMatrix w) v = ∑ y ∈ w.support, w y * ⟪y, v⟫ ^ 2 := by
  rw [designMatrix_apply, mahalanobisSq_sum_left]
  simp_rw [mahalanobisSq_smul_left, mahalanobisSq_outerSelf]

omit [Fintype ι] in
/-- The design matrix of a design is positive semidefinite. -/
lemma IsDesign.posSemidef_designMatrix [Finite ι] (hw : IsDesign 𝒳 w) :
    (designMatrix w).PosSemidef :=
  posSemidef_of_mem_designSet hw.designMatrix_mem_designSet

/-- For a design on a finite set `s`, `vᵀ A(w) v ≤ ∑_{y ∈ s} ⟪y, v⟫²`. -/
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

end QuadraticForm

/-! ### Designs with prescribed weights on a finite set -/

section Weights

open scoped Classical in
/-- The design on the finite set `𝒳` with weight `q a` at each point `a ∈ 𝒳` (a design when the
weights are nonnegative and sum to `1`, `isDesign_designOfWeights`). For instance, the expected
frequencies `q a = (1/T) ∑_{t < T} P(X_t = a)` of the arms played by a bandit algorithm. -/
noncomputable def designOfWeights (𝒳 : Finset (EuclideanSpace ℝ ι)) (q : 𝒳 → ℝ) :
    EuclideanSpace ℝ ι →₀ ℝ :=
  Finsupp.onFinset 𝒳 (fun x ↦ if hx : x ∈ 𝒳 then q ⟨x, hx⟩ else 0) fun x hx ↦ by
    by_contra h
    simp [h] at hx

variable {s : Finset (EuclideanSpace ℝ ι)} {q : s → ℝ}

/-- Sums against the design of weights `q` on `s` are weighted sums over `s`. -/
lemma sum_designOfWeights_mul (f : EuclideanSpace ℝ ι → ℝ) :
    ∑ x ∈ (designOfWeights s q).support, designOfWeights s q x * f x = ∑ a : s, q a * f a := by
  classical
  have hsupp : (designOfWeights s q).support ⊆ s := Finsupp.support_onFinset_subset
  rw [Finset.sum_subset hsupp fun x _ hx ↦ by rw [Finsupp.notMem_support_iff.1 hx, zero_mul]]
  simp only [designOfWeights, Finsupp.onFinset_apply, dite_mul, zero_mul]
  exact Finset.sum_dite_of_true (fun _ h ↦ h) _ _

/-- Nonnegative weights summing to `1` on a finite set define a design on it. -/
lemma isDesign_designOfWeights (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∑ a, q a = 1) :
    IsDesign s (designOfWeights s q) where
  support_subset := by exact_mod_cast Finsupp.support_onFinset_subset
  nonneg x := by
    simp only [designOfWeights, Finsupp.onFinset_apply]
    split_ifs
    exacts [hq0 _, le_rfl]
  sum_eq_one := by
    have h := sum_designOfWeights_mul (q := q) fun _ ↦ 1
    simp only [mul_one] at h
    rw [h, hq1]

/-- The quadratic form of the design of weights `q` on `s` is `v ↦ ∑_{a ∈ s} q a ⟪a, v⟫²`. -/
lemma mahalanobisSq_designMatrix_designOfWeights (v : EuclideanSpace ℝ ι) :
    Matrix.mahalanobisSq (designMatrix (designOfWeights s q)) v
      = ∑ a : s, q a * ⟪(a : EuclideanSpace ℝ ι), v⟫ ^ 2 := by
  rw [mahalanobisSq_designMatrix, sum_designOfWeights_mul]

end Weights

variable [DecidableEq ι]

/-- The design matrix of the image of `w` by the linear map of matrix `M` is `M A(w) Mᵀ`. -/
lemma designMatrix_mapDomain_toEuclideanCLM (M : Matrix ι ι ℝ) (w : EuclideanSpace ℝ ι →₀ ℝ) :
    designMatrix (Finsupp.mapDomain (Matrix.toEuclideanCLM (𝕜 := ℝ) M) w) =
      M * designMatrix w * Mᵀ := by
  rw [designMatrix, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply,
    Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Function.comp_apply, outerSelf_toEuclideanCLM, Matrix.mul_smul, Matrix.smul_mul]

omit [DecidableEq ι] in
/-- For weights `w` with design matrix `A = ∑ₓ w x • x xᵀ` and any matrix `C`,
`∑ₓ w x * xᵀ C x = tr (C A)`. -/
lemma sum_mul_dotProduct_mulVec (C : Matrix ι ι ℝ) (w : EuclideanSpace ℝ ι →₀ ℝ) :
    ∑ x ∈ w.support, w x * (WithLp.ofLp x ⬝ᵥ C *ᵥ WithLp.ofLp x) = (C * designMatrix w).trace := by
  simp_rw [dotProduct_mulVec_eq_trace_mul_outerSelf]
  rw [designMatrix_apply, Matrix.mul_sum, Matrix.trace_sum]
  simp_rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- For weights `w` with invertible design matrix `A = ∑ₓ w x • x xᵀ`,
`∑ₓ w x * xᵀ A⁻¹ x = card ι`. -/
lemma sum_mul_dotProduct_inv_mulVec (hA : IsUnit (designMatrix w).det) :
    ∑ x ∈ w.support, w x * (WithLp.ofLp x ⬝ᵥ (designMatrix w)⁻¹ *ᵥ WithLp.ofLp x) =
      Fintype.card ι := by
  rw [sum_mul_dotProduct_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.trace_one]

end Learning
