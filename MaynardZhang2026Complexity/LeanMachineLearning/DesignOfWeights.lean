/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.LeanMachineLearning.DesignMahalanobis

/-!
# Designs from weights on a finite set

Nonnegative weights `q` summing to `1` on the points of a finite set `𝒳` define a design on `𝒳`
(a finitely supported function on the whole space), whose quadratic form is
`v ↦ ∑_{a ∈ 𝒳} q a ⟪a, v⟫²`. For example, the expected frequencies of the arms played by a bandit
algorithm over `T` rounds, `q a = (1/T) ∑_{t < T} P(X_t = a)`.

## Main statements

* `Learning.exists_isDesign_mahalanobisSq_eq`: the design of weights on a finite set.
-/

@[expose] public section

open Matrix
open scoped RealInnerProductSpace

namespace Learning

variable {ι : Type*} [Fintype ι]

/-- For nonnegative weights `q` summing to `1` on the points of a finite set `𝒳`, there is a
design on `𝒳` whose quadratic form is `v ↦ ∑_{a ∈ 𝒳} q a ⟪a, v⟫²`. -/
lemma exists_isDesign_mahalanobisSq_eq (𝒳 : Finset (EuclideanSpace ℝ ι)) (q : 𝒳 → ℝ)
    (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∑ a, q a = 1) :
    ∃ w, IsDesign 𝒳 w ∧
      ∀ v, mahalanobisSq (designMatrix w) v = ∑ a, q a * ⟪(a : EuclideanSpace ℝ ι), v⟫ ^ 2 := by
  classical
  let p : EuclideanSpace ℝ ι → ℝ := fun x ↦ if hx : x ∈ 𝒳 then q ⟨x, hx⟩ else 0
  have hp : ∀ x, p x ≠ 0 → x ∈ 𝒳 := fun x hx ↦ by
    by_contra h
    simp [p, h] at hx
  let w : EuclideanSpace ℝ ι →₀ ℝ := Finsupp.onFinset 𝒳 p hp
  have hsupp : w.support ⊆ 𝒳 := Finsupp.support_onFinset_subset
  have hsum : ∀ f : EuclideanSpace ℝ ι → ℝ,
      ∑ x ∈ w.support, w x * f x = ∑ a : 𝒳, q a * f a := by
    intro f
    rw [Finset.sum_subset hsupp fun x _ hx ↦ by rw [Finsupp.notMem_support_iff.1 hx, zero_mul]]
    simp only [w, Finsupp.onFinset_apply, p, dite_mul, zero_mul]
    exact Finset.sum_dite_of_true (fun _ h ↦ h) _ _
  refine ⟨w, ⟨by exact_mod_cast hsupp, fun x ↦ ?_, ?_⟩, fun v ↦ ?_⟩
  · simp only [w, Finsupp.onFinset_apply, p]
    split_ifs
    exacts [hq0 _, le_rfl]
  · have h1 := hsum fun _ ↦ 1
    simp only [mul_one] at h1
    rw [h1, hq1]
  · rw [mahalanobisSq_designMatrix, hsum]

end Learning
