/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.MXJF2026.Setting
public import MaynardZhang2026Complexity.Mathlib.Analysis.Convex.Vertices
public import MaynardZhang2026Complexity.Mathlib.Analysis.InnerProductSpace.Mahalanobis

/-!
# The inner optimization problem of the lower bound

Basic properties of the constraints `PairFeasible 𝒳 Δ x x' θ v` and of the value
`pairValue 𝒳 Δ A x x' = inf {vᵀ A v | (θ, v) feasible for (x, x')}` of the inner problem of
Lemma 3, used in Lemmas 4, 7 and 8 and in the bounds on `f(𝒳, Δ)`.

## Main statements

* `PairFeasible.two_mul_le_inner`: every feasible `(θ, v)` has `2Δ ≤ ⟪x' - x, v⟫`;
* `exists_pairFeasible_of_finite`: the inner problem of a pair of distinct vertices of a finite
  set is feasible;
* `pairValue_nonneg`, `pairValue_le_mahalanobisSq`, `le_pairValue_of_forall`,
  `exists_pairFeasible_lt_of_pairValue_lt`: the value is a nonnegative infimum;
* `pairValue_mono`, `pairValue_smul`: the value is monotone in `A` for the Loewner order and
  positively homogeneous.
-/

@[expose] public section

open Learning Matrix Set
open scoped RealInnerProductSpace MatrixOrder

namespace MaynardZhang2026Complexity

variable {ι : Type*} [Fintype ι] {𝒳 : Set (EuclideanSpace ℝ ι)} {Δ : ℝ}
  {x x' θ v : EuclideanSpace ℝ ι} {A B : Matrix ι ι ℝ}

/-- The constraints at `y = x'` and at `y = x` add up to `2Δ ≤ ⟪x' - x, v⟫` for every feasible
`(θ, v)`. -/
lemma PairFeasible.two_mul_le_inner (h : PairFeasible 𝒳 Δ x x' θ v)
    (hxx' : (x, x') ∈ vertexPairs 𝒳) :
    2 * Δ ≤ ⟪x' - x, v⟫ := by
  obtain ⟨hx, hx', hne⟩ := hxx'
  have h1 := h.1 x' hx' hne.symm
  have h2 := h.2 x hx hne
  rw [inner_add_right] at h2
  have h3 : ⟪x - x', θ⟫ = -⟪x' - x, θ⟫ := by rw [← inner_neg_left, neg_sub]
  linarith

/-- For a vertex `x` of a finite set and any `Δ`, some direction makes `x` beat every other vertex
by at least `Δ`: a strictly exposing direction, scaled. -/
lemma exists_forall_le_inner_sub_of_mem_vertices (h𝒳 : 𝒳.Finite) (hx : x ∈ vertices 𝒳)
    (Δ : ℝ) :
    ∃ θ, ∀ y ∈ vertices 𝒳, y ≠ x → Δ ≤ ⟪x - y, θ⟫ := by
  obtain ⟨w, hw⟩ := (mem_vertices_iff_exists_inner_lt (vertices_subset hx)).1 hx
  obtain ⟨c, hc⟩ := ((h𝒳.subset vertices_subset).image fun y ↦ Δ / ⟪x - y, w⟫).bddAbove
  refine ⟨c • w, fun y hy hyx ↦ ?_⟩
  have hpos : 0 < ⟪x - y, w⟫ := by
    rw [inner_sub_left, sub_pos]
    exact hw y (vertices_subset hy) hyx
  rw [inner_smul_right, ← div_le_iff₀ hpos]
  exact hc ⟨y, hy, rfl⟩

/-- The inner optimization problem of a pair of distinct vertices of a finite set is feasible. -/
lemma exists_pairFeasible_of_finite (h𝒳 : 𝒳.Finite) (Δ : ℝ) (hxx' : (x, x') ∈ vertexPairs 𝒳) :
    ∃ θ v, PairFeasible 𝒳 Δ x x' θ v := by
  obtain ⟨θ, hθ⟩ := exists_forall_le_inner_sub_of_mem_vertices h𝒳 hxx'.1 Δ
  obtain ⟨θ', hθ'⟩ := exists_forall_le_inner_sub_of_mem_vertices h𝒳 hxx'.2.1 Δ
  exact ⟨θ, θ' - θ, hθ, by simpa using hθ'⟩

/-! ### The value of the inner problem -/

/-- The values `vᵀ A v` of the inner problem are bounded below for `A` positive semidefinite. -/
lemma bddBelow_range_mahalanobisSq_pairFeasible (hA : A.PosSemidef) :
    BddBelow (range fun q : {q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι //
      PairFeasible 𝒳 Δ x x' q.1 q.2} ↦ mahalanobisSq A q.1.2) :=
  ⟨0, by rintro _ ⟨q, rfl⟩; exact hA.mahalanobisSq_nonneg _⟩

/-- The value of the inner problem is nonnegative for `A` positive semidefinite. -/
lemma pairValue_nonneg (hA : A.PosSemidef) : 0 ≤ pairValue 𝒳 Δ A x x' :=
  Real.iInf_nonneg fun _ ↦ hA.mahalanobisSq_nonneg _

/-- The values of the inner problems of the pairs of distinct vertices are bounded below for `A`
positive semidefinite. -/
lemma bddBelow_range_pairValue (hA : A.PosSemidef) :
    BddBelow (range fun p : vertexPairs 𝒳 ↦ pairValue 𝒳 Δ A p.1.1 p.1.2) :=
  ⟨0, by rintro _ ⟨p, rfl⟩; exact pairValue_nonneg hA⟩

/-- The value of the inner problem is at most `vᵀ A v` for every feasible `(θ, v)`. -/
lemma pairValue_le_mahalanobisSq (hA : A.PosSemidef) (h : PairFeasible 𝒳 Δ x x' θ v) :
    pairValue 𝒳 Δ A x x' ≤ mahalanobisSq A v :=
  ciInf_le (bddBelow_range_mahalanobisSq_pairFeasible hA)
    (⟨(θ, v), h⟩ : {q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι //
      PairFeasible 𝒳 Δ x x' q.1 q.2})

/-- A lower bound on `vᵀ A v` over the feasible points of a feasible inner problem is a lower
bound on its value. -/
lemma le_pairValue_of_forall (hne : ∃ θ v, PairFeasible 𝒳 Δ x x' θ v) {c : ℝ}
    (h : ∀ θ v, PairFeasible 𝒳 Δ x x' θ v → c ≤ mahalanobisSq A v) :
    c ≤ pairValue 𝒳 Δ A x x' := by
  obtain ⟨θ, v, hθv⟩ := hne
  have : Nonempty {q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι //
      PairFeasible 𝒳 Δ x x' q.1 q.2} := ⟨⟨(θ, v), hθv⟩⟩
  exact le_ciInf fun q ↦ h q.1.1 q.1.2 q.2

/-- If the value of a feasible inner problem is less than `c`, some feasible `(θ, v)` has
`vᵀ A v < c`. -/
lemma exists_pairFeasible_lt_of_pairValue_lt (hne : ∃ θ v, PairFeasible 𝒳 Δ x x' θ v) {c : ℝ}
    (h : pairValue 𝒳 Δ A x x' < c) :
    ∃ θ v, PairFeasible 𝒳 Δ x x' θ v ∧ mahalanobisSq A v < c := by
  obtain ⟨θ, v, hθv⟩ := hne
  have : Nonempty {q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι //
      PairFeasible 𝒳 Δ x x' q.1 q.2} := ⟨⟨(θ, v), hθv⟩⟩
  obtain ⟨q, hq⟩ := exists_lt_of_ciInf_lt h
  exact ⟨q.1.1, q.1.2, q.2, hq⟩

/-- The value of the inner problem is monotone in the matrix for the Loewner order on positive
semidefinite matrices. -/
lemma pairValue_mono (hA : A.PosSemidef) (hAB : A ≤ B) :
    pairValue 𝒳 Δ A x x' ≤ pairValue 𝒳 Δ B x x' := by
  rcases isEmpty_or_nonempty {q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι //
      PairFeasible 𝒳 Δ x x' q.1 q.2} with hne | hne
  · simp [pairValue]
  · exact ciInf_mono (bddBelow_range_mahalanobisSq_pairFeasible hA)
      fun q ↦ mahalanobisSq_le_of_le hAB _

/-- The value of the inner problem is positively homogeneous in the matrix. -/
lemma pairValue_smul {c : ℝ} (hc : 0 ≤ c) (A : Matrix ι ι ℝ) :
    pairValue 𝒳 Δ (c • A) x x' = c * pairValue 𝒳 Δ A x x' := by
  simp_rw [pairValue, mahalanobisSq_smul_left, Real.mul_iInf_of_nonneg hc]

end MaynardZhang2026Complexity
