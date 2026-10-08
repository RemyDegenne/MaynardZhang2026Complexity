/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.Mathlib.Analysis.Convex.Vertices

/-!
# Existence of vertices and of adjacent vertices

For a finite set `𝒳` of a finite-dimensional real inner product space, a point of `𝒳` of
maximal norm is a vertex of `conv 𝒳`, and if `𝒳` has two points then `conv 𝒳` has an edge.

## Main statements

* `Set.mem_vertices_of_forall_norm_le`: a point of `𝒳` of maximal norm is a vertex;
* `Set.Finite.exists_isAdjacent`: a finite set with two points has two adjacent vertices.
-/

@[expose] public section

open scoped RealInnerProductSpace

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {𝒳 : Set E} {x : E}

/-- A point of a set with maximal norm is a vertex of its convex hull: it is strictly exposed by
itself. -/
lemma mem_vertices_of_forall_norm_le (hx : x ∈ 𝒳) (h : ∀ y ∈ 𝒳, ‖y‖ ≤ ‖x‖) :
    x ∈ vertices 𝒳 := by
  refine mem_vertices_of_inner_lt hx (w := x) fun y hy hyx ↦ ?_
  have h1 : 0 < ‖y - x‖ ^ 2 := by
    have : y - x ≠ 0 := sub_ne_zero.2 hyx
    positivity
  have h2 : ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg y) (h y hy) 2
  rw [norm_sub_sq_real] at h1
  rw [real_inner_self_eq_norm_sq]
  linarith

namespace Finite

variable [FiniteDimensional ℝ E]

/-- A finite set with two points has two adjacent vertices. -/
lemma exists_isAdjacent (h𝒳 : 𝒳.Finite) (hnt : 𝒳.Nontrivial) : ∃ x x', IsAdjacent 𝒳 x x' := by
  obtain ⟨x, hx, hmax⟩ := Set.exists_max_image 𝒳 (fun y ↦ ‖y‖) h𝒳 hnt.nonempty
  have hxv : x ∈ vertices 𝒳 := mem_vertices_of_forall_norm_le hx hmax
  obtain ⟨y, hy, hyx⟩ := hnt.exists_ne x
  obtain ⟨x', hx'⟩ := h𝒳.adjacentTo_nonempty hxv hy hyx
  exact ⟨x, x', hx'⟩

end Finite

end Set
