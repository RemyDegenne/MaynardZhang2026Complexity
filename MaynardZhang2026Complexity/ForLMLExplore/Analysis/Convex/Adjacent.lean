/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Vertices and adjacent vertices of the convex hull of a set

For a set `𝒳` of a real topological vector space (typically a finite set, whose convex hull is a
polytope), in terms of Mathlib's exposed points and exposed sets:

## Main definitions

* `Set.vertices 𝒳` is the set of *vertices* of `conv 𝒳`: its exposed points, that is the points
  `x` such that `{x}` is the set of maximizers over `conv 𝒳` of some continuous linear
  functional;
* `Set.IsAdjacent 𝒳 x x'`: two distinct vertices are *adjacent* if the segment `[x, x']` is an
  exposed subset of `conv 𝒳` (the set of maximizers of some functional), i.e. an edge of the
  polytope;
* `Set.adjacentPairs 𝒳`, `Set.adjacentTo 𝒳 x`, `Set.vertexPairs 𝒳`: the adjacent pairs, the
  vertices adjacent to `x`, and the pairs of distinct vertices.

## Main statements

* `Set.vertices_subset`: the vertices of `conv 𝒳` belong to `𝒳`;
* `Set.IsAdjacent.symm`: adjacency is symmetric.
-/

@[expose] public section

namespace Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] {𝒳 : Set E} {x x' : E}

/-- The vertices of the convex hull of `𝒳`: its exposed points. -/
def vertices (𝒳 : Set E) : Set E := (convexHull ℝ 𝒳).exposedPoints ℝ

/-- Two distinct vertices `x`, `x'` of the convex hull of `𝒳` are *adjacent* if the segment
`[x, x']` is an exposed subset of the hull (an edge of the polytope). -/
def IsAdjacent (𝒳 : Set E) (x x' : E) : Prop :=
  x ∈ vertices 𝒳 ∧ x' ∈ vertices 𝒳 ∧ x ≠ x' ∧ IsExposed ℝ (convexHull ℝ 𝒳) (segment ℝ x x')

/-- The pairs of adjacent vertices of the convex hull of `𝒳`. -/
def adjacentPairs (𝒳 : Set E) : Set (E × E) := {p | IsAdjacent 𝒳 p.1 p.2}

/-- The vertices adjacent to `x`. -/
def adjacentTo (𝒳 : Set E) (x : E) : Set E := {x' | IsAdjacent 𝒳 x x'}

/-- The pairs of distinct vertices of the convex hull of `𝒳`. -/
def vertexPairs (𝒳 : Set E) : Set (E × E) := (vertices 𝒳).offDiag

lemma IsAdjacent.symm (h : IsAdjacent 𝒳 x x') : IsAdjacent 𝒳 x' x :=
  ⟨h.2.1, h.1, h.2.2.1.symm, segment_symm ℝ x x' ▸ h.2.2.2⟩

lemma IsAdjacent.left_mem_vertices (h : IsAdjacent 𝒳 x x') : x ∈ vertices 𝒳 := h.1

lemma IsAdjacent.right_mem_vertices (h : IsAdjacent 𝒳 x x') : x' ∈ vertices 𝒳 := h.2.1

lemma IsAdjacent.ne (h : IsAdjacent 𝒳 x x') : x ≠ x' := h.2.2.1

lemma adjacentPairs_subset_vertexPairs : adjacentPairs 𝒳 ⊆ vertexPairs 𝒳 :=
  fun _ h ↦ ⟨h.1, h.2.1, h.2.2.1⟩

lemma mem_adjacentTo_iff : x' ∈ adjacentTo 𝒳 x ↔ IsAdjacent 𝒳 x x' := Iff.rfl

lemma mem_adjacentPairs_iff {p : E × E} : p ∈ adjacentPairs 𝒳 ↔ IsAdjacent 𝒳 p.1 p.2 := Iff.rfl

/-- The vertices of the convex hull of `𝒳` are points of `𝒳`. -/
lemma vertices_subset : vertices 𝒳 ⊆ 𝒳 :=
  exposedPoints_subset_extremePoints.trans extremePoints_convexHull_subset

end Set
