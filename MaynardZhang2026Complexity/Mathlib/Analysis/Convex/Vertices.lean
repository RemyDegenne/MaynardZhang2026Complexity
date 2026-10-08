/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.Mathlib.Analysis.Convex.Adjacent
public import Mathlib.Analysis.Convex.Join
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Vertices and edges of the convex hull of a finite set

For a finite set `𝒳` of a real inner product space (complete, for the characterizations through
inner products), the vertices of `conv 𝒳` (`Set.vertices`) and its edges (`Set.IsAdjacent`) are
characterized through directions `w`, and a vertex that is not beaten by its adjacent vertices in a
direction `θ` is a maximizer of `θ` over `𝒳` (local optimality implies global optimality, the
*adjacency lemma*).

## Main statements

* `Set.mem_convexHull_setOf_inner_eq`: the maximizers of a linear form over `conv s` are the
  convex combinations of its maximizers in `s`;
* `Set.mem_vertices_iff_exists_inner_lt`: a point of `𝒳` is a vertex iff some direction makes it
  strictly better than the other points of `𝒳`;
* `Set.mem_vertices_of_forall_norm_le`: a point of maximal norm is a vertex;
* `Set.Finite.convexHull_vertices`: `conv 𝒳` is the convex hull of its vertices;
* `Set.Finite.isAdjacent_iff_exists_inner`: two distinct vertices are adjacent iff some direction
  makes them tie and beat every other vertex;
* `Set.Finite.exists_mem_adjacentTo_inner_pos`: if some point of `𝒳` beats the vertex `x` in the
  direction `θ`, then some vertex adjacent to `x` beats it (the adjacency lemma);
* `Set.Finite.exists_mem_adjacentTo_inner_nonneg`: the same with weak inequalities;
* `Set.Finite.adjacentTo_nonempty`, `Set.Finite.exists_isAdjacent`: a vertex of a set with another
  point has an adjacent vertex, and a set with two points has an edge;
* `Set.Finite.smul_mem_convexHull_image_adjacentTo`: the cone property at a strict maximizer;
* `Set.Finite.inner_lt_of_forall_mem_vertices`, `Set.Finite.mem_vertices_of_forall_mem_vertices`:
  a point strictly better than every other vertex in some direction is strictly better than every
  other point, and is a vertex.

## Implementation notes

The adjacency lemma is proved directly, without the theory of faces of polytopes. Let `w` strictly
expose the vertex `x`; every other point of `𝒳` is `y = x + d_y a_y` with `d_y = ⟪x - y, w⟫ > 0`
and `⟪a_y, w⟫ = -1`. A vertex `b` of the finite set `{a_y}` maximizing `⟪·, θ⟫` is strictly
exposed by some `ψ`; then `φ = ψ + ⟪b, ψ⟫ w` is maximized over `𝒳` exactly at `x` and at the
points of the ray `x + ℝ₊ b`, and the farthest such point `z` is a vertex adjacent to `x` with
`⟪z - x, θ⟫ > 0`. The usual proof deduces the adjacency lemma from the cone property of polytopes
(Ziegler, *Lectures on Polytopes*, Lemma 3.6), which is proved here as a consequence
(`Set.Finite.smul_mem_convexHull_image_adjacentTo`).

## Tags

polytope, vertex, edge, exposed point, adjacency, convex hull
-/

@[expose] public section

open Filter Topology
open scoped RealInnerProductSpace

namespace Set

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {𝒳 s : Set E} {x z w : E}
  {c : ℝ}

/-- `y ↦ ⟪y, w⟫` is linear. -/
private lemma isLinearMap_inner_left (w : E) : IsLinearMap ℝ fun y : E ↦ ⟪y, w⟫ :=
  ⟨fun a b ↦ inner_add_left a b w, fun r a ↦ real_inner_smul_left a w r⟩

/-- If `⟪·, w⟫ ≤ c` on `s`, a point `z` of the convex hull of `s` with `c ≤ ⟪z, w⟫` is a convex
combination of the points `y ∈ s` with `⟪y, w⟫ = c`: the maximizers of a linear form over `conv s`
are the convex combinations of its maximizers in `s`. -/
lemma mem_convexHull_setOf_inner_eq (hs : ∀ y ∈ s, ⟪y, w⟫ ≤ c) (hz : z ∈ convexHull ℝ s)
    (hzc : c ≤ ⟪z, w⟫) :
    z ∈ convexHull ℝ {y ∈ s | ⟪y, w⟫ = c} := by
  set s₁ := {y ∈ s | ⟪y, w⟫ = c}
  set s₂ := {y ∈ s | ⟪y, w⟫ < c}
  have hlt : convexHull ℝ s₂ ⊆ {y | ⟪y, w⟫ < c} :=
    convexHull_min (fun y hy ↦ hy.2) (convex_halfSpace_lt (isLinearMap_inner_left w) c)
  have hs12 : s = s₁ ∪ s₂ := by
    ext y
    simp only [mem_union, mem_ofPred_eq, s₁, s₂]
    constructor
    · intro hy
      rcases (hs y hy).eq_or_lt with h | h
      exacts [Or.inl ⟨hy, h⟩, Or.inr ⟨hy, h⟩]
    · rintro (h | h) <;> exact h.1
  rcases s₂.eq_empty_or_nonempty with h₂ | h₂
  · rwa [hs12, h₂, union_empty] at hz
  rcases s₁.eq_empty_or_nonempty with h₁ | h₁
  · rw [hs12, h₁, empty_union] at hz
    exact absurd hzc (hlt hz).not_ge
  rw [hs12, convexHull_union h₁ h₂, mem_convexJoin] at hz
  obtain ⟨a, ha, b, hb, hz⟩ := hz
  have ha' : ⟪a, w⟫ = c := convexHull_min (fun y hy ↦ hy.2)
    (convex_hyperplane (isLinearMap_inner_left w) c) ha
  have hb' : ⟪b, w⟫ < c := hlt hb
  rw [segment_eq_image] at hz
  obtain ⟨t, ⟨ht0, -⟩, rfl⟩ := hz
  obtain rfl : t = 0 := by
    refine le_antisymm ?_ ht0
    by_contra! ht
    simp only [inner_add_left, inner_smul_left, ha', RCLike.conj_to_real] at hzc
    nlinarith
  simpa using ha

/-- A point of `𝒳` strictly better than the other points of `𝒳` in some direction is a vertex
of the convex hull of `𝒳`. -/
lemma mem_vertices_of_inner_lt (hx : x ∈ 𝒳) (h : ∀ y ∈ 𝒳, y ≠ x → ⟪y, w⟫ < ⟪x, w⟫) :
    x ∈ vertices 𝒳 := by
  have hle : ∀ y ∈ 𝒳, ⟪y, w⟫ ≤ ⟪x, w⟫ := fun y hy ↦ by
    rcases eq_or_ne y x with rfl | hyx
    exacts [le_rfl, (h y hy hyx).le]
  refine ⟨subset_convexHull ℝ 𝒳 hx, innerSL ℝ w, fun y hy ↦ ⟨?_, fun hxy ↦ ?_⟩⟩
  · rw [innerSL_apply_apply, innerSL_apply_apply, ← real_inner_comm w y, ← real_inner_comm w x]
    exact convexHull_min hle (convex_halfSpace_le (isLinearMap_inner_left w) _) hy
  · rw [innerSL_apply_apply, innerSL_apply_apply, ← real_inner_comm w y,
      ← real_inner_comm w x] at hxy
    have hsub : {y ∈ 𝒳 | ⟪y, w⟫ = ⟪x, w⟫} ⊆ {x} := fun y hy ↦ by
      by_contra hyx
      exact (h y hy.1 hyx).ne hy.2
    simpa using convexHull_mono hsub (mem_convexHull_setOf_inner_eq hle hy hxy)

/-- A vertex of the convex hull of `𝒳` is strictly better than the other points of `𝒳` in some
direction. -/
lemma exists_inner_lt_of_mem_vertices [CompleteSpace E] (hx : x ∈ vertices 𝒳) :
    ∃ w, ∀ y ∈ 𝒳, y ≠ x → ⟪y, w⟫ < ⟪x, w⟫ := by
  obtain ⟨-, l, hl⟩ := hx
  refine ⟨(InnerProductSpace.toDual ℝ E).symm l, fun y hy hyx ↦ ?_⟩
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply, real_inner_comm,
    InnerProductSpace.toDual_symm_apply]
  obtain ⟨h1, h2⟩ := hl y (subset_convexHull ℝ 𝒳 hy)
  exact lt_of_le_of_ne h1 fun h ↦ hyx (h2 h.ge)

/-- A point of `𝒳` is a vertex of the convex hull of `𝒳` if and only if some direction makes it
strictly better than every other point of `𝒳`. -/
lemma mem_vertices_iff_exists_inner_lt [CompleteSpace E] (hx : x ∈ 𝒳) :
    x ∈ vertices 𝒳 ↔ ∃ w, ∀ y ∈ 𝒳, y ≠ x → ⟪y, w⟫ < ⟪x, w⟫ :=
  ⟨exists_inner_lt_of_mem_vertices, fun ⟨_, hw⟩ ↦ mem_vertices_of_inner_lt hx hw⟩

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

/-- The vertices adjacent to a vertex of a finite set form a finite set. -/
lemma finite_adjacentTo (h𝒳 : 𝒳.Finite) : (adjacentTo 𝒳 x).Finite :=
  h𝒳.subset fun _ hz ↦ vertices_subset hz.2.1

/-- For a finite set `𝒳`, the extreme points of `conv 𝒳` are exposed points. -/
lemma mem_vertices_of_mem_extremePoints [CompleteSpace E] (h𝒳 : 𝒳.Finite)
    (hx : x ∈ (convexHull ℝ 𝒳).extremePoints ℝ) : x ∈ vertices 𝒳 := by
  have hx𝒳 : x ∈ 𝒳 := extremePoints_convexHull_subset hx
  have hnot : x ∉ convexHull ℝ (𝒳 \ {x}) := by
    intro hmem
    have := inter_extremePoints_subset_extremePoints_of_subset
      (convexHull_mono sdiff_subset) ⟨hmem, hx⟩
    simpa using extremePoints_convexHull_subset this
  obtain ⟨f, u, hfu, hux⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _)
    (h𝒳.sdiff.isCompact_convexHull (𝕜 := ℝ)).isClosed hnot
  refine mem_vertices_of_inner_lt hx𝒳 (w := (InnerProductSpace.toDual ℝ E).symm f)
    fun y hy hyx ↦ ?_
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply, real_inner_comm,
    InnerProductSpace.toDual_symm_apply]
  exact (hfu y (subset_convexHull ℝ _ ⟨hy, hyx⟩)).trans hux

/-- The convex hull of a finite set is the convex hull of its vertices. -/
lemma convexHull_vertices [CompleteSpace E] (h𝒳 : 𝒳.Finite) :
    convexHull ℝ (vertices 𝒳) = convexHull ℝ 𝒳 := by
  refine (convexHull_mono vertices_subset).antisymm ?_
  calc convexHull ℝ 𝒳
      = closure (convexHull ℝ ((convexHull ℝ 𝒳).extremePoints ℝ)) :=
        (closure_convexHull_extremePoints (h𝒳.isCompact_convexHull (𝕜 := ℝ))
          (convex_convexHull ℝ 𝒳)).symm
    _ ⊆ convexHull ℝ (vertices 𝒳) :=
        closure_minimal (convexHull_mono fun _ hy ↦ h𝒳.mem_vertices_of_mem_extremePoints hy)
          ((h𝒳.subset vertices_subset).isCompact_convexHull (𝕜 := ℝ)).isClosed

/-- The maximum of `⟪·, θ⟫` over a finite nonempty set is attained at a vertex. -/
lemma exists_mem_vertices_forall_inner_le [CompleteSpace E] (h𝒳 : 𝒳.Finite)
    (hne : 𝒳.Nonempty) (θ : E) :
    ∃ v ∈ vertices 𝒳, ∀ y ∈ 𝒳, ⟪y, θ⟫ ≤ ⟪v, θ⟫ := by
  have hVne : (vertices 𝒳).Nonempty := by
    rw [← convexHull_nonempty_iff (𝕜 := ℝ), h𝒳.convexHull_vertices]
    exact hne.convexHull
  obtain ⟨v, hv, hvmax⟩ :=
    Set.exists_max_image _ (fun y ↦ ⟪y, θ⟫) (h𝒳.subset vertices_subset) hVne
  refine ⟨v, hv, fun y hy ↦ ?_⟩
  have : y ∈ convexHull ℝ (vertices 𝒳) := h𝒳.convexHull_vertices ▸ subset_convexHull ℝ 𝒳 hy
  exact convexHull_min hvmax (convex_halfSpace_le (isLinearMap_inner_left θ) _) this

/-- Lexicographic optimality: if `x` maximizes `⟪·, φ⟫` over the finite set `𝒳` and is strictly
better than the other maximizers for `⟪·, ψ⟫`, then a direction `φ + δ ψ` makes `x` strictly better
than every other point of `𝒳`. -/
lemma exists_inner_lt_of_lex (h𝒳 : 𝒳.Finite) {φ ψ : E} (h₁ : ∀ y ∈ 𝒳, ⟪y, φ⟫ ≤ ⟪x, φ⟫)
    (h₂ : ∀ y ∈ 𝒳, y ≠ x → ⟪y, φ⟫ = ⟪x, φ⟫ → ⟪y, ψ⟫ < ⟪x, ψ⟫) :
    ∃ w, ∀ y ∈ 𝒳, y ≠ x → ⟪y, w⟫ < ⟪x, w⟫ := by
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ y ∈ 𝒳 \ {x}, ⟪y, φ + δ • ψ⟫ < ⟪x, φ + δ • ψ⟫ := by
    rw [h𝒳.sdiff.eventually_all]
    rintro y ⟨hy, hyx⟩
    simp only [inner_add_right, real_inner_smul_right]
    rcases (h₁ y hy).eq_or_lt with heq | hlt
    · filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
      rw [heq]
      gcongr
      exact h₂ y hy hyx heq
    · refine nhdsWithin_le_nhds (Filter.Tendsto.eventually_lt ?_ ?_ hlt)
      · exact (continuous_const.add (continuous_id.mul continuous_const)).tendsto' 0 _ (by simp)
      · exact (continuous_const.add (continuous_id.mul continuous_const)).tendsto' 0 _ (by simp)
  obtain ⟨δ, hδ⟩ := hev.exists
  exact ⟨φ + δ • ψ, fun y hy hyx ↦ hδ y ⟨hy, hyx⟩⟩

end Finite

end General

end Set

namespace Set.Finite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {𝒳 : Set E} {x x' y : E}

/-- Two distinct vertices of a finite set are adjacent if and only if some direction makes them
tie and beat every other vertex. -/
lemma isAdjacent_iff_exists_inner (h𝒳 : 𝒳.Finite) (hx : x ∈ vertices 𝒳)
    (hx' : x' ∈ vertices 𝒳) (hne : x ≠ x') :
    IsAdjacent 𝒳 x x' ↔
      ∃ w, ⟪x, w⟫ = ⟪x', w⟫ ∧ ∀ y ∈ vertices 𝒳, y ≠ x → y ≠ x' → ⟪y, w⟫ < ⟪x, w⟫ := by
  have hx𝒳 : x ∈ 𝒳 := vertices_subset hx
  have hx'𝒳 : x' ∈ 𝒳 := vertices_subset hx'
  constructor
  · rintro ⟨-, -, -, hexp⟩
    obtain ⟨l, hl⟩ := hexp ⟨x, left_mem_segment ℝ x x'⟩
    have hw : ∀ y, ⟪y, (InnerProductSpace.toDual ℝ E).symm l⟫ = l y := fun y ↦ by
      rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    have hmx : x ∈ {y ∈ convexHull ℝ 𝒳 | ∀ z ∈ convexHull ℝ 𝒳, l z ≤ l y} :=
      hl ▸ left_mem_segment ℝ x x'
    have hmx' : x' ∈ {y ∈ convexHull ℝ 𝒳 | ∀ z ∈ convexHull ℝ 𝒳, l z ≤ l y} :=
      hl ▸ right_mem_segment ℝ x x'
    refine ⟨(InnerProductSpace.toDual ℝ E).symm l, ?_, fun y hy hyx hyx' ↦ ?_⟩
    · rw [hw, hw]
      exact le_antisymm (hmx'.2 x hmx.1) (hmx.2 x' hmx'.1)
    · rw [hw, hw]
      refine lt_of_le_of_ne (hmx.2 y hy.1) fun hyl ↦ ?_
      have hyseg : y ∈ segment ℝ x x' := by
        rw [hl]
        exact ⟨hy.1, fun z hz ↦ hyl ▸ hmx.2 z hz⟩
      -- a vertex in the segment `[x, x']` is one of its endpoints
      exact hyx ((exposedPoints_subset_extremePoints hy).2 hmx.1 hmx'.1
        (mem_openSegment_of_ne_left_right hyx.symm hyx'.symm hyseg)).symm
  · rintro ⟨w, hxx', hw⟩
    have hV : ∀ y ∈ vertices 𝒳, ⟪y, w⟫ ≤ ⟪x, w⟫ := fun y hy ↦ by
      rcases eq_or_ne y x with rfl | hyx
      · exact le_rfl
      rcases eq_or_ne y x' with rfl | hyx'
      · exact hxx'.ge
      exact (hw y hy hyx hyx').le
    have hle : ∀ z ∈ convexHull ℝ 𝒳, ⟪z, w⟫ ≤ ⟪x, w⟫ := fun z hz ↦
      convexHull_min hV (convex_halfSpace_le (isLinearMap_inner_left w) _)
        (h𝒳.convexHull_vertices.symm ▸ hz)
    refine ⟨hx, hx', hne, fun _ ↦ ⟨innerSL ℝ w, ?_⟩⟩
    ext y
    simp only [mem_ofPred_eq, innerSL_apply_apply]
    simp_rw [← real_inner_comm w]
    constructor
    · intro hy
      have hyw : ⟪y, w⟫ = ⟪x, w⟫ := by
        rw [← convexHull_pair] at hy
        refine convexHull_min ?_ (convex_hyperplane (isLinearMap_inner_left w) _) hy
        rintro z (rfl | rfl)
        exacts [rfl, hxx'.symm]
      exact ⟨segment_subset_convexHull hx𝒳 hx'𝒳 hy, fun z hz ↦ hyw ▸ hle z hz⟩
    · -- a maximizer is a convex combination of maximizing vertices, here `x` and `x'`
      rintro ⟨hyc, hymax⟩
      have := mem_convexHull_setOf_inner_eq hV (h𝒳.convexHull_vertices.symm ▸ hyc)
        (hymax x (subset_convexHull ℝ 𝒳 hx𝒳))
      rw [← convexHull_pair]
      refine convexHull_mono ?_ this
      rintro z ⟨hz, hzw⟩
      by_contra h
      simp only [mem_insert_iff, mem_singleton_iff, not_or] at h
      exact (hw z hz h.1 h.2).ne hzw

/-- **Local optimality implies global optimality.** If some point of a finite set beats the
vertex `x` in the direction `θ`, then some vertex adjacent to `x` beats it. -/
lemma exists_mem_adjacentTo_inner_pos (h𝒳 : 𝒳.Finite) (hx : x ∈ vertices 𝒳) {θ : E}
    (hy : y ∈ 𝒳) (hθ : 0 < ⟪y - x, θ⟫) :
    ∃ z ∈ adjacentTo 𝒳 x, 0 < ⟪z - x, θ⟫ := by
  have hx𝒳 : x ∈ 𝒳 := vertices_subset hx
  obtain ⟨w, hw⟩ := (mem_vertices_iff_exists_inner_lt hx𝒳).1 hx
  -- the points `y ≠ x` are `x + d y • a y` with `d y > 0` and `⟪a y, w⟫ = -1`
  set S := 𝒳 \ {x} with hS
  set d : E → ℝ := fun y ↦ ⟪x - y, w⟫ with hd_def
  set a : E → E := fun y ↦ (d y)⁻¹ • (y - x) with ha_def
  have hd : ∀ y ∈ S, 0 < d y := fun y hy ↦ by
    simp only [d, inner_sub_left, sub_pos]
    exact hw y hy.1 hy.2
  have hya : ∀ y ∈ S, y - x = d y • a y := fun y hy ↦ by
    simp only [a, smul_smul, mul_inv_cancel₀ (hd y hy).ne', one_smul]
  have hdw : ∀ y, ⟪y - x, w⟫ = -d y := fun y ↦ by
    simp only [d, inner_sub_left]
    ring
  have hyS : y ∈ S := ⟨hy, fun h ↦ by simp only [mem_singleton_iff] at h; simp [h] at hθ⟩
  -- a vertex `b` of the finite set `a '' S` maximizing `θ`, strictly exposed by `ψ`
  have hA : (a '' S).Finite := h𝒳.sdiff.image a
  obtain ⟨b, hbV, hbmax⟩ :=
    hA.exists_mem_vertices_forall_inner_le ⟨a y, mem_image_of_mem a hyS⟩ θ
  obtain ⟨ψ, hψ⟩ := (mem_vertices_iff_exists_inner_lt (vertices_subset hbV)).1 hbV
  have hbθ : 0 < ⟪b, θ⟫ := by
    refine lt_of_lt_of_le ?_ (hbmax _ (mem_image_of_mem a hyS))
    simp only [a, real_inner_smul_left]
    exact mul_pos (inv_pos.2 (hd y hyS)) hθ
  -- `z`: the farthest point of `S` on the ray `x + ℝ₊ b`
  obtain ⟨y₁, hy₁S, hy₁b⟩ := vertices_subset hbV
  obtain ⟨z, ⟨hzS, hzb⟩, hzmax⟩ := Set.exists_max_image {y' ∈ S | a y' = b} d
    (h𝒳.sdiff.subset (sep_subset _ _)) ⟨y₁, hy₁S, hy₁b⟩
  -- the direction `φ`, maximized over `𝒳` exactly at `x` and at the points of the ray
  set φ := ψ + ⟪b, ψ⟫ • w with hφ_def
  have hφ : ∀ y' ∈ S, ⟪y', φ⟫ = ⟪x, φ⟫ + d y' * (⟪a y', ψ⟫ - ⟪b, ψ⟫) := fun y' hy' ↦ by
    have h1 : ⟪y' - x, φ⟫ = d y' * (⟪a y', ψ⟫ - ⟪b, ψ⟫) := by
      rw [hφ_def, inner_add_right, real_inner_smul_right, hdw, hya y' hy', real_inner_smul_left]
      ring
    rw [inner_sub_left] at h1
    linarith
  have hψle : ∀ y' ∈ S, ⟪a y', ψ⟫ ≤ ⟪b, ψ⟫ := fun y' hy' ↦ by
    rcases eq_or_ne (a y') b with h | h
    · rw [h]
    · exact (hψ _ (mem_image_of_mem a hy') h).le
  have hφle : ∀ y' ∈ 𝒳, ⟪y', φ⟫ ≤ ⟪x, φ⟫ := fun y' hy' ↦ by
    rcases eq_or_ne y' x with rfl | hy'x
    · exact le_rfl
    rw [hφ y' ⟨hy', hy'x⟩]
    have := mul_nonpos_of_nonneg_of_nonpos (hd y' ⟨hy', hy'x⟩).le
      (sub_nonpos.2 (hψle y' ⟨hy', hy'x⟩))
    linarith
  have hzφ : ⟪z, φ⟫ = ⟪x, φ⟫ := by rw [hφ z hzS, hzb, sub_self, mul_zero, add_zero]
  -- the other maximizers of `φ` are on the ray, closer to `x` than `z`
  have htie : ∀ y' ∈ S, y' ≠ z → ⟪y', φ⟫ = ⟪x, φ⟫ → a y' = b ∧ d y' < d z := by
    intro y' hy' hy'z hy'φ
    have hab : a y' = b := by
      by_contra h
      have := hψ _ (mem_image_of_mem a hy') h
      rw [hφ y' hy'] at hy'φ
      have := mul_neg_of_pos_of_neg (hd y' hy') (sub_neg.2 this)
      linarith
    refine ⟨hab, lt_of_le_of_ne (hzmax y' ⟨hy', hab⟩) fun hdz ↦ hy'z ?_⟩
    have := hya y' hy'
    rw [hdz, hab, ← hzb, ← hya z hzS] at this
    simpa using this
  -- `z` is a vertex: it maximizes `φ`, and then `-w`
  have hzV : z ∈ vertices 𝒳 := by
    refine (mem_vertices_iff_exists_inner_lt hzS.1).2
      (h𝒳.exists_inner_lt_of_lex (φ := φ) (ψ := -w) (fun y' hy' ↦ hzφ ▸ hφle y' hy') ?_)
    intro y' hy' hy'z hy'φ
    have hdlt : d y' < d z := by
      rcases eq_or_ne y' x with rfl | hy'x
      · simpa [d] using hd z hzS
      · exact (htie y' ⟨hy', hy'x⟩ hy'z (hy'φ.trans hzφ)).2
    simp only [d, inner_sub_left] at hdlt
    simp only [inner_neg_right]
    linarith
  refine ⟨z, ?_, ?_⟩
  · -- `φ` exposes the edge `[x, z]`: a vertex on the ray strictly before `z` is not extreme
    refine (h𝒳.isAdjacent_iff_exists_inner hx hzV (Ne.symm hzS.2)).2
      ⟨φ, hzφ.symm, fun v hv hvx hvz ↦ lt_of_le_of_ne (hφle v (vertices_subset hv)) fun hvφ ↦ ?_⟩
    have hvS : v ∈ S := ⟨vertices_subset hv, hvx⟩
    obtain ⟨hab, hdlt⟩ := htie v hvS hvz hvφ
    refine hvx ((exposedPoints_subset_extremePoints hv).2 (subset_convexHull ℝ 𝒳 hx𝒳)
      (subset_convexHull ℝ 𝒳 hzS.1) ?_).symm
    rw [openSegment_eq_image']
    refine ⟨d v / d z, ⟨div_pos (hd v hvS) (hd z hzS), (div_lt_one (hd z hzS)).2 hdlt⟩, ?_⟩
    dsimp only
    rw [hya z hzS, hzb, smul_smul, div_mul_cancel₀ _ (hd z hzS).ne', ← hab, ← hya v hvS]
    abel
  · rw [hya z hzS, real_inner_smul_left, hzb]
    exact mul_pos (hd z hzS) hbθ

/-- If some point of a finite set other than the vertex `x` is at least as good as `x` in the
direction `θ`, then so is some vertex adjacent to `x`. -/
lemma exists_mem_adjacentTo_inner_nonneg (h𝒳 : 𝒳.Finite) (hx : x ∈ vertices 𝒳) {θ : E}
    (hy : y ∈ 𝒳) (hyx : y ≠ x) (hθ : 0 ≤ ⟪y - x, θ⟫) :
    ∃ z ∈ adjacentTo 𝒳 x, 0 ≤ ⟪z - x, θ⟫ := by
  by_contra! h
  -- perturb `θ` to `θ + ε (y - x)`: the finitely many adjacent vertices still lose for small `ε`
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ z ∈ adjacentTo 𝒳 x, ⟪z - x, θ + ε • (y - x)⟫ < 0 := by
    rw [h𝒳.finite_adjacentTo.eventually_all]
    intro z hz
    simp only [inner_add_right, real_inner_smul_right]
    exact Filter.Tendsto.eventually_lt
      ((continuous_const.add (continuous_id.mul continuous_const)).tendsto' 0 _ (by simp))
      tendsto_const_nhds (h z hz)
  obtain ⟨ε, hε, hεpos⟩ :=
    ((hev.filter_mono (nhdsWithin_le_nhds (s := Ioi 0))).and self_mem_nhdsWithin).exists
  have hpos : 0 < ⟪y - x, θ + ε • (y - x)⟫ := by
    rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    have : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hyx)
    have : 0 < ε := hεpos
    positivity
  obtain ⟨z, hz, hzpos⟩ := h𝒳.exists_mem_adjacentTo_inner_pos hx hy hpos
  exact (hε z hz).not_gt hzpos

/-- A vertex of a finite set with another point has an adjacent vertex. -/
lemma adjacentTo_nonempty (h𝒳 : 𝒳.Finite) (hx : x ∈ vertices 𝒳) (hy : y ∈ 𝒳) (hyx : y ≠ x) :
    (adjacentTo 𝒳 x).Nonempty := by
  have hpos : 0 < ⟪y - x, y - x⟫ := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_pos (norm_pos_iff.2 (sub_ne_zero.2 hyx)) 2
  obtain ⟨z, hz, -⟩ := h𝒳.exists_mem_adjacentTo_inner_pos hx hy hpos
  exact ⟨z, hz⟩

/-- **Cone property** at a strict maximizer. Let `x ∈ 𝒳` be the unique maximizer of `⟪·, θ⟫` over
the finite set `𝒳`, and for `y ≠ x` let `u y = (x - y) / ⟪x - y, θ⟫` (a point of the hyperplane
`⟪·, θ⟫ = 1`). Then `u y` is a convex combination of the `u z` for the vertices `z` adjacent
to `x`. -/
lemma smul_mem_convexHull_image_adjacentTo (h𝒳 : 𝒳.Finite) {θ : E} (hx : x ∈ 𝒳)
    (hmax : ∀ y ∈ 𝒳, y ≠ x → ⟪y, θ⟫ < ⟪x, θ⟫) (hy : y ∈ 𝒳) (hyx : y ≠ x) :
    ⟪x - y, θ⟫⁻¹ • (x - y) ∈
      convexHull ℝ ((fun z ↦ ⟪x - z, θ⟫⁻¹ • (x - z)) '' adjacentTo 𝒳 x) := by
  set u : E → E := fun z ↦ ⟪x - z, θ⟫⁻¹ • (x - z) with hu_def
  have hxV : x ∈ vertices 𝒳 := mem_vertices_of_inner_lt hx hmax
  -- otherwise, separate `u y` from the convex hull of the `u z`
  by_contra hnot
  obtain ⟨f, c, hfc, hcf⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _)
    ((h𝒳.finite_adjacentTo.image u).isCompact_convexHull (𝕜 := ℝ)).isClosed hnot
  set φ := (InnerProductSpace.toDual ℝ E).symm f
  have hφ : ∀ v, ⟪v, φ⟫ = f v := fun v ↦ by
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  -- `ψ = c θ - φ` has `⟪z - x, ψ⟫ < 0` for every adjacent `z` and `⟪y - x, ψ⟫ > 0`
  have key : ∀ z ∈ 𝒳, z ≠ x →
      ⟪z - x, c • θ - φ⟫ = -⟪x - z, θ⟫ * (c - f (u z)) ∧ 0 < ⟪x - z, θ⟫ := by
    intro z hz hzx
    have hδ : 0 < ⟪x - z, θ⟫ := by rw [inner_sub_left, sub_pos]; exact hmax z hz hzx
    refine ⟨?_, hδ⟩
    have hxz : ⟪x - z, φ⟫ = ⟪x - z, θ⟫ * f (u z) := by
      rw [← hφ, real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul]
    rw [← neg_sub x z, inner_neg_left, inner_sub_right, real_inner_smul_right, hxz]
    ring
  obtain ⟨z, hz, hzpos⟩ := h𝒳.exists_mem_adjacentTo_inner_pos hxV hy (θ := c • θ - φ) (by
    obtain ⟨h1, h2⟩ := key y hy hyx
    rw [h1]
    nlinarith)
  obtain ⟨h1, h2⟩ := key z (vertices_subset hz.2.1) hz.2.2.1.symm
  have := hfc (u z) (subset_convexHull ℝ _ (mem_image_of_mem u hz))
  rw [h1] at hzpos
  nlinarith

/-- A point of a finite set strictly better than every other vertex in the direction `θ` is
strictly better than every other point of the set. -/
lemma inner_lt_of_forall_mem_vertices (h𝒳 : 𝒳.Finite) {θ : E}
    (h : ∀ v ∈ vertices 𝒳, v ≠ x → ⟪v, θ⟫ < ⟪x, θ⟫) (hy : y ∈ 𝒳) (hyx : y ≠ x) :
    ⟪y, θ⟫ < ⟪x, θ⟫ := by
  have hV : ∀ v ∈ vertices 𝒳, ⟪v, θ⟫ ≤ ⟪x, θ⟫ := fun v hv ↦ by
    rcases eq_or_ne v x with rfl | hvx
    exacts [le_rfl, (h v hv hvx).le]
  have hsub : {v ∈ vertices 𝒳 | ⟪v, θ⟫ = ⟪x, θ⟫} ⊆ {x} := fun v hv ↦ by
    by_contra hvx
    exact (h v hv.1 hvx).ne hv.2
  refine lt_of_not_ge fun hle ↦ hyx ?_
  -- `y` is a convex combination of maximizing vertices, and `x` is the only one
  simpa using convexHull_mono hsub (mem_convexHull_setOf_inner_eq hV
    (h𝒳.convexHull_vertices.symm ▸ subset_convexHull ℝ 𝒳 hy) hle)

/-- A point of a finite set strictly better than every other vertex in some direction is a
vertex. -/
lemma mem_vertices_of_forall_mem_vertices (h𝒳 : 𝒳.Finite) (hx : x ∈ 𝒳) {θ : E}
    (h : ∀ v ∈ vertices 𝒳, v ≠ x → ⟪v, θ⟫ < ⟪x, θ⟫) : x ∈ vertices 𝒳 :=
  mem_vertices_of_inner_lt hx fun _ hy hyx ↦ h𝒳.inner_lt_of_forall_mem_vertices h hy hyx

/-- A finite set with two points has two adjacent vertices. -/
lemma exists_isAdjacent (h𝒳 : 𝒳.Finite) (hnt : 𝒳.Nontrivial) : ∃ x x', IsAdjacent 𝒳 x x' := by
  obtain ⟨x, hx, hmax⟩ := Set.exists_max_image 𝒳 (fun y ↦ ‖y‖) h𝒳 hnt.nonempty
  obtain ⟨y, hy, hyx⟩ := hnt.exists_ne x
  obtain ⟨x', hx'⟩ := h𝒳.adjacentTo_nonempty (mem_vertices_of_forall_norm_le hx hmax) hy hyx
  exact ⟨x, x', hx'⟩

end Set.Finite
