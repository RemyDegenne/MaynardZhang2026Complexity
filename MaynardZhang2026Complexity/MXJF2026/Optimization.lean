/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.MXJF2026.Lemma4
public import MaynardZhang2026Complexity.LeanMachineLearning.DesignMahalanobis
public import MaynardZhang2026Complexity.Mathlib.Analysis.Convex.AdjacentNonempty

/-!
# The optimization problems of the lower bound

Properties of the inner problem `pairValue`, of its value `f(𝒳, Δ)` over designs (`optValue`)
and of the complexity `H_Adjacent(𝒳, Δ)` (`hAdjacent`), used in the proofs of Lemma 3 and
Theorem 1.

## Main statements

* `exists_pairFeasible`: the inner problem of a pair of distinct vertices is feasible;
* `optValue_pos`: `f(𝒳, Δ) > 0` when `𝒳` has two points and `Δ > 0`;
* `exists_pairFeasible_lt_two_mul_optValue`: for every design `λ`, some pair of distinct
  vertices has a feasible point with `vᵀ A(λ) v < 2 f(𝒳, Δ)`;
* `hAdjacent_pos`, `optValue_le`: `H_Adjacent(𝒳, Δ) > 0` and `f(𝒳, Δ) ≤ 4 / H_Adjacent(𝒳, Δ)`
  for a spanning `𝒳` with two points.

## Proof outline

* `f(𝒳, Δ)` is a supremum over designs of `min_{𝒴} p_{A(λ)}`, bounded above by fixing a feasible
  `v` for one pair: `vᵀ A(λ) v ≤ ∑_{y ∈ 𝒳} ⟪y, v⟫²` for every design
  (`bddAbove_range_iInf_pairValue`); it is positive through the uniform design, for which every
  pair has value at least `2 Δ² / |𝒳|` (`le_pairValue_inv_card_smul_sum_outerSelf`).
* `adjDesignValue 𝒳 > 0`: by the Cauchy–Schwarz inequality `‖z‖⁴ ≤ ‖z‖²_{A⁻¹} ‖z‖²_A` and
  `‖z‖²_{A(λ)} ≤ ∑_{y ∈ 𝒳} ⟪y, z⟫²`, for `z = x - x'` with `(x, x')` an adjacent pair.
* `optValue_le`: for a design `λ` and `ε > 0`, `A_ε = (A(λ) + ε A₀) / (1 + ε)` (with `A₀` a
  positive definite design matrix) is a positive definite design matrix and
  `A(λ) ≤ (1 + ε) A_ε`; monotonicity and homogeneity of `pairValue` and Lemma 4 at an adjacent
  pair maximizing `‖x - x'‖²_{A_ε⁻¹}` give `min_{𝒴} p_{A(λ)} ≤ (1 + ε) 4 Δ² / adjDesignValue 𝒳`
  (`iInf_pairValue_le_one_add_mul`); let `ε → 0`.
-/

@[expose] public section

open Learning Matrix Set
open scoped RealInnerProductSpace MatrixOrder

namespace MaynardZhang2026Complexity

variable {ι : Type*} [Fintype ι]

/-- The inner optimization problem of a pair of distinct vertices is feasible. -/
lemma exists_pairFeasible (𝒳 : Finset (EuclideanSpace ℝ ι)) (Δ : ℝ)
    {x x' : EuclideanSpace ℝ ι} (hxx' : (x, x') ∈ vertexPairs (𝒳 : Set (EuclideanSpace ℝ ι))) :
    ∃ θ v, PairFeasible 𝒳 Δ x x' θ v :=
  exists_pairFeasible_of_finite 𝒳.finite_toSet Δ hxx'

omit [Fintype ι] in
/-- A finite set with two points has a pair of distinct vertices. -/
lemma nonempty_vertexPairs [Finite ι] (𝒳 : Finset (EuclideanSpace ℝ ι)) (h𝒳 : 𝒳.Nontrivial) :
    (vertexPairs (𝒳 : Set (EuclideanSpace ℝ ι))).Nonempty := by
  have := Fintype.ofFinite ι
  obtain ⟨x, x', h⟩ := 𝒳.finite_toSet.exists_isAdjacent h𝒳
  exact ⟨(x, x'), adjacentPairs_subset_vertexPairs h⟩

omit [Fintype ι] in
/-- The index type of a Euclidean space with two distinct points is nonempty. -/
lemma nonempty_index_of_nontrivial {𝒳 : Set (EuclideanSpace ℝ ι)} (h𝒳 : 𝒳.Nontrivial) :
    Nonempty ι := by
  by_contra hι
  rw [not_nonempty_iff] at hι
  obtain ⟨a, -, b, -, hab⟩ := h𝒳
  exact hab (WithLp.ofLp_injective 2 (funext fun i ↦ isEmptyElim i))

/-- For the design matrix `|𝒳|⁻¹ ∑_{y ∈ 𝒳} y yᵀ` of the uniform design, the inner problem of every
pair of distinct vertices has value at least `2 Δ² / |𝒳|`. -/
lemma le_pairValue_inv_card_smul_sum_outerSelf (𝒳 : Finset (EuclideanSpace ℝ ι)) {Δ : ℝ}
    (hΔ : 0 < Δ) {x x' : EuclideanSpace ℝ ι}
    (hxx' : (x, x') ∈ vertexPairs (𝒳 : Set (EuclideanSpace ℝ ι))) :
    2 * Δ ^ 2 / 𝒳.card ≤ pairValue 𝒳 Δ ((𝒳.card : ℝ)⁻¹ • ∑ y ∈ 𝒳, outerSelf y) x x' := by
  classical
  refine le_pairValue_of_forall (exists_pairFeasible 𝒳 Δ hxx') fun θ v h ↦ ?_
  have h2 := h.two_mul_le_inner hxx'
  have hx : x ∈ 𝒳 := Finset.mem_coe.1 (vertices_subset hxx'.1)
  have hx' : x' ∈ 𝒳 := Finset.mem_coe.1 (vertices_subset hxx'.2.1)
  have hsum : ⟪x, v⟫ ^ 2 + ⟪x', v⟫ ^ 2 ≤ ∑ y ∈ 𝒳, ⟪y, v⟫ ^ 2 := by
    rw [← Finset.sum_pair (f := fun y ↦ ⟪y, v⟫ ^ 2) hxx'.2.2]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.insert_subset_iff.2 ⟨hx, Finset.singleton_subset_iff.2 hx'⟩)
      fun _ _ _ ↦ sq_nonneg _
  rw [inner_sub_left] at h2
  rw [mahalanobisSq_inv_card_smul_sum_outerSelf, div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  nlinarith [sq_nonneg (⟪x, v⟫ + ⟪x', v⟫)]

/-- The values `min_{𝒴} p_{A(λ)}` of the designs `λ` in the definition of `f(𝒳, Δ)` are bounded
above. -/
lemma bddAbove_range_iInf_pairValue (𝒳 : Finset (EuclideanSpace ℝ ι)) (h𝒳 : 𝒳.Nontrivial)
    (Δ : ℝ) :
    BddAbove (range fun w : {w // IsDesign (𝒳 : Set (EuclideanSpace ℝ ι)) w} ↦
      ⨅ p : vertexPairs (𝒳 : Set (EuclideanSpace ℝ ι)),
        pairValue 𝒳 Δ (designMatrix (w : EuclideanSpace ℝ ι →₀ ℝ)) p.1.1 p.1.2) := by
  obtain ⟨p, hp⟩ := nonempty_vertexPairs 𝒳 h𝒳
  obtain ⟨θ, v, h⟩ := exists_pairFeasible 𝒳 Δ hp
  refine ⟨∑ y ∈ 𝒳, ⟪y, v⟫ ^ 2, ?_⟩
  rintro _ ⟨w, rfl⟩
  have hA := w.2.posSemidef_designMatrix
  calc ⨅ p : vertexPairs (𝒳 : Set (EuclideanSpace ℝ ι)),
        pairValue 𝒳 Δ (designMatrix (w : EuclideanSpace ℝ ι →₀ ℝ)) p.1.1 p.1.2
      ≤ pairValue 𝒳 Δ (designMatrix (w : EuclideanSpace ℝ ι →₀ ℝ)) p.1 p.2 :=
        ciInf_le (bddBelow_range_pairValue hA) ⟨p, hp⟩
    _ ≤ mahalanobisSq (designMatrix (w : EuclideanSpace ℝ ι →₀ ℝ)) v :=
        pairValue_le_mahalanobisSq hA h
    _ ≤ ∑ y ∈ 𝒳, ⟪y, v⟫ ^ 2 := w.2.mahalanobisSq_designMatrix_le v

/-- The value `min_{𝒴} p_{A(λ)}` of a design `λ` is at most `f(𝒳, Δ)`. -/
lemma iInf_pairValue_le_optValue (𝒳 : Finset (EuclideanSpace ℝ ι)) (h𝒳 : 𝒳.Nontrivial)
    (Δ : ℝ) {w : EuclideanSpace ℝ ι →₀ ℝ} (hw : IsDesign (𝒳 : Set (EuclideanSpace ℝ ι)) w) :
    ⨅ p : vertexPairs (𝒳 : Set (EuclideanSpace ℝ ι)), pairValue 𝒳 Δ (designMatrix w) p.1.1 p.1.2
      ≤ optValue (𝒳 : Set (EuclideanSpace ℝ ι)) Δ :=
  le_ciSup (bddAbove_range_iInf_pairValue 𝒳 h𝒳 Δ) ⟨w, hw⟩

/-- The value `f(𝒳, Δ)` of the optimization problem of Lemma 3 is positive when `𝒳` has two
points and `Δ > 0`. -/
lemma optValue_pos (𝒳 : Finset (EuclideanSpace ℝ ι)) (h𝒳 : 𝒳.Nontrivial) {Δ : ℝ}
    (hΔ : 0 < Δ) :
    0 < optValue (𝒳 : Set (EuclideanSpace ℝ ι)) Δ := by
  have hne : 𝒳.Nonempty := h𝒳.nonempty
  obtain ⟨w, hw, hwA⟩ :=
    mem_designSet_iff.1 (inv_card_smul_sum_outerSelf_mem_designSet hne subset_rfl)
  have : Nonempty (vertexPairs (𝒳 : Set (EuclideanSpace ℝ ι))) :=
    (nonempty_vertexPairs 𝒳 h𝒳).to_subtype
  have hcard : (0 : ℝ) < 𝒳.card := by exact_mod_cast hne.card_pos
  calc 0 < 2 * Δ ^ 2 / 𝒳.card := by positivity
    _ ≤ ⨅ p : vertexPairs (𝒳 : Set (EuclideanSpace ℝ ι)),
        pairValue 𝒳 Δ (designMatrix w) p.1.1 p.1.2 :=
      le_ciInf fun p ↦ by rw [hwA]; exact le_pairValue_inv_card_smul_sum_outerSelf 𝒳 hΔ p.2
    _ ≤ optValue (𝒳 : Set (EuclideanSpace ℝ ι)) Δ := iInf_pairValue_le_optValue 𝒳 h𝒳 Δ hw

/-- For every design `λ`, some pair of distinct vertices has a feasible point `(θ, v)` with
`vᵀ A(λ) v < 2 f(𝒳, Δ)`. -/
lemma exists_pairFeasible_lt_two_mul_optValue (𝒳 : Finset (EuclideanSpace ℝ ι))
    (h𝒳 : 𝒳.Nontrivial) {Δ : ℝ} (hΔ : 0 < Δ) {w : EuclideanSpace ℝ ι →₀ ℝ}
    (hw : IsDesign 𝒳 w) :
    ∃ x x' θ v, (x, x') ∈ vertexPairs (𝒳 : Set (EuclideanSpace ℝ ι)) ∧
      PairFeasible 𝒳 Δ x x' θ v ∧
      mahalanobisSq (designMatrix w) v < 2 * optValue (𝒳 : Set (EuclideanSpace ℝ ι)) Δ := by
  have hpos := optValue_pos 𝒳 h𝒳 hΔ
  have : Nonempty (vertexPairs (𝒳 : Set (EuclideanSpace ℝ ι))) :=
    (nonempty_vertexPairs 𝒳 h𝒳).to_subtype
  obtain ⟨p, hp⟩ := exists_lt_of_ciInf_lt
    ((iInf_pairValue_le_optValue 𝒳 h𝒳 Δ hw).trans_lt (by linarith :
      optValue (𝒳 : Set (EuclideanSpace ℝ ι)) Δ < 2 * optValue (𝒳 : Set (EuclideanSpace ℝ ι)) Δ))
  obtain ⟨θ, v, h, hv⟩ := exists_pairFeasible_lt_of_pairValue_lt (exists_pairFeasible 𝒳 Δ p.2) hp
  exact ⟨p.1.1, p.1.2, θ, v, p.2, h, hv⟩

variable [DecidableEq ι]

/-- The squared norms `‖x - x'‖²_{A⁻¹}` of the adjacent pairs of a finite set are bounded
above. -/
lemma bddAbove_range_mahalanobisSq_adjacentPairs (𝒳 : Finset (EuclideanSpace ℝ ι))
    (A : Matrix ι ι ℝ) :
    BddAbove (range fun p : adjacentPairs (𝒳 : Set (EuclideanSpace ℝ ι)) ↦
      mahalanobisSq A⁻¹ (p.1.1 - p.1.2)) := by
  have : Finite (adjacentPairs (𝒳 : Set (EuclideanSpace ℝ ι))) :=
    ((𝒳.finite_toSet.subset vertices_subset).offDiag.subset
      adjacentPairs_subset_vertexPairs).to_subtype
  exact (finite_range _).bddAbove

/-- The values `max_{ℐ} ‖x - x'‖²_{A(λ)⁻¹}` of the designs with positive definite design matrix
are nonnegative, hence bounded below. -/
lemma bddBelow_range_adjValue (𝒳 : Set (EuclideanSpace ℝ ι)) :
    BddBelow (range fun w : PosDefDesign 𝒳 ↦
      adjValue 𝒳 (designMatrix (w : EuclideanSpace ℝ ι →₀ ℝ))) :=
  ⟨0, by
    rintro _ ⟨w, rfl⟩
    exact Real.iSup_nonneg fun _ ↦ w.2.2.inv.posSemidef.mahalanobisSq_nonneg _⟩

/-- The value `min_λ max_{ℐ} ‖x - x'‖²_{A(λ)⁻¹}` of the adjacent-optimal design is positive for
a spanning `𝒳` with two points. -/
lemma adjDesignValue_pos (𝒳 : Finset (EuclideanSpace ℝ ι)) (h𝒳 : 𝒳.Nontrivial)
    (hspan : Submodule.span ℝ (𝒳 : Set (EuclideanSpace ℝ ι)) = ⊤) :
    0 < adjDesignValue (𝒳 : Set (EuclideanSpace ℝ ι)) := by
  have := nonempty_index_of_nontrivial (𝒳 := (𝒳 : Set (EuclideanSpace ℝ ι))) h𝒳
  obtain ⟨x, x', hadj⟩ := 𝒳.finite_toSet.exists_isAdjacent h𝒳
  obtain ⟨A₀, hA₀, hA₀pd⟩ := exists_posDef_mem_designSet hspan
  obtain ⟨w₀, hw₀, rfl⟩ := mem_designSet_iff.1 hA₀
  have : Nonempty (PosDefDesign (𝒳 : Set (EuclideanSpace ℝ ι))) := ⟨⟨w₀, hw₀, hA₀pd⟩⟩
  set z := x - x'
  have hz : 0 < ‖z‖ ^ 2 := by
    have : z ≠ 0 := sub_ne_zero.2 hadj.ne
    positivity
  set K := ∑ y ∈ 𝒳, ⟪y, z⟫ ^ 2
  -- for every positive definite design, `‖z‖⁴ ≤ ‖z‖²_{A⁻¹} K` (Cauchy–Schwarz)
  have key : ∀ w : PosDefDesign (𝒳 : Set (EuclideanSpace ℝ ι)),
      (‖z‖ ^ 2) ^ 2 ≤ mahalanobisSq (designMatrix (w : EuclideanSpace ℝ ι →₀ ℝ))⁻¹ z * K := by
    intro w
    calc (‖z‖ ^ 2) ^ 2 = ⟪z, z⟫ ^ 2 := by rw [real_inner_self_eq_norm_sq]
      _ ≤ mahalanobisSq (designMatrix (w : EuclideanSpace ℝ ι →₀ ℝ))⁻¹ z *
          mahalanobisSq (designMatrix (w : EuclideanSpace ℝ ι →₀ ℝ)) z :=
        w.2.2.inner_sq_le_mahalanobisSq_inv_mul z z
      _ ≤ mahalanobisSq (designMatrix (w : EuclideanSpace ℝ ι →₀ ℝ))⁻¹ z * K :=
        mul_le_mul_of_nonneg_left (w.2.1.mahalanobisSq_designMatrix_le z)
          (w.2.2.inv.posSemidef.mahalanobisSq_nonneg z)
  have hK : 0 < K := by
    refine lt_of_le_of_ne (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) fun hK0 ↦ ?_
    have h := key ⟨w₀, hw₀, hA₀pd⟩
    rw [← hK0, mul_zero] at h
    linarith [pow_pos hz 2]
  refine (div_pos (pow_pos hz 2) hK).trans_le (le_ciInf fun w ↦ ?_)
  rw [div_le_iff₀ hK]
  refine (key w).trans (mul_le_mul_of_nonneg_right ?_ hK.le)
  exact le_ciSup (bddAbove_range_mahalanobisSq_adjacentPairs 𝒳 _)
    (⟨(x, x'), hadj⟩ : adjacentPairs (𝒳 : Set (EuclideanSpace ℝ ι)))

/-- The complexity `H_Adjacent(𝒳, Δ)` is positive for a spanning `𝒳` with two points. -/
lemma hAdjacent_pos (𝒳 : Finset (EuclideanSpace ℝ ι)) (h𝒳 : 𝒳.Nontrivial)
    (hspan : Submodule.span ℝ (𝒳 : Set (EuclideanSpace ℝ ι)) = ⊤) {Δ : ℝ} (hΔ : 0 < Δ) :
    0 < hAdjacent (𝒳 : Set (EuclideanSpace ℝ ι)) Δ :=
  div_pos (adjDesignValue_pos 𝒳 h𝒳 hspan) (by positivity)

/-- For a design `λ` and `ε > 0`, `min_{𝒴} p_{A(λ)} ≤ (1 + ε) 4 Δ² / adjDesignValue 𝒳`, through
the positive definite design matrix `A_ε = (A(λ) + ε A₀) / (1 + ε)`. -/
lemma iInf_pairValue_le_one_add_mul (𝒳 : Finset (EuclideanSpace ℝ ι)) (h𝒳 : 𝒳.Nontrivial)
    (hspan : Submodule.span ℝ (𝒳 : Set (EuclideanSpace ℝ ι)) = ⊤) {Δ : ℝ} (hΔ : 0 < Δ)
    {w : EuclideanSpace ℝ ι →₀ ℝ} (hw : IsDesign (𝒳 : Set (EuclideanSpace ℝ ι)) w) {ε : ℝ}
    (hε : 0 < ε) :
    ⨅ p : vertexPairs (𝒳 : Set (EuclideanSpace ℝ ι)), pairValue 𝒳 Δ (designMatrix w) p.1.1 p.1.2
      ≤ (1 + ε) * (4 * Δ ^ 2 / adjDesignValue (𝒳 : Set (EuclideanSpace ℝ ι))) := by
  have := nonempty_index_of_nontrivial (𝒳 := (𝒳 : Set (EuclideanSpace ℝ ι))) h𝒳
  have ha := adjDesignValue_pos 𝒳 h𝒳 hspan
  obtain ⟨A₀, hA₀, hA₀pd⟩ := exists_posDef_mem_designSet hspan
  have hA := hw.posSemidef_designMatrix
  -- the positive definite design matrix `A_ε`
  set Aε := (1 + ε)⁻¹ • (designMatrix w + ε • A₀) with hAε_def
  have hAε_mem : Aε ∈ designSet (𝒳 : Set (EuclideanSpace ℝ ι)) := by
    have h : Aε = (1 + ε)⁻¹ • designMatrix w + ((1 + ε)⁻¹ * ε) • A₀ := by
      rw [hAε_def, smul_add, smul_smul]
    rw [h]
    refine convex_designSet hw.designMatrix_mem_designSet hA₀ (by positivity) (by positivity) ?_
    field_simp
  have hAε_pd : Aε.PosDef :=
    (Matrix.PosDef.posSemidef_add hA (hA₀pd.smul hε)).smul (by positivity)
  obtain ⟨wε, hwε, hwεA⟩ := mem_designSet_iff.1 hAε_mem
  have hle : designMatrix w ≤ (1 + ε) • Aε := by
    rw [hAε_def, smul_smul, mul_inv_cancel₀ (by positivity), one_smul, Matrix.le_iff,
      add_sub_cancel_left]
    exact (hA₀pd.smul hε).posSemidef
  -- an adjacent pair maximizing `‖x - x'‖²_{A_ε⁻¹}`
  obtain ⟨x, x', hadj⟩ := 𝒳.finite_toSet.exists_isAdjacent h𝒳
  have : Nonempty (adjacentPairs (𝒳 : Set (EuclideanSpace ℝ ι))) := ⟨⟨(x, x'), hadj⟩⟩
  have : Finite (adjacentPairs (𝒳 : Set (EuclideanSpace ℝ ι))) :=
    ((𝒳.finite_toSet.subset vertices_subset).offDiag.subset
      adjacentPairs_subset_vertexPairs).to_subtype
  obtain ⟨p, hp⟩ := exists_eq_ciSup_of_finite
    (f := fun p : adjacentPairs (𝒳 : Set (EuclideanSpace ℝ ι)) ↦ mahalanobisSq Aε⁻¹ (p.1.1 - p.1.2))
  have hm : adjDesignValue (𝒳 : Set (EuclideanSpace ℝ ι)) ≤ mahalanobisSq Aε⁻¹ (p.1.1 - p.1.2) := by
    have h := ciInf_le (bddBelow_range_adjValue (𝒳 : Set (EuclideanSpace ℝ ι)))
      (⟨wε, hwε, hwεA ▸ hAε_pd⟩ : PosDefDesign (𝒳 : Set (EuclideanSpace ℝ ι)))
    rw [hwεA] at h
    rw [hp]
    exact h
  calc ⨅ q : vertexPairs (𝒳 : Set (EuclideanSpace ℝ ι)),
        pairValue 𝒳 Δ (designMatrix w) q.1.1 q.1.2
      ≤ pairValue 𝒳 Δ (designMatrix w) p.1.1 p.1.2 :=
        ciInf_le (bddBelow_range_pairValue hA)
          (⟨p.1, adjacentPairs_subset_vertexPairs p.2⟩ :
            vertexPairs (𝒳 : Set (EuclideanSpace ℝ ι)))
    _ ≤ pairValue 𝒳 Δ ((1 + ε) • Aε) p.1.1 p.1.2 := pairValue_mono hA hle
    _ = (1 + ε) * (4 * Δ ^ 2 / mahalanobisSq Aε⁻¹ (p.1.1 - p.1.2)) := by
      rw [pairValue_smul (by positivity), pairValue_eq 𝒳 hΔ hAε_pd p.2]
    _ ≤ (1 + ε) * (4 * Δ ^ 2 / adjDesignValue (𝒳 : Set (EuclideanSpace ℝ ι))) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) ha hm)
        (by positivity)

/-- `f(𝒳, Δ) ≤ 4 / H_Adjacent(𝒳, Δ)` for a spanning `𝒳` with two points: the relaxation to
adjacent pairs and the closed form of Lemma 4, through positive definite approximations of the
design matrices. -/
lemma optValue_le (𝒳 : Finset (EuclideanSpace ℝ ι)) (h𝒳 : 𝒳.Nontrivial)
    (hspan : Submodule.span ℝ (𝒳 : Set (EuclideanSpace ℝ ι)) = ⊤) {Δ : ℝ} (hΔ : 0 < Δ) :
    optValue (𝒳 : Set (EuclideanSpace ℝ ι)) Δ ≤ 4 / hAdjacent (𝒳 : Set (EuclideanSpace ℝ ι)) Δ := by
  have ha := adjDesignValue_pos 𝒳 h𝒳 hspan
  rw [hAdjacent, div_div_eq_mul_div]
  set C := 4 * Δ ^ 2 / adjDesignValue (𝒳 : Set (EuclideanSpace ℝ ι))
  have hC : 0 ≤ C := div_nonneg (by positivity) ha.le
  refine Real.iSup_le (fun w ↦ le_of_forall_pos_le_add fun δ hδ ↦ ?_) hC
  have hε : 0 < δ / (C + 1) := by positivity
  refine (iInf_pairValue_le_one_add_mul 𝒳 h𝒳 hspan hΔ w.2 hε).trans ?_
  have h : δ / (C + 1) * C ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith

end MaynardZhang2026Complexity
