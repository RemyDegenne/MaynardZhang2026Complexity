/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.MXJF2026.Setting
public import MaynardZhang2026Complexity.MXJF2026.Lemma5
public import MaynardZhang2026Complexity.Mathlib.Analysis.Convex.Vertices
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Theorem 2: error probability of Adjacent-BAI

With unit-norm arms and parameters, min-gap `Δ > 0` and `1`-sub-Gaussian noise,
Adjacent-BAI run on an allocation satisfying the rounding guarantee errs with probability at most
`|ℐ^{x⋆}| exp(-T / (36 H_Adjacent(𝒳, Δ)))`.

The arm of the min-gap is the best arm `x⋆`, a vertex beating every other arm
(`Set.Finite.mem_vertices_of_forall_vertices`). If the output `x̂` (an argmax of `⟪·, θ̂_T⟫`) is
not `x⋆`, then `⟪x̂ - x⋆, θ̂_T⟫ ≥ 0` and the adjacency lemma
(`Set.Finite.exists_mem_adjacentTo_inner_nonneg`) gives an adjacent vertex `z` with
`⟪z - x⋆, θ̂_T⟫ ≥ 0`, hence `⟪z - x⋆, θ̂_T - θ̄_T⟫ ≥ Δ`. The union bound over `ℐ^{x⋆}`, the
sub-Gaussian tail of Lemma 5 and the rounding guarantee
`T ‖z - x⋆‖²_{A⁻¹} ≤ 2 min_λ max_{ℐ} ‖x - x'‖²_{A(λ)⁻¹}` conclude. When `x⋆` has no adjacent
vertex the error event is empty.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits.Linear Matrix Real Set
open scoped RealInnerProductSpace

universe u

namespace MaynardZhang2026Complexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Theorem 2** (error probability of Adjacent-BAI, Maynard-Zhang, Xiong, Jamieson, Fazel
2026). Let `𝒳 ⊆ ℝ^d` finite with `‖x‖ ≤ 1` for all arms, and `θ_1, …, θ_T` with
`‖θ_t‖ ≤ 1` and min-gap at least `Δ > 0`, with best arm `x⋆`. For an allocation `x_1, …, x_T`
satisfying the rounding guarantee, every run of Adjacent-BAI with centered `1`-sub-Gaussian noise
outputs `x̂ ≠ x⋆` with probability at most `|ℐ^{x⋆}| exp(-T / (36 H_Adjacent(𝒳, Δ)))`.

The paper's assumption `T ≥ d²` is the condition under which the rounding procedure yields an
allocation with the rounding guarantee (`IsAdjacentRounding`); with the guarantee as hypothesis it
is not needed. -/
theorem prob_ne_bestArm_le (𝒳 : Finset (EuclideanSpace ℝ ι))
    [Nonempty (𝒳 : Set (EuclideanSpace ℝ ι))] (hnorm : ∀ x ∈ 𝒳, ‖x‖ ≤ 1) {T : ℕ}
    (x : Fin T → (𝒳 : Set (EuclideanSpace ℝ ι)))
    (hx : IsAdjacentRounding (𝒳 : Set (EuclideanSpace ℝ ι)) x) (θ : ℕ → EuclideanSpace ℝ ι)
    (hθ : ∀ t < T, ‖θ t‖ ≤ 1)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : MinGapGE 𝒳 θ T Δ) {xstar : EuclideanSpace ℝ ι}
    (hstar : IsBestArm 𝒳 θ T xstar) (ξ : ℕ → Measure ℝ) [∀ t, IsProbabilityMeasure (ξ t)]
    (hξ : ∀ t, HasSubgaussianMGF id 1 (ξ t))
    {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → 𝒳) (Y : ℕ → Ω → ℝ) (out : Ω → 𝒳)
    (h : (adjacentBAI x).IsRun (nonstationaryLinearEnv 𝒳 θ ξ) (fun _ _ ↦ ()) X Y out P) :
    P.real {ω | (out ω : EuclideanSpace ℝ ι) ≠ xstar} ≤
      (adjacentTo (𝒳 : Set (EuclideanSpace ℝ ι)) xstar).ncard *
        exp (-(T / (36 * hAdjacent (𝒳 : Set (EuclideanSpace ℝ ι)) Δ))) := by
  have h𝒳 : (𝒳 : Set (EuclideanSpace ℝ ι)).Finite := 𝒳.finite_toSet
  -- the arm of the min-gap is the best arm `xstar`, a vertex
  obtain ⟨x₀, hx₀, hgap₀⟩ := hgap
  obtain ⟨hx₀v, hx₀max⟩ := h𝒳.mem_vertices_of_forall_vertices hΔ hx₀ hgap₀
  have hstar_eq : xstar = x₀ := by
    by_contra hne
    exact absurd (hstar.2 x₀ hx₀) (not_le.2 (hx₀max xstar hstar.1 hne))
  subst hstar_eq
  -- the output is the recommendation computed from the history of the `T` rounds
  have hout : out =ᵐ[P] fun ω ↦ recommend x (history (fun _ _ ↦ ()) X Y T ω) :=
    h.output_ae_eq_of_outputAt_eq_deterministic (IdentAlg.isFixedBudget_fixedBudget _ _ _)
      (measurable_recommend x) (IdentAlg.outputAt_fixedBudget _ _ _)
  -- the adjacent vertices
  have hadjfin : (adjacentTo (𝒳 : Set (EuclideanSpace ℝ ι)) xstar).Finite :=
    h𝒳.subset fun z hz ↦ vertices_subset hz.2.1
  set S := hadjfin.toFinset with hS
  -- an error implies a large deviation of `⟪z - xstar, θ̂ - θ̄⟫` for an adjacent vertex `z`
  have h_sub : {ω | ((recommend x (history (fun _ _ ↦ ()) X Y T ω) : 𝒳) : EuclideanSpace ℝ ι)
        ≠ xstar}
      ⊆ ⋃ z ∈ S, {ω | Δ ≤ ⟪z - xstar,
        lsEstimator x (history (fun _ _ ↦ ()) X Y T ω) - avgParam θ T⟫} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω
    set θhat := lsEstimator x (history (fun _ _ ↦ ()) X Y T ω)
    have hmax : ⟪xstar, θhat⟫ ≤ ⟪((recommend x (history (fun _ _ ↦ ()) X Y T ω) : 𝒳) :
        EuclideanSpace ℝ ι), θhat⟫ :=
      isMaxOn_argmax (fun y : (𝒳 : Set (EuclideanSpace ℝ ι)) ↦
        ⟪(y : EuclideanSpace ℝ ι), θhat⟫) ⟨xstar, hstar.1⟩
    obtain ⟨z, hz, hz0⟩ := h𝒳.exists_mem_adjacentTo_inner_nonneg hx₀v
      (recommend x (history (fun _ _ ↦ ()) X Y T ω)).2 hω (by rw [inner_sub_left]; linarith)
    have hgz := hgap₀ z hz.2.1 hz.2.2.1.symm
    simp only [mem_iUnion, mem_ofPred_eq, exists_prop, hS, Finite.mem_toFinset]
    refine ⟨z, hz, ?_⟩
    rw [inner_sub_left] at hz0 hgz
    rw [inner_sub_right, inner_sub_left, inner_sub_left]
    linarith
  -- the adjacent pairs are finitely many
  have hpairs : (adjacentPairs (𝒳 : Set (EuclideanSpace ℝ ι))).Finite :=
    (h𝒳.prod h𝒳).subset fun p hp ↦ ⟨vertices_subset hp.1, vertices_subset hp.2.1⟩
  -- the tail bound for each adjacent vertex
  have hterm (z : EuclideanSpace ℝ ι) (hz : z ∈ S) :
      P.real {ω | Δ ≤ ⟪z - xstar,
        lsEstimator x (history (fun _ _ ↦ ()) X Y T ω) - avgParam θ T⟫}
        ≤ exp (-(T / (36 * hAdjacent (𝒳 : Set (EuclideanSpace ℝ ι)) Δ))) := by
    have hz' : z ∈ adjacentTo (𝒳 : Set (EuclideanSpace ℝ ι)) xstar := by simpa [hS] using hz
    have hzne : z - xstar ≠ 0 := sub_ne_zero.2 hz'.2.2.1.symm
    -- `T ≠ 0` and the allocation matrix is positive definite
    have hT : (T : ℝ) ≠ 0 := by
      intro hT0
      have := hx.1.mahalanobisSq_pos hzne
      simp [hT0] at this
    have hTpos : (0 : ℝ) < T := lt_of_le_of_ne (Nat.cast_nonneg T) (Ne.symm hT)
    have hA : (allocMatrix x).PosDef := by
      have := hx.1.smul hTpos
      rwa [smul_smul, mul_inv_cancel₀ hT, one_smul] at this
    have hdet : IsUnit (allocMatrix x).det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
    set m := mahalanobisSq (allocMatrix x)⁻¹ (z - xstar) with hm_def
    have hm : 0 < m := hA.inv.mahalanobisSq_pos hzne
    -- the rounding guarantee
    have hround : T * m ≤ 2 * adjDesignValue (𝒳 : Set (EuclideanSpace ℝ ι)) := by
      have hinv : ((T : ℝ)⁻¹ • allocMatrix x)⁻¹ = (T : ℝ) • (allocMatrix x)⁻¹ :=
        Matrix.inv_eq_left_inv (by rw [smul_mul_smul_comm, mul_inv_cancel₀ hT, one_smul,
          nonsing_inv_mul _ hdet])
      have hle : mahalanobisSq ((T : ℝ)⁻¹ • allocMatrix x)⁻¹ (xstar - z)
          ≤ adjValue (𝒳 : Set (EuclideanSpace ℝ ι)) ((T : ℝ)⁻¹ • allocMatrix x) := by
        have := hpairs.to_subtype
        exact le_ciSup (f := fun p : adjacentPairs (𝒳 : Set (EuclideanSpace ℝ ι)) ↦
          mahalanobisSq ((T : ℝ)⁻¹ • allocMatrix x)⁻¹ (p.1.1 - p.1.2))
          (Set.finite_range _).bddAbove ⟨(xstar, z), hz'⟩
      rw [hinv, mahalanobisSq_smul_left, ← neg_sub, mahalanobisSq_neg] at hle
      exact hle.trans hx.2
    have h5 := hasSubgaussianMGF_lsEstimator 𝒳 x hA (fun t ↦ hnorm _ (x t).2) θ hθ ξ hξ P X Y
      out h (z - xstar)
    refine (h5.measure_ge_le hΔ.le).trans (exp_le_exp.2 ?_)
    rw [← hm_def, Real.coe_toNNReal _ (by positivity), hAdjacent, neg_div, neg_le_neg_iff]
    have hadj : 0 < adjDesignValue (𝒳 : Set (EuclideanSpace ℝ ι)) := by nlinarith
    rw [show (T : ℝ) / (36 * (adjDesignValue (𝒳 : Set (EuclideanSpace ℝ ι)) / Δ ^ 2))
        = T * Δ ^ 2 / (36 * adjDesignValue (𝒳 : Set (EuclideanSpace ℝ ι))) by field_simp,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hround (by positivity : (0 : ℝ) ≤ 18 * Δ ^ 2)]
  calc P.real {ω | (out ω : EuclideanSpace ℝ ι) ≠ xstar}
      = P.real {ω | ((recommend x (history (fun _ _ ↦ ()) X Y T ω) : 𝒳) :
          EuclideanSpace ℝ ι) ≠ xstar} := by
        refine measureReal_congr ?_
        filter_upwards [hout] with ω hω
        rw [hω]
    _ ≤ P.real (⋃ z ∈ S, {ω | Δ ≤ ⟪z - xstar,
          lsEstimator x (history (fun _ _ ↦ ()) X Y T ω) - avgParam θ T⟫}) :=
        measureReal_mono h_sub (measure_ne_top _ _)
    _ ≤ ∑ z ∈ S, P.real {ω | Δ ≤ ⟪z - xstar,
          lsEstimator x (history (fun _ _ ↦ ()) X Y T ω) - avgParam θ T⟫} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _z ∈ S, exp (-(T / (36 * hAdjacent (𝒳 : Set (EuclideanSpace ℝ ι)) Δ))) :=
        Finset.sum_le_sum hterm
    _ = (adjacentTo (𝒳 : Set (EuclideanSpace ℝ ι)) xstar).ncard *
          exp (-(T / (36 * hAdjacent (𝒳 : Set (EuclideanSpace ℝ ι)) Δ))) := by
        rw [Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card _ hadjfin]


end MaynardZhang2026Complexity
