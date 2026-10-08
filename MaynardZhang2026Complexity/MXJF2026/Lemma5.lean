/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.MXJF2026.Setting
public import MaynardZhang2026Complexity.MXJF2026.Lemma9
public import MaynardZhang2026Complexity.LeanMachineLearning.Online.Bandit.Linear.ActionModel
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Lemma 5: sub-Gaussian error of the least-squares estimator of Adjacent-BAI

In a run of Adjacent-BAI with `1`-sub-Gaussian noise, `zᵀ(θ̂_T - θ̄_T)` is
`3 ‖z‖_{(∑_t x_t x_tᵀ)⁻¹}`-sub-Gaussian for every `z`.

The proof identifies the law of the history of the `T` rounds with that of an explicit model
(`Bandits.Linear.isAlgEnvSeqUntil_randomOrder_prod_infinitePi`): a uniformly random permutation
`π` and independent noises `ε_t ∼ ξ t`, the arm `x_{π(t)}` and the reward
`⟪x_{π(t)}, θ_t⟫ + ε_t` at round `t`. There,
`⟪z, θ̂_T - θ̄_T⟫ = S(π) + ∑_t ⟪z, A⁻¹ x_{π(t)}⟫ ε_t` where `S` is the statistic of Lemma 9 for
the permutation `π⁻¹` (variance proxy `8 ‖z‖²_{A⁻¹}`) and the noise term is, for every `π`,
sub-Gaussian with variance proxy `∑_t ⟪z, A⁻¹ x_t⟫² = ‖z‖²_{A⁻¹}`
(`ProbabilityTheory.HasSubgaussianMGF.add_prod`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits.Linear Matrix Set
open scoped RealInnerProductSpace

universe u

namespace MaynardZhang2026Complexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Lemma 5** (sub-Gaussian error of the least-squares estimator, Maynard-Zhang, Xiong,
Jamieson, Fazel 2026). In a run of Adjacent-BAI with allocation `x_1, …, x_T` (with invertible
`∑_t x_t x_tᵀ`) and centered `1`-sub-Gaussian noise, for every `z ∈ ℝ^d` the error
`zᵀ(θ̂_T - θ̄_T)` of the least-squares estimator is `3 ‖z‖_{(∑_t x_t x_tᵀ)⁻¹}`-sub-Gaussian.

The bounds `‖x_t‖ ≤ 1` and `‖θ_t‖ ≤ 1` are those of Theorem 2, which the paper's proof uses
(through Lemma 9 with `B = M = 1`) but its statement omits; without them the statement is false
(in dimension `1`, with `x = (1, 2)` and `θ = (-10, 10)` the bias term alone has variance `36 z²`,
above `9 z² / 5`). -/
theorem hasSubgaussianMGF_lsEstimator (𝒳 : Finset (EuclideanSpace ℝ ι))
    [Nonempty (𝒳 : Set (EuclideanSpace ℝ ι))] {T : ℕ} (x : Fin T → (𝒳 : Set (EuclideanSpace ℝ ι)))
    (hx : (allocMatrix x).PosDef) (hx₁ : ∀ t, ‖(x t : EuclideanSpace ℝ ι)‖ ≤ 1)
    (θ : ℕ → EuclideanSpace ℝ ι) (hθ : ∀ t < T, ‖θ t‖ ≤ 1) (ξ : ℕ → Measure ℝ)
    [∀ t, IsProbabilityMeasure (ξ t)] (hξ : ∀ t, HasSubgaussianMGF id 1 (ξ t))
    {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → 𝒳) (Y : ℕ → Ω → ℝ) (out : Ω → 𝒳)
    (h : (adjacentBAI x).IsRun (nonstationaryLinearEnv 𝒳 θ ξ) (fun _ _ ↦ ()) X Y out P)
    (z : EuclideanSpace ℝ ι) :
    HasSubgaussianMGF (fun ω ↦ ⟪z, lsEstimator x (history (fun _ _ ↦ ()) X Y T ω) - avgParam θ T⟫)
      (9 * mahalanobisSq (allocMatrix x)⁻¹ z).toNNReal P := by
  let : DecidableEq (𝒳 : Set (EuclideanSpace ℝ ι)) := Classical.decEq _
  -- the law of the history of the `T` rounds is that of the explicit model
  have h1 : IsAlgEnvSeqUntil (fun _ _ ↦ ()) X Y (Algorithm.randomOrder x)
      (nonstationaryLinearEnv 𝒳 θ ξ) P T := h.isAlgEnvSeq.isAlgEnvSeqUntil T
  have h2 := isAlgEnvSeqUntil_randomOrder_prod_infinitePi x θ ξ
  have hlaw := isAlgEnvSeqUntil_unique h1 h2
  set F : Hist Unit (𝒳 : Set (EuclideanSpace ℝ ι)) ℝ T → ℝ :=
    fun h ↦ ⟪z, lsEstimator x h - avgParam θ T⟫ with hF_def
  have hF : Measurable F := by
    simp only [hF_def]
    fun_prop
  change HasSubgaussianMGF (F ∘ history (fun _ _ ↦ ()) X Y T) _ P
  rw [← HasSubgaussianMGF.id_map_iff (hF.comp (h1.measurable_history T)).aemeasurable,
    ← Measure.map_map hF (h1.measurable_history T), hlaw,
    Measure.map_map hF (h2.measurable_history T),
    HasSubgaussianMGF.id_map_iff (hF.comp (h2.measurable_history T)).aemeasurable]
  -- the computation on the explicit model
  set A := allocMatrix x with hA
  set c : EuclideanSpace ℝ ι → ℝ := fun v ↦ ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ v⟫
  set m := mahalanobisSq A⁻¹ z
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hx.isUnit
  have hsq : ∑ t, c (x t) ^ 2 = m :=
    sum_inner_toEuclideanCLM_inv_sum_outerSelf_sq (fun t ↦ (x t : EuclideanSpace ℝ ι)) z
  have hm0 : 0 ≤ m := hsq ▸ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  -- the bias term, a function of the permutation, and the noise term
  let S : Equiv.Perm (Fin T) → ℝ := fun π ↦
    ∑ t, c (x (π t)) * ⟪(x (π t) : EuclideanSpace ℝ ι), θ t⟫ - ⟪z, avgParam θ T⟫
  let η : Equiv.Perm (Fin T) → (ℕ → ℝ) → ℝ := fun π ε ↦ ∑ t : Fin T, c (x (π t)) * ε t
  have h_eq : F ∘ history (fun _ _ ↦ ())
      (fun n (ω : Equiv.Perm (Fin T) × (ℕ → ℝ)) ↦ permArm x n ω.1)
      (fun n ω ↦ ⟪((permArm x n ω.1 : 𝒳) : EuclideanSpace ℝ ι), θ n⟫ + ω.2 n) T
      = fun ω ↦ S ω.1 + η ω.1 ω.2 := by
    funext ω
    obtain ⟨π, ε⟩ := ω
    have hpa (t : Fin T) : permArm x t π = x (π t) := permArm_of_lt x t.2 π
    simp only [Function.comp_apply, hF_def, lsEstimator, history_apply, Round.feedback_mk,
      Round.action_mk, hpa, inner_sub_right, map_sum, map_smul, inner_sum, real_inner_smul_right]
    simp only [S, η, c, hA, add_mul, Finset.sum_add_distrib]
    simp_rw [mul_comm _ (inner ℝ z _)]
    ring
  rw [h_eq]
  -- the bias term: Lemma 9 for the inverse permutation
  have hS : HasSubgaussianMGF S (8 * 1 ^ 2 * 1 ^ 2 * m).toNNReal
      (PMF.uniformOfFintype (Equiv.Perm (Fin T))).toMeasure := by
    have h9 := hasSubgaussianMGF_sum_perm (fun t ↦ (x t : EuclideanSpace ℝ ι))
      (fun t : Fin T ↦ θ t) (span_range_eq_top_of_posDef _ hx) hx₁ (fun t ↦ hθ t t.2) z
    rw [← PMF.map_toMeasure_uniformOfFintype_equiv (Equiv.inv (Equiv.Perm (Fin T)))
      (measurable_of_countable _)] at h9
    refine (h9.of_map (measurable_of_countable _).aemeasurable).congr (ae_of_all _ fun π ↦ ?_)
    have havg : (T : ℝ)⁻¹ • ∑ s : Fin T, θ s = avgParam θ T := by
      rw [avgParam, Fin.sum_univ_eq_sum_range (fun t ↦ θ t) T]
    simp only [Function.comp_apply, Equiv.inv_apply, inner_sub_right, mul_sub,
      Finset.sum_sub_distrib, havg]
    rw [← inner_eq_sum_inner_toEuclideanCLM_inv_mul _ hdet]
    congr 1
    rw [← Equiv.sum_comp π]
    simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    rfl
  -- the noise term: conditionally on the permutation, a weighted sum of independent noises
  have hη (π : Equiv.Perm (Fin T)) :
      HasSubgaussianMGF (η π) m.toNNReal (Measure.infinitePi ξ) := by
    have h' := hasSubgaussianMGF_sum_mul_infinitePi (fun t ↦ c (x (π t))) hξ
    simp only [NNReal.coe_one, mul_one] at h'
    rwa [Equiv.sum_comp π (fun s ↦ c (x s) ^ 2), hsq] at h'
  have hηm : Measurable (Function.uncurry η) :=
    measurable_from_prod_countable_right fun π ↦ by
      change Measurable fun ε : ℕ → ℝ ↦ ∑ t : Fin T, c (x (π t)) * ε t
      exact Finset.measurable_sum _ fun t _ ↦
        (measurable_pi_apply (X := fun _ : ℕ ↦ ℝ) (t : ℕ)).const_mul _
  refine (hS.add_prod hη hηm).mono ?_
  rw [← NNReal.coe_le_coe, NNReal.coe_add, Real.coe_toNNReal _ (by positivity),
    Real.coe_toNNReal _ hm0, Real.coe_toNNReal _ (by positivity)]
  linarith


end MaynardZhang2026Complexity
