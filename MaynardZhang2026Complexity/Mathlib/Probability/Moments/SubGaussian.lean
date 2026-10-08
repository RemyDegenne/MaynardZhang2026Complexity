/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Complements on sub-Gaussian random variables

## Main statements

* `HasSubgaussianMGF.mono`: the variance proxy can be increased.
* `HasSubgaussianMGF.add_prod`: if `X` is sub-Gaussian under `μ` and every section `Y a` is
  sub-Gaussian under `ν`, then `(a, b) ↦ X a + Y a b` is sub-Gaussian under `μ.prod ν`, with the
  sum of the variance proxies (the second term is sub-Gaussian conditionally on the first
  coordinate).
* `hasSubgaussianMGF_sum_mul_infinitePi`: a weighted sum `∑_t c_t ε_t` of the coordinates of a
  product of sub-Gaussian laws is sub-Gaussian with variance proxy `∑_t c_t² σ_t`.
-/

@[expose] public section

open MeasureTheory Real

open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : Ω → ℝ} {c c' : ℝ≥0}

/-- The variance proxy of a sub-Gaussian moment generating function can be increased. -/
lemma HasSubgaussianMGF.mono {μ : Measure Ω} (h : HasSubgaussianMGF X c μ) (hc : c ≤ c') :
    HasSubgaussianMGF X c' μ where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := (h.mgf_le t).trans (exp_le_exp.2 (by gcongr))

/-- If `X` is sub-Gaussian under `μ` with variance proxy `cX` and, for every `a`, `Y a` is
sub-Gaussian under `ν` with variance proxy `cY`, then `(a, b) ↦ X a + Y a b` is sub-Gaussian under
`μ.prod ν` with variance proxy `cX + cY`. -/
lemma HasSubgaussianMGF.add_prod {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {X : α → ℝ} {Y : α → β → ℝ}
    {cX cY : ℝ≥0} (hX : HasSubgaussianMGF X cX μ) (hY : ∀ a, HasSubgaussianMGF (Y a) cY ν)
    (hYm : Measurable (Function.uncurry Y)) :
    HasSubgaussianMGF (fun p ↦ X p.1 + Y p.1 p.2) (cX + cY) (μ.prod ν) := by
  have h_meas (t : ℝ) : AEStronglyMeasurable (fun p : α × β ↦ exp (t * (X p.1 + Y p.1 p.2)))
      (μ.prod ν) := by
    have h1 : AEMeasurable (fun p : α × β ↦ X p.1) (μ.prod ν) := hX.aemeasurable.comp_fst
    have h2 : AEMeasurable (fun p : α × β ↦ Y p.1 p.2) (μ.prod ν) := hYm.aemeasurable
    exact (measurable_exp.comp_aemeasurable ((h1.add h2).const_mul t)).aestronglyMeasurable
  have h_eq (t : ℝ) (a : α) : (fun b ↦ exp (t * (X a + Y a b)))
      = fun b ↦ exp (t * X a) * exp (t * Y a b) := by
    ext b
    rw [mul_add, exp_add]
  have h_int (t : ℝ) :
      Integrable (fun p : α × β ↦ exp (t * (X p.1 + Y p.1 p.2))) (μ.prod ν) := by
    rw [integrable_prod_iff (h_meas t)]
    refine ⟨ae_of_all _ fun a ↦ ?_, ?_⟩
    · simp only
      rw [h_eq t a]
      exact ((hY a).integrable_exp_mul t).const_mul _
    · refine Integrable.mono' ((hX.integrable_exp_mul t).mul_const (exp (cY * t ^ 2 / 2)))
        (h_meas t).norm.integral_prod_right' (ae_of_all _ fun a ↦ ?_)
      simp only [norm_eq_abs, abs_of_pos (exp_pos _)]
      rw [abs_of_nonneg (integral_nonneg fun _ ↦ (exp_pos _).le), h_eq t a, integral_const_mul]
      gcongr
      exact (hY a).mgf_le t
  refine ⟨h_int, fun t ↦ ?_⟩
  rw [mgf, integral_prod _ (h_int t)]
  calc ∫ a, ∫ b, exp (t * (X a + Y a b)) ∂ν ∂μ
      ≤ ∫ a, exp (t * X a) * exp (cY * t ^ 2 / 2) ∂μ := by
        refine integral_mono (h_int t).integral_prod_left
          ((hX.integrable_exp_mul t).mul_const _) fun a ↦ ?_
        simp only
        rw [h_eq t a, integral_const_mul]
        gcongr
        exact (hY a).mgf_le t
    _ = mgf X μ t * exp (cY * t ^ 2 / 2) := by rw [integral_mul_const, mgf]
    _ ≤ exp (cX * t ^ 2 / 2) * exp (cY * t ^ 2 / 2) := by
        gcongr
        exact hX.mgf_le t
    _ = exp (↑(cX + cY) * t ^ 2 / 2) := by
        rw [← exp_add, NNReal.coe_add]
        ring_nf

/-- Under a product `⊗ₜ ξ t` of laws with sub-Gaussian moment generating functions of variance
proxies `σ t`, the weighted sum `∑_{t < T} c_t ε_t` of the coordinates is sub-Gaussian with
variance proxy `∑_t c_t² σ_t`. -/
lemma hasSubgaussianMGF_sum_mul_infinitePi {T : ℕ} (c : Fin T → ℝ) {ξ : ℕ → Measure ℝ}
    [∀ t, IsProbabilityMeasure (ξ t)] {σ : ℕ → ℝ≥0} (hξ : ∀ t, HasSubgaussianMGF id (σ t) (ξ t)) :
    HasSubgaussianMGF (fun ε : ℕ → ℝ ↦ ∑ t, c t * ε t) (∑ t : Fin T, c t ^ 2 * σ t).toNNReal
      (Measure.infinitePi ξ) := by
  have hind : iIndepFun (fun (t : Fin T) (ε : ℕ → ℝ) ↦ c t * ε t) (Measure.infinitePi ξ) := by
    have h := (iIndepFun_infinitePi (P := ξ) (X := fun _ x ↦ x) (fun _ ↦ measurable_id)).precomp
      (g := fun t : Fin T ↦ (t : ℕ)) Fin.val_injective
    exact h.comp (fun t u ↦ c t * u) fun t ↦ by fun_prop
  have heval (t : ℕ) : HasSubgaussianMGF (fun ε : ℕ → ℝ ↦ ε t) (σ t) (Measure.infinitePi ξ) := by
    have h := hξ t
    rw [← Measure.infinitePi_map_eval ξ t] at h
    exact HasSubgaussianMGF.of_map (Y := fun ε : ℕ → ℝ ↦ ε t)
      (measurable_pi_apply (X := fun _ : ℕ ↦ ℝ) t).aemeasurable h
  have h := HasSubgaussianMGF.sum_of_iIndepFun hind (s := Finset.univ)
    fun t _ ↦ (heval t).const_mul (c t)
  refine h.mono (le_of_eq ?_)
  rw [← NNReal.coe_inj, Real.coe_toNNReal _ (Finset.sum_nonneg fun _ _ ↦ by positivity),
    NNReal.coe_sum]
  rfl

end ProbabilityTheory
