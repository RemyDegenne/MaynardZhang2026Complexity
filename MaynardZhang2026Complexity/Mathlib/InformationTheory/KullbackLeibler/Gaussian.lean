/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import MaynardZhang2026Complexity.Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The Kullback-Leibler divergence between real Gaussians

We compute the log-likelihood ratio and the Kullback-Leibler divergence between
`gaussianReal m₁ v₁` and `gaussianReal m₂ v₂` for nonzero variances `v₁`, `v₂`. The
Radon-Nikodym derivative is `ProbabilityTheory.rnDeriv_gaussianReal_gaussianReal`.

## Main statements

* `llr_gaussianReal`: the log-likelihood ratio of `gaussianReal m₁ v₁` with respect to
  `gaussianReal m₂ v₂` is almost everywhere equal to
  `y ↦ log (v₂ / v₁) / 2 - (y - m₁) ^ 2 / (2 * v₁) + (y - m₂) ^ 2 / (2 * v₂)`;
  `llr_gaussianReal_same_var`: for a common variance `v`, it is the affine function
  `y ↦ (m₁ - m₂) / v * (y - (m₁ + m₂) / 2)`.
* `klDiv_gaussianReal`: `klDiv (gaussianReal m₁ v₁) (gaussianReal m₂ v₂)
  = ENNReal.ofReal ((log (v₂ / v₁) + v₁ / v₂ + (m₁ - m₂) ^ 2 / v₂ - 1) / 2)`;
  `klDiv_gaussianReal_same_var`: for a common variance `v`, it is
  `ENNReal.ofReal ((m₁ - m₂) ^ 2 / (2 * v))`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal NNReal

namespace InformationTheory

variable {m₁ m₂ : ℝ} {v v₁ v₂ : ℝ≥0}

/-- The log-likelihood ratio of a Gaussian measure with respect to another one, both with nonzero
variances: `log (v₂ / v₁) / 2 - (y - m₁)² / (2 v₁) + (y - m₂)² / (2 v₂)`. -/
lemma llr_gaussianReal (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    llr (gaussianReal m₁ v₁) (gaussianReal m₂ v₂) =ᵐ[gaussianReal m₁ v₁]
      fun y ↦ log (v₂ / v₁) / 2 - (y - m₁) ^ 2 / (2 * v₁) + (y - m₂) ^ 2 / (2 * v₂) := by
  have hv₁' : (v₁ : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv₁
  have hv₂' : (v₂ : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv₂
  filter_upwards [rnDeriv_gaussianReal_gaussianReal (m₁ := m₁) (m₂ := m₂) hv₁ hv₂] with y hy
  rw [llr, hy, ENNReal.toReal_div, toReal_gaussianPDF, toReal_gaussianPDF,
    log_div (gaussianPDFReal_pos _ _ _ hv₁).ne' (gaussianPDFReal_pos _ _ _ hv₂).ne',
    log_gaussianPDFReal _ hv₁, log_gaussianPDFReal _ hv₂, log_div hv₂' hv₁',
    log_mul (by positivity) hv₁', log_mul (by positivity) hv₂']
  ring

/-- The log-likelihood ratio of a Gaussian measure with respect to another one with the same
nonzero variance is an affine function. -/
lemma llr_gaussianReal_same_var (hv : v ≠ 0) :
    llr (gaussianReal m₁ v) (gaussianReal m₂ v)
      =ᵐ[gaussianReal m₁ v] fun y ↦ (m₁ - m₂) / v * (y - (m₁ + m₂) / 2) := by
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  filter_upwards [llr_gaussianReal (m₁ := m₁) (m₂ := m₂) hv hv] with y hy
  rw [hy, div_self hv', log_one]
  field_simp
  ring

/-- The log-likelihood ratio between two Gaussian measures with nonzero variances is
integrable. -/
lemma integrable_llr_gaussianReal (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    Integrable (llr (gaussianReal m₁ v₁) (gaussianReal m₂ v₂)) (gaussianReal m₁ v₁) := by
  refine Integrable.congr ?_ (llr_gaussianReal hv₁ hv₂).symm
  exact ((integrable_const _).sub ((integrable_sub_sq_gaussianReal m₁ m₁ v₁).div_const _)).add
    ((integrable_sub_sq_gaussianReal m₁ m₂ v₁).div_const _)

/-- The Kullback-Leibler divergence between two Gaussian measures with means `m₁`, `m₂` and
nonzero variances `v₁`, `v₂` is `(log (v₂ / v₁) + v₁ / v₂ + (m₁ - m₂)² / v₂ - 1) / 2`. -/
lemma klDiv_gaussianReal (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    klDiv (gaussianReal m₁ v₁) (gaussianReal m₂ v₂)
      = ENNReal.ofReal ((log (v₂ / v₁) + v₁ / v₂ + (m₁ - m₂) ^ 2 / v₂ - 1) / 2) := by
  have hv₁' : (v₁ : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv₁
  have hv₂' : (v₂ : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv₂
  have h₁ : Integrable (fun y ↦ (y - m₁) ^ 2 / (2 * v₁)) (gaussianReal m₁ v₁) :=
    (integrable_sub_sq_gaussianReal m₁ m₁ v₁).div_const _
  have h₂ : Integrable (fun y ↦ (y - m₂) ^ 2 / (2 * v₂)) (gaussianReal m₁ v₁) :=
    (integrable_sub_sq_gaussianReal m₁ m₂ v₁).div_const _
  have h₃ : Integrable (fun y ↦ log (v₂ / v₁) / 2 - (y - m₁) ^ 2 / (2 * v₁)) (gaussianReal m₁ v₁) :=
    (integrable_const _).sub h₁
  rw [klDiv_of_ac_of_integrable (gaussianReal_absolutelyContinuous_gaussianReal hv₁ hv₂)
    (integrable_llr_gaussianReal hv₁ hv₂), integral_congr_ae (llr_gaussianReal hv₁ hv₂),
    integral_add h₃ h₂, integral_sub (integrable_const _) h₁, integral_const, integral_div,
    integral_div, integral_sub_sq_gaussianReal, integral_sub_sq_gaussianReal]
  simp only [probReal_univ, smul_eq_mul, one_mul, sub_self, add_sub_cancel_right]
  congr 1
  field_simp
  ring

/-- The Kullback-Leibler divergence between two Gaussian measures with the same nonzero
variance `v` and means `m₁`, `m₂` is `(m₁ - m₂) ^ 2 / (2 * v)`. -/
lemma klDiv_gaussianReal_same_var (hv : v ≠ 0) :
    klDiv (gaussianReal m₁ v) (gaussianReal m₂ v) = ENNReal.ofReal ((m₁ - m₂) ^ 2 / (2 * v)) := by
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  rw [klDiv_gaussianReal hv hv, div_self hv', log_one]
  congr 1
  field_simp
  ring

/-- The Kullback-Leibler divergence between two Gaussian measures with variance `1` and means
`m₁`, `m₂` is `(m₁ - m₂) ^ 2 / 2`. -/
lemma klDiv_gaussianReal_one :
    klDiv (gaussianReal m₁ 1) (gaussianReal m₂ 1) = ENNReal.ofReal ((m₁ - m₂) ^ 2 / 2) := by
  rw [klDiv_gaussianReal_same_var one_ne_zero]
  simp

end InformationTheory
