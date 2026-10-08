/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Complements on real Gaussian distributions

## Main statements

* `gaussianReal_absolutelyContinuous_gaussianReal`, `rnDeriv_gaussianReal_gaussianReal`: two
  Gaussian measures with nonzero variances are equivalent and the Radon-Nikodym derivative is the
  ratio of the densities.
* `log_gaussianPDFReal`: `log φ(y) = -log (2π v) / 2 - (y - μ)² / (2 v)` for the density `φ` of
  `N(μ, v)`, `v ≠ 0`.
* `integrable_sub_sq_gaussianReal`, `integral_sub_sq_gaussianReal`: `E[(X - c)²] = v + (μ - c)²`
  for `X ~ N(μ, v)`.

Copied from `LMLPapers` (`ForMathlib/Probability/Distributions/Gaussian/Real.lean`).
-/

@[expose] public section

open MeasureTheory Real Set
open scoped ENNReal NNReal

namespace ProbabilityTheory

section DensityRatio

variable {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0}

/-- Two Gaussian measures with nonzero variances are mutually absolutely continuous. -/
lemma gaussianReal_absolutelyContinuous_gaussianReal (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    gaussianReal m₁ v₁ ≪ gaussianReal m₂ v₂ :=
  (gaussianReal_absolutelyContinuous m₁ hv₁).trans (gaussianReal_absolutelyContinuous' m₂ hv₂)

/-- The Radon-Nikodym derivative of a Gaussian measure with respect to another one, both with
nonzero variances, is the ratio of the densities. -/
lemma rnDeriv_gaussianReal_gaussianReal (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    ∂(gaussianReal m₁ v₁)/∂(gaussianReal m₂ v₂)
      =ᵐ[gaussianReal m₁ v₁] fun y ↦ gaussianPDF m₁ v₁ y / gaussianPDF m₂ v₂ y := by
  refine (gaussianReal_absolutelyContinuous m₁ hv₁).ae_eq ?_
  have h := Measure.rnDeriv_withDensity_right (gaussianReal m₁ v₁) volume
    (measurable_gaussianPDF m₂ v₂).aemeasurable
    (ae_of_all _ fun x ↦ (gaussianPDF_pos _ hv₂ x).ne') (ae_of_all _ fun _ ↦ gaussianPDF_ne_top)
  rw [← gaussianReal_of_var_ne_zero m₂ hv₂] at h
  filter_upwards [h, rnDeriv_gaussianReal m₁ v₁] with y hy₁ hy₂
  rw [hy₁, hy₂, ENNReal.div_eq_inv_mul]

end DensityRatio

/-- The logarithm of the density of `N(μ, v)`, `v ≠ 0`:
`log φ(y) = -log (2π v) / 2 - (y - μ)² / (2 v)`. -/
lemma log_gaussianPDFReal (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (y : ℝ) :
    log (gaussianPDFReal μ v y) = -log (2 * π * v) / 2 - (y - μ) ^ 2 / (2 * v) := by
  have hv' : 0 < (v : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  rw [gaussianPDFReal, log_mul (inv_ne_zero (sqrt_ne_zero'.2 (by positivity))) (exp_pos _).ne',
    log_exp, log_inv, log_sqrt (by positivity)]
  ring

section SecondMoment

/-- `x ↦ (x - c)²` is integrable under a real Gaussian measure. -/
lemma integrable_sub_sq_gaussianReal (μ c : ℝ) (v : ℝ≥0) :
    Integrable (fun y ↦ (y - c) ^ 2) (gaussianReal μ v) :=
  ((memLp_id_gaussianReal' 2 (by simp)).sub (memLp_const c)).integrable_sq

/-- The second moment of `N(μ, v)` about a point `c`: `E[(X - c)²] = v + (μ - c)²`. -/
lemma integral_sub_sq_gaussianReal (μ c : ℝ) (v : ℝ≥0) :
    ∫ y, (y - c) ^ 2 ∂gaussianReal μ v = v + (μ - c) ^ 2 := by
  have h_id : Integrable (fun y ↦ y) (gaussianReal μ v) :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal' 1 ENNReal.one_ne_top)
  have h_var : ∫ y, (y - μ) ^ 2 ∂gaussianReal μ v = v := by
    have h := variance_fun_id_gaussianReal (μ := μ) (v := v)
    rwa [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at h
  calc ∫ y, (y - c) ^ 2 ∂gaussianReal μ v
      = ∫ y, ((y - μ) ^ 2 + (2 * (μ - c) * y + ((μ - c) ^ 2 - 2 * (μ - c) * μ)))
          ∂gaussianReal μ v := by
        congr 1
        ext y
        ring
    _ = v + (μ - c) ^ 2 := by
        have h_lin : Integrable (fun y ↦ 2 * (μ - c) * y + ((μ - c) ^ 2 - 2 * (μ - c) * μ))
            (gaussianReal μ v) := (h_id.const_mul _).add (integrable_const _)
        rw [integral_add (integrable_sub_sq_gaussianReal μ μ v) h_lin, h_var,
          integral_add (h_id.const_mul _) (integrable_const _), integral_const_mul,
          integral_id_gaussianReal, integral_const]
        simp only [probReal_univ, smul_eq_mul, one_mul]
        ring

end SecondMoment

end ProbabilityTheory
