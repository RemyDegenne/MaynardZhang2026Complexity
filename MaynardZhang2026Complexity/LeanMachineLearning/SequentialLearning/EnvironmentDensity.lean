/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.Probability.WithDensity
public import MaynardZhang2026Complexity.LeanMachineLearning.SequentialLearning.Algorithm

/-!
# Change of environment: the density of the law of the history

Let an algorithm interact with two environments `env` and `env'` with the same observation
kernels, the feedback kernels of `env'` having densities with respect to those of `env` which only
depend on the round (observation, action, feedback) and on its index:
`env'.feedback n = (env.feedback n).withDensity (fun p y ↦ ρ n (p.1.2, p.2, y))`. Then the law of
the history of the first `n` rounds against `env'` has density `h ↦ ∏_{s < n} ρ s (h s)` with
respect to that against `env`. This is the analogue for environments of LML's
`IsAlgEnvSeq.hasLaw_history_withDensity` (change of algorithm in a fixed environment).

## Main statements

* `stepKernel_eq_withDensity_of_feedback_eq`: the step kernels then have densities `ρ n`.
* `IsAlgEnvSeq.hasLaw_history_withDensity_of_feedback_eq`: the law of the history.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace Learning

variable {𝓞 𝓐 𝓨 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {alg : Algorithm 𝓞 𝓐 𝓨} {env env' : Environment 𝓞 𝓐 𝓨}
  {ρ : ℕ → Round 𝓞 𝓐 𝓨 → ℝ≥0∞}

/-- If two environments have the same observation kernel at round `n` and the feedback kernel of
`env'` at round `n` has density `(p, y) ↦ ρ n (p.1.2, p.2, y)` with respect to that of `env`, then
the step kernel of round `n` against `env'` has density `ρ n` with respect to that against
`env`. -/
lemma stepKernel_eq_withDensity_of_feedback_eq (n : ℕ) (hρ : Measurable (ρ n))
    (hobs : env'.obs n = env.obs n)
    (hfeedback : env'.feedback n =
      (env.feedback n).withDensity fun p y ↦ ρ n (p.1.2, p.2, y)) :
    stepKernel alg env' n = (stepKernel alg env n).withDensity fun _ r ↦ ρ n r := by
  have hg : Measurable (Function.uncurry fun (p : (Hist 𝓞 𝓐 𝓨 n × 𝓞) × 𝓐) (y : 𝓨) ↦
      ρ n (p.1.2, p.2, y)) := by
    change Measurable fun q : ((Hist 𝓞 𝓐 𝓨 n × 𝓞) × 𝓐) × 𝓨 ↦ ρ n (q.1.1.2, q.1.2, q.2)
    fun_prop
  have h_sf : IsSFiniteKernel
      ((env.feedback n).withDensity fun p y ↦ ρ n (p.1.2, p.2, y)) := by
    rw [← hfeedback]
    infer_instance
  have h_inner : alg.policy n ⊗ₖ env'.feedback n = (alg.policy n ⊗ₖ env.feedback n).withDensity
      (fun p ay ↦ ρ n (p.2, ay.1, ay.2)) := by
    rw [hfeedback, Kernel.compProd_withDensity hg]
  have h_sf' : IsSFiniteKernel ((alg.policy n ⊗ₖ env.feedback n).withDensity
      (fun p ay ↦ ρ n (p.2, ay.1, ay.2))) := by
    rw [← h_inner]
    infer_instance
  change env'.obs n ⊗ₖ (alg.policy n ⊗ₖ env'.feedback n) =
    (env.obs n ⊗ₖ (alg.policy n ⊗ₖ env.feedback n)).withDensity fun _ r ↦ ρ n r
  rw [hobs, h_inner, Kernel.compProd_withDensity (by fun_prop)]

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
  {O' : ℕ → Ω' → 𝓞} {A' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → 𝓨}

/-- **Change of environment**: if two environments have the same observation kernels and the
feedback kernels of `env'` have densities `(p, y) ↦ ρ n (p.1.2, p.2, y)` with respect to those of
`env`, then the law of the history of the first `n` rounds of an algorithm against `env'` has
density `h ↦ ∏_{s < n} ρ s (h s)` with respect to that against `env`. -/
lemma IsAlgEnvSeq.hasLaw_history_withDensity_of_feedback_eq (h : IsAlgEnvSeq O A Y alg env P)
    (h' : IsAlgEnvSeq O' A' Y' alg env' P') (hρ : ∀ n, Measurable (ρ n))
    (hobs : ∀ n, env'.obs n = env.obs n)
    (hfeedback : ∀ n, env'.feedback n =
      (env.feedback n).withDensity fun p y ↦ ρ n (p.1.2, p.2, y)) (n : ℕ) :
    HasLaw (history O' A' Y' n)
      ((P.map (history O A Y n)).withDensity fun hn ↦ ∏ s : Fin n, ρ s (hn s)) P' where
  aemeasurable := (h'.measurable_history n).aemeasurable
  map_eq := by
    induction n with
    | zero =>
      rw [(hasLaw_history_zero O A Y).map_eq, (hasLaw_history_zero O' A' Y').map_eq]
      simp
    | succ n ih =>
      have hs := stepKernel_eq_withDensity_of_feedback_eq (alg := alg) n (hρ n) (hobs n)
        (hfeedback n)
      have : IsMarkovKernel ((stepKernel alg env n).withDensity fun _ r ↦ ρ n r) := by
        rw [← hs]
        infer_instance
      have hD : Measurable fun hn : Hist 𝓞 𝓐 𝓨 n ↦ ∏ s : Fin n, ρ s (hn s) :=
        Finset.measurable_prod _ fun s _ ↦ (hρ s).comp (measurable_pi_apply s)
      rw [h'.map_history_succ, h.map_history_succ, ih, hs,
        Measure.withDensity_compProd_withDensity hD (by fun_prop),
        map_equiv_withDensity (by fun_prop)]
      congr 1
      funext hn
      simp only [Function.comp_apply, MeasurableEquiv.symm_symm,
        MeasurableEquiv.finSuccProd_apply]
      rw [Fin.prod_univ_castSucc]
      rfl

end Learning
