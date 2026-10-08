/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.MXJF2026.Setting
public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace

/-!
# Lemma 6: change of measure at a stopping time for non-stationary bandits

On the trajectory space of an algorithm played against the non-stationary bandits `ν` and `ν'`,
`P_ν'(E) = E_ν[1_E exp(-L_σ)]` for every stopping time `σ` and event `E ∈ 𝓕_σ`, where `L_t` is
the log-likelihood ratio of the observed rewards (Lemma 18 of Kaufmann, Cappé, Garivier 2016,
generalized to non-stationary bandits).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Real
open scoped ENNReal ENat

namespace MaynardZhang2026Complexity

variable {𝓐 : Type*} [Countable 𝓐] [MeasurableSpace 𝓐] [DiscreteMeasurableSpace 𝓐]

/-- **Lemma 6** (Maynard-Zhang, Xiong, Jamieson, Fazel 2026). Let `ν`, `ν'` be non-stationary
bandit models with mutually absolutely continuous reward distributions and `alg` an algorithm;
`P_ν`, `P_ν'` are the laws of the trajectory of `alg` under `ν` and `ν'`. For every stopping time
`σ` of the history filtration (finite everywhere) and every event `E ∈ 𝓕_σ`,
`P_ν'(E) = E_ν[1_E exp(-L_σ)]`. The arms are countable (finitely many in the paper), so that
the log-likelihood ratio is jointly measurable in the arm and the reward. -/
theorem trajMeasure_eq_lintegral_exp_neg_llrProcess (alg : Algorithm Unit 𝓐 ℝ)
    (ν ν' : ℕ → Kernel 𝓐 ℝ) [∀ t, IsMarkovKernel (ν t)] [∀ t, IsMarkovKernel (ν' t)]
    (hac : ∀ t k, ν t k ≪ ν' t k) (hac' : ∀ t k, ν' t k ≪ ν t k)
    {σ : (ℕ → Round Unit 𝓐 ℝ) → ℕ∞} (hσ : IsStoppingTime (IT.filtration Unit 𝓐 ℝ) σ)
    (hfin : ∀ ω, σ ω ≠ ⊤)
    {S : Set (ℕ → Round Unit 𝓐 ℝ)} (hS : MeasurableSet[hσ.measurableSpace] S) :
    trajMeasure alg (Environment.banditSeq ν') S =
      ∫⁻ ω in S,
        ENNReal.ofReal (exp (-Bandits.llrProcess ν ν' IT.action IT.feedback (σ ω).toNat ω))
        ∂(trajMeasure alg (Environment.banditSeq ν)) := by
  sorry

end MaynardZhang2026Complexity
