/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace

/-!
# Environments agreeing before a round

If two environments have the same observation and feedback kernels at the rounds before `N`,
the first `N` rounds of an algorithm-environment sequence do not see the difference: the history
of the first `N` rounds has the same law against both environments, and so has the action of
round `N` when the observation kernels also agree at round `N`.

## Main statements

* `IsAlgEnvSeqUntil.of_env_eq`: an algorithm-environment sequence until time `N` for `env` is one
  for every environment with the same kernels before round `N`.
* `IsAlgEnvSeq.identDistrib_history_of_env_eq`: the histories of the first `N` rounds of two
  algorithm-environment sequences of the same algorithm against environments agreeing before
  round `N` have the same law.
* `IsAlgEnvSeq.identDistrib_action_of_env_eq`: so have the actions of round `N`, if the
  observation kernels also agree at round `N`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓞 𝓐 𝓨 Ω Ω' : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {alg : Algorithm 𝓞 𝓐 𝓨} {env env' : Environment 𝓞 𝓐 𝓨} {N : ℕ}
  {P : Measure Ω} {P' : Measure Ω'}
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
  {O' : ℕ → Ω' → 𝓞} {A' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → 𝓨}

/-- An algorithm-environment sequence until time `N` for the environment `env` is one for every
environment `env'` with the same observation and feedback kernels at the rounds before `N`. -/
lemma IsAlgEnvSeqUntil.of_env_eq [IsFiniteMeasure P] (h : IsAlgEnvSeqUntil O A Y alg env P N)
    (hobs : ∀ n < N, env.obs n = env'.obs n)
    (hfeedback : ∀ n < N, env.feedback n = env'.feedback n) :
    IsAlgEnvSeqUntil O A Y alg env' P N where
  measurable_obs := h.measurable_obs
  measurable_action := h.measurable_action
  measurable_feedback := h.measurable_feedback
  hasCondDistrib_obs n hn := hobs n hn ▸ h.hasCondDistrib_obs n hn
  hasCondDistrib_action n hn := h.hasCondDistrib_action n hn
  hasCondDistrib_feedback n hn := hfeedback n hn ▸ h.hasCondDistrib_feedback n hn

/-- **Runs against environments agreeing before round `N`**: the histories of the first `N`
rounds of algorithm-environment sequences of the same algorithm against two environments with the
same observation and feedback kernels at the rounds before `N` have the same law. -/
lemma IsAlgEnvSeq.identDistrib_history_of_env_eq [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] (h : IsAlgEnvSeq O A Y alg env P)
    (h' : IsAlgEnvSeq O' A' Y' alg env' P') (hobs : ∀ n < N, env.obs n = env'.obs n)
    (hfeedback : ∀ n < N, env.feedback n = env'.feedback n) :
    IdentDistrib (history O A Y N) (history O' A' Y' N) P P' where
  aemeasurable_fst := (h.measurable_history N).aemeasurable
  aemeasurable_snd := (h'.measurable_history N).aemeasurable
  map_eq := isAlgEnvSeqUntil_unique ((h.isAlgEnvSeqUntil N).of_env_eq hobs hfeedback)
    (h'.isAlgEnvSeqUntil N)

/-- **Runs against environments agreeing before round `N`**: the actions of round `N` of
algorithm-environment sequences of the same algorithm against two environments with the same
observation kernels at the rounds up to `N` and the same feedback kernels at the rounds before
`N` have the same law. -/
lemma IsAlgEnvSeq.identDistrib_action_of_env_eq [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] (h : IsAlgEnvSeq O A Y alg env P)
    (h' : IsAlgEnvSeq O' A' Y' alg env' P') (hobs : ∀ n ≤ N, env.obs n = env'.obs n)
    (hfeedback : ∀ n < N, env.feedback n = env'.feedback n) :
    IdentDistrib (A N) (A' N) P P' where
  aemeasurable_fst := (h.measurable_action N).aemeasurable
  aemeasurable_snd := (h'.measurable_action N).aemeasurable
  map_eq := by
    have h_hist := (h.identDistrib_history_of_env_eq h' (fun n hn ↦ hobs n hn.le) hfeedback).map_eq
    rw [(h.hasCondDistrib_action N).hasLaw_comp.map_eq,
      (h'.hasCondDistrib_action N).hasLaw_comp.map_eq, (h.hasCondDistrib_obs N).map_eq,
      (h'.hasCondDistrib_obs N).map_eq, h_hist, hobs N le_rfl]

end Learning
