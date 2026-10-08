/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.MXJF2026.Setting
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Lemma 2: the change-of-measure lower bound for non-stationary bandits

For two non-stationary bandit models `ν`, `ν'` with different best arms over `T` rounds and a
fixed-budget identification algorithm with budget `T`,
`max(P_ν(k̂ ≠ k⋆), P_ν'(k̂ ≠ k⋆'))` is at least
`(1/4) exp(-∑_k ∑_{t < T} P_ν(A_t = k) KL(ν_{t, k}, ν'_{t, k}))`.
This generalizes Lemma 15 of Kaufmann, Cappé, Garivier (2016).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Learning Real
open scoped ENNReal

universe u

namespace MaynardZhang2026Complexity

variable {𝓐 : Type*} [Fintype 𝓐] [MeasurableSpace 𝓐] [DiscreteMeasurableSpace 𝓐]

/-- **Lemma 2** (Maynard-Zhang, Xiong, Jamieson, Fazel 2026). Let `ν`, `ν'` be non-stationary
bandit models (with finite Kullback–Leibler divergences), `k ≠ k'` two arms (in the paper, the
best arms of `ν` and `ν'` over `T` rounds; the proof only uses `k ≠ k'`) and `A` an identification
algorithm with budget `T`. For all runs of `A` under `ν` and under `ν'`,
`max(P_ν(k̂ ≠ k), P_ν'(k̂ ≠ k'))` is at least
`(1/4) exp(-∑_k ∑_{t < T} P_ν(A_t = k) KL(ν_{t, k} ‖ ν'_{t, k}))`. -/
theorem le_max_prob_ne (ν ν' : ℕ → Kernel 𝓐 ℝ) [∀ t, IsMarkovKernel (ν t)]
    [∀ t, IsMarkovKernel (ν' t)] (T : ℕ) (hkl : ∀ t k, klDiv (ν t k) (ν' t k) ≠ ∞)
    {k k' : 𝓐} (hne : k ≠ k')
    (A : IdentAlg Unit 𝓐 ℝ 𝓐) (hA : A.IsFixedBudget T)
    {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (out : Ω → 𝓐)
    {Ω' : Type u} {_mΩ' : MeasurableSpace Ω'} (P' : Measure Ω') [IsProbabilityMeasure P']
    (X' : ℕ → Ω' → 𝓐) (Y' : ℕ → Ω' → ℝ) (out' : Ω' → 𝓐)
    (h : A.IsRun (Environment.banditSeq ν) (fun _ _ ↦ ()) X Y out P)
    (h' : A.IsRun (Environment.banditSeq ν') (fun _ _ ↦ ()) X' Y' out' P') :
    1 / 4 * exp (-(∑ a, ∑ t ∈ Finset.range T,
        P.real {ω | X t ω = a} * (klDiv (ν t a) (ν' t a)).toReal)) ≤
      max (P.real {ω | out ω ≠ k}) (P'.real {ω | out' ω ≠ k'}) := by
  sorry

end MaynardZhang2026Complexity
