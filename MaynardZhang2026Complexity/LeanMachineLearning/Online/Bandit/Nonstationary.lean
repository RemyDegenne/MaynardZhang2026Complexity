/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.LeanMachineLearning.Online.Bandit.BestArm
public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

/-!
# Non-stationary bandits

A non-stationary bandit with arms `𝓐` is a sequence of reward kernels `ν : ℕ → Kernel 𝓐 ℝ`, the
kernel `ν t` giving the law of the reward of each arm at round `t`; it is played through LML's
oblivious environment `Environment.banditSeq ν`.

## Main definitions

* `cumMean ν T a`: the cumulative mean reward `∑_{t < T} E[ν t a]` of arm `a` over `T` rounds.
* `IsBestArm ν T a`: `a` maximizes the cumulative mean reward over `T` rounds.
* `llrProcess ν ν' A Y t`: the log-likelihood ratio
  `∑_{s < t} log (dν_{s, A_s} / dν'_{s, A_s}) (Y_s)` of the rewards of the first `t` rounds under
  `ν` against `ν'`, along the actions `A` and rewards `Y`.

## Main results

* `isBestArm_bestMeanArm`: the best arm of the vector of cumulative means is a best arm;
* `cumMean_const`, `isBestArm_const_iff`, `isBestArm_const_bestArm`: for a stationary bandit, the
  best arms are the arms of maximal mean, among them LML's `bestArm`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ProbabilityTheory

namespace Bandits

variable {𝓐 : Type*} {m𝓐 : MeasurableSpace 𝓐}

/-- The cumulative mean reward of arm `a` over the first `T` rounds of the non-stationary
bandit `ν`. -/
noncomputable def cumMean (ν : ℕ → Kernel 𝓐 ℝ) (T : ℕ) (a : 𝓐) : ℝ :=
  ∑ t ∈ range T, (ν t a)[id]

/-- The cumulative mean of a stationary bandit is `T` times the mean. -/
lemma cumMean_const (ν : Kernel 𝓐 ℝ) (T : ℕ) (a : 𝓐) :
    cumMean (fun _ ↦ ν) T a = T * (ν a)[id] := by
  simp [cumMean]

/-- `a` is a best arm of the non-stationary bandit `ν` over `T` rounds: it maximizes the
cumulative mean reward. -/
def IsBestArm (ν : ℕ → Kernel 𝓐 ℝ) (T : ℕ) (a : 𝓐) : Prop :=
  ∀ b, cumMean ν T b ≤ cumMean ν T a

/-- The best arm of the vector of cumulative means is a best arm. -/
lemma isBestArm_bestMeanArm [Fintype 𝓐] [Nonempty 𝓐] (ν : ℕ → Kernel 𝓐 ℝ) (T : ℕ) :
    IsBestArm ν T (bestMeanArm (cumMean ν T)) :=
  le_bestMeanArm (cumMean ν T)

/-- Over `T ≠ 0` rounds of a stationary bandit, the best arms are the arms of maximal mean. -/
lemma isBestArm_const_iff {ν : Kernel 𝓐 ℝ} {T : ℕ} (hT : T ≠ 0) {a : 𝓐} :
    IsBestArm (fun _ ↦ ν) T a ↔ ∀ b, (ν b)[id] ≤ (ν a)[id] := by
  have hT' : (0 : ℝ) < T := by positivity
  simp only [IsBestArm, cumMean_const]
  exact forall_congr' fun b ↦ mul_le_mul_iff_right₀ hT'

/-- LML's `bestArm ν` is a best arm of the stationary bandit `ν` over any number of rounds. -/
lemma isBestArm_const_bestArm [Fintype 𝓐] [Nonempty 𝓐] (ν : Kernel 𝓐 ℝ) (T : ℕ) :
    IsBestArm (fun _ ↦ ν) T (bestArm ν) := by
  intro b
  simp only [cumMean_const]
  exact mul_le_mul_of_nonneg_left (le_bestArm b) (Nat.cast_nonneg T)

/-- The log-likelihood ratio of the rewards of the first `t` rounds under the bandit `ν` against
the bandit `ν'`, along the actions `A` and rewards `Y`:
`∑_{s < t} log (dν_{s, A_s} / dν'_{s, A_s}) (Y_s)`. -/
noncomputable def llrProcess {Ω : Type*} (ν ν' : ℕ → Kernel 𝓐 ℝ) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) : ℝ :=
  ∑ s ∈ range t, llr (ν s (A s ω)) (ν' s (A s ω)) (Y s ω)

@[simp]
lemma llrProcess_zero {Ω : Type*} (ν ν' : ℕ → Kernel 𝓐 ℝ) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) :
    llrProcess ν ν' A Y 0 = 0 := by
  ext
  simp [llrProcess]

lemma llrProcess_succ {Ω : Type*} (ν ν' : ℕ → Kernel 𝓐 ℝ) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) :
    llrProcess ν ν' A Y (t + 1) ω
      = llrProcess ν ν' A Y t ω + llr (ν t (A t ω)) (ν' t (A t ω)) (Y t ω) := by
  simp [llrProcess, sum_range_succ]

end Bandits
