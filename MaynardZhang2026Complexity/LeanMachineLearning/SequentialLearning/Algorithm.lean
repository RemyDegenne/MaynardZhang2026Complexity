/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.Algorithm
public import MaynardZhang2026Complexity.Mathlib.Probability.HasCondDistrib

/-!
# Algorithm-environment sequences: law of the history, transport, agreeing algorithms

Complements to LML's `LeanMachineLearning.SequentialLearning.Algorithm`.

The history of the first `n + 1` rounds is the history of the first `n` rounds followed by the
step at round `n` (LML's `history_succ`). At the level of laws, the law of the first `n + 1`
rounds is therefore the composition-product of the law of the first `n` rounds with the step
kernel, read through `MeasurableEquiv.finSuccProd`.

## Main statements

* `IsAlgEnvSeq.map_history_succ`, `IsAlgEnvSeqUntil.map_history_succ`: the law of the first
  `n + 1` rounds is the composition-product of the law of the first `n` rounds with the step
  kernel (`map_history_succ_of_hasCondDistrib` for any measure under which the step at round `n`
  has a given conditional law given the first `n` rounds).
* `IsAlgEnvSeq.comp_hasLaw`, `IsAlgEnvSeqUntil.comp_hasLaw`: algorithm-environment sequences are
  transported along a measurable map `g : Ω → Ω'` carrying `P` to `P'`.
* `IsAlgEnvSeqUntil.of_policy_eq`: an algorithm-environment sequence until time `N` for `alg` is
  one for every algorithm with the same policies before time `N` (LML's
  `IsAlgEnvSeq.isAlgEnvSeqUntil_of_policy_eq` is the version for algorithm-environment
  sequences).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓞 𝓐 𝓨 Ω Ω' : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {alg alg' : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨} {n N : ℕ}

section HistoryLaw

variable {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

/-- If the step at round `n` has conditional law `κ` given the first `n` rounds under a measure
`Q`, then the law of the first `n + 1` rounds under `Q` is the composition-product of the law of
the first `n` rounds with `κ`. -/
lemma map_history_succ_of_hasCondDistrib {Q : Measure Ω}
    {κ : Kernel (Hist 𝓞 𝓐 𝓨 n) (Round 𝓞 𝓐 𝓨)}
    (h : HasCondDistrib (step O X Y n) (history O X Y n) κ Q) :
    Q.map (history O X Y (n + 1)) =
      (Q.map (history O X Y n) ⊗ₘ κ).map (MeasurableEquiv.finSuccProd (Round 𝓞 𝓐 𝓨) n).symm := by
  rw [history_succ, ← h.map_eq, AEMeasurable.map_map_of_aemeasurable
    (MeasurableEquiv.measurable _).aemeasurable h.aemeasurable]

/-- The law of the first `n + 1` rounds of an algorithm-environment sequence is the
composition-product of the law of the first `n` rounds with the step kernel. -/
lemma IsAlgEnvSeq.map_history_succ {P : Measure Ω} [IsFiniteMeasure P]
    (h : IsAlgEnvSeq O X Y alg env P) (n : ℕ) :
    P.map (history O X Y (n + 1)) =
      (P.map (history O X Y n) ⊗ₘ stepKernel alg env n).map
        (MeasurableEquiv.finSuccProd (Round 𝓞 𝓐 𝓨) n).symm :=
  map_history_succ_of_hasCondDistrib (h.hasCondDistrib_step n)

/-- The law of the first `n + 1 ≤ N` rounds of an algorithm-environment sequence until time `N`
is the composition-product of the law of the first `n` rounds with the step kernel. -/
lemma IsAlgEnvSeqUntil.map_history_succ {P : Measure Ω} [IsFiniteMeasure P]
    (h : IsAlgEnvSeqUntil O X Y alg env P N) (hn : n < N) :
    P.map (history O X Y (n + 1)) =
      (P.map (history O X Y n) ⊗ₘ stepKernel alg env n).map
        (MeasurableEquiv.finSuccProd (Round 𝓞 𝓐 𝓨) n).symm :=
  map_history_succ_of_hasCondDistrib (h.hasCondDistrib_step n hn)

end HistoryLaw

section Transport

variable {P : Measure Ω} {P' : Measure Ω'} [IsFiniteMeasure P] [IsFiniteMeasure P'] {g : Ω → Ω'}
  {O : ℕ → Ω' → 𝓞} {X : ℕ → Ω' → 𝓐} {Y : ℕ → Ω' → 𝓨}

/-- An algorithm-environment sequence is transported along a measurable map `g` carrying `P`
to `P'`. -/
lemma IsAlgEnvSeq.comp_hasLaw (h : IsAlgEnvSeq O X Y alg env P') (hg : HasLaw g P' P)
    (hgm : Measurable g) :
    IsAlgEnvSeq (fun n ↦ O n ∘ g) (fun n ↦ X n ∘ g) (fun n ↦ Y n ∘ g) alg env P where
  measurable_obs n := (h.measurable_obs n).comp hgm
  measurable_action n := (h.measurable_action n).comp hgm
  measurable_feedback n := (h.measurable_feedback n).comp hgm
  hasCondDistrib_obs n := (h.hasCondDistrib_obs n).comp_hasLaw hg
  hasCondDistrib_action n := (h.hasCondDistrib_action n).comp_hasLaw hg
  hasCondDistrib_feedback n := (h.hasCondDistrib_feedback n).comp_hasLaw hg

/-- An algorithm-environment sequence until time `N` is transported along a measurable map `g`
carrying `P` to `P'`. -/
lemma IsAlgEnvSeqUntil.comp_hasLaw (h : IsAlgEnvSeqUntil O X Y alg env P' N) (hg : HasLaw g P' P)
    (hgm : Measurable g) :
    IsAlgEnvSeqUntil (fun n ↦ O n ∘ g) (fun n ↦ X n ∘ g) (fun n ↦ Y n ∘ g) alg env P N where
  measurable_obs n := (h.measurable_obs n).comp hgm
  measurable_action n := (h.measurable_action n).comp hgm
  measurable_feedback n := (h.measurable_feedback n).comp hgm
  hasCondDistrib_obs n hn := (h.hasCondDistrib_obs n hn).comp_hasLaw hg
  hasCondDistrib_action n hn := (h.hasCondDistrib_action n hn).comp_hasLaw hg
  hasCondDistrib_feedback n hn := (h.hasCondDistrib_feedback n hn).comp_hasLaw hg

end Transport

/-- If two algorithms have the same policies before time `N`, an algorithm-environment sequence
until time `N` for the first one is an algorithm-environment sequence until time `N` for the
second one. -/
lemma IsAlgEnvSeqUntil.of_policy_eq {P : Measure Ω} [IsFiniteMeasure P] {O : ℕ → Ω → 𝓞}
    {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} (h : IsAlgEnvSeqUntil O X Y alg env P N)
    (h_eq : ∀ n < N, alg.policy n = alg'.policy n) : IsAlgEnvSeqUntil O X Y alg' env P N where
  measurable_obs := h.measurable_obs
  measurable_action := h.measurable_action
  measurable_feedback := h.measurable_feedback
  hasCondDistrib_obs := h.hasCondDistrib_obs
  hasCondDistrib_action n hn := h_eq n hn ▸ h.hasCondDistrib_action n hn
  hasCondDistrib_feedback := h.hasCondDistrib_feedback

end Learning
