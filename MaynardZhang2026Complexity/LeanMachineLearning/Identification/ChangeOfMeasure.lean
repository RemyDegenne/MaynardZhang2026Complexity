/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.LeanMachineLearning.Identification.FixedBudget
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
# Data processing for fixed-budget identification algorithms

The output of an identification algorithm is drawn from the same Markov kernel in all runs,
applied to the history at the stopping time. For a fixed-budget algorithm with budget `T`, that
history is the history of the first `T` rounds, so the divergence between the laws of the outputs
of two runs (in two environments) is at most the divergence between the laws of the histories of
the first `T` rounds.

Copied from `LMLPapers` (`Identification/ChangeOfMeasure.lean`).

## Main statements

* `IdentAlg.IsFixedBudget.klDiv_outputMeasure_le`: for the laws of the outputs.
* `IdentAlg.IsRun.klDiv_map_out_le`: for the outputs of two runs.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory

namespace Learning.IdentAlg

variable {𝓞 𝓐 𝓨 𝓓 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {m𝓓 : MeasurableSpace 𝓓}
  {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'}
  {A : IdentAlg 𝓞 𝓐 𝓨 𝓓} {T : ℕ} {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
  {O' : ℕ → Ω' → 𝓞} {X' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → 𝓨}
  {out : Ω → 𝓓} {out' : Ω' → 𝓓} {env env' : Environment 𝓞 𝓐 𝓨}

/-- **Data processing for fixed-budget algorithms**: the divergence between the laws of the
outputs of a fixed-budget algorithm with budget `T` in two environments is at most the divergence
between the laws of the histories of the first `T` rounds. -/
lemma IsFixedBudget.klDiv_outputMeasure_le (hA : A.IsFixedBudget T)
    (env env' : Environment 𝓞 𝓐 𝓨) :
    klDiv (A.outputMeasure env) (A.outputMeasure env') ≤
      klDiv ((trajMeasure A.alg env).map (IT.hist T))
        ((trajMeasure A.alg env').map (IT.hist T)) := by
  rw [hA.outputMeasure_eq, hA.outputMeasure_eq]
  exact klDiv_comp_right_le _ _ _

/-- **Data processing for runs of a fixed-budget algorithm**: for two runs (in two environments)
of a fixed-budget algorithm with budget `T`, the divergence between the laws of the outputs is
at most the divergence between the laws of the histories of the first `T` rounds. -/
lemma IsRun.klDiv_map_out_le [IsFiniteMeasure P] [IsFiniteMeasure P'] (hA : A.IsFixedBudget T)
    (h : A.IsRun env O X Y out P) (h' : A.IsRun env' O' X' Y' out' P') :
    klDiv (P.map out) (P'.map out') ≤
      klDiv (P.map (history O X Y T)) (P'.map (history O' X' Y' T)) := by
  rw [(h.hasCondDistrib_output_history hA).hasLaw_comp.map_eq,
    (h'.hasCondDistrib_output_history hA).hasLaw_comp.map_eq]
  exact klDiv_comp_right_le _ _ _

end Learning.IdentAlg
