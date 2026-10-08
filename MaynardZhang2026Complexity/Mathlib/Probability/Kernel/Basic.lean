/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Basic

/-!
# Markov kernels from functions on countable spaces

## Main statements

* `ProbabilityTheory.Kernel.isMarkovKernel_ofFunOfCountable`: `Kernel.ofFunOfCountable f` is a
  Markov kernel when every `f a` is a probability measure.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

instance isMarkovKernel_ofFunOfCountable {α β : Type*} [MeasurableSpace α]
    {_ : MeasurableSpace β} [Countable α] [MeasurableSingletonClass α] {f : α → Measure β}
    [∀ a, IsProbabilityMeasure (f a)] : IsMarkovKernel (Kernel.ofFunOfCountable f) :=
  ⟨fun a ↦ inferInstanceAs (IsProbabilityMeasure (f a))⟩

end ProbabilityTheory.Kernel
