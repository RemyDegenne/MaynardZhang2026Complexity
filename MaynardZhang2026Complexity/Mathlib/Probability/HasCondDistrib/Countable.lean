/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.HasCondDistrib
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Conditional laws on countable spaces

On countable spaces with measurable singletons, `HasCondDistrib Z C κ μ` holds as soon as
`μ (C = a, Z = b) = μ (C = a) κ a {b}` for all `a` and `b` (`hasCondDistrib_of_countable`).
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- On countable spaces with measurable singletons, a conditional law is determined by the
probabilities of the singletons: if `μ (C = a, Z = b) = μ (C = a) κ a {b}` for all `a`, `b`, then
`κ` is the conditional law of `Z` given `C`. -/
lemma hasCondDistrib_of_countable {Ω α β : Type*} {mΩ : MeasurableSpace Ω}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [Countable α] [Countable β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] {μ : Measure Ω} [SFinite μ]
    {C : Ω → α} {Z : Ω → β} {κ : Kernel α β} [IsSFiniteKernel κ] (hC : Measurable C)
    (hZ : Measurable Z) (h : ∀ a b, μ (C ⁻¹' {a} ∩ Z ⁻¹' {b}) = μ (C ⁻¹' {a}) * κ a {b}) :
    HasCondDistrib Z C κ μ := by
  refine ⟨(hC.prodMk hZ).aemeasurable, Measure.ext_of_singleton fun ⟨a, b⟩ ↦ ?_⟩
  rw [← Set.singleton_prod_singleton, Measure.map_apply (hC.prodMk hZ)
    ((measurableSet_singleton a).prod (measurableSet_singleton b)), Set.mk_preimage_prod,
    Measure.compProd_apply_prod (measurableSet_singleton a) (measurableSet_singleton b),
    lintegral_singleton, Measure.map_apply hC (measurableSet_singleton a), h, mul_comm]

end ProbabilityTheory
