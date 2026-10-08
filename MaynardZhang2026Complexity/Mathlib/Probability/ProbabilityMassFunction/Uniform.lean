/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Distributions.Uniform

/-!
# The uniform law on a finite type

## Main statements

* `PMF.toMeasure_uniformOfFintype_setOf`: the uniform probability of an event is its number of
  elements divided by the number of elements of the space;
* `PMF.map_toMeasure_uniformOfFintype_equiv`: the image of the uniform law by a bijection is the
  uniform law;
* `PMF.toMeasure_uniformOfFintype_prod`: the product of two uniform laws is the uniform law on the
  product.
-/

@[expose] public section

open MeasureTheory Finset

open scoped ENNReal

namespace PMF

variable {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]
  [MeasurableSingletonClass β]

/-- The uniform probability of an event: the number of its elements divided by the number of
elements of the space. -/
lemma toMeasure_uniformOfFintype_setOf (p : α → Prop) [DecidablePred p] :
    (uniformOfFintype α).toMeasure {a | p a} = #(univ.filter p) * (Fintype.card α : ℝ≥0∞)⁻¹ := by
  rw [toMeasure_apply_fintype]
  simp [Set.indicator_apply, sum_ite]

/-- The image of the uniform law by a measurable bijection is the uniform law. -/
lemma map_toMeasure_uniformOfFintype_equiv (e : α ≃ β) (he : Measurable e) :
    (uniformOfFintype α).toMeasure.map e = (uniformOfFintype β).toMeasure := by
  refine Measure.ext_of_singleton fun b ↦ ?_
  rw [Measure.map_apply he (measurableSet_singleton b),
    show e ⁻¹' {b} = {e.symm b} by ext; simp [Equiv.eq_symm_apply],
    toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    toMeasure_apply_singleton _ _ (measurableSet_singleton _), uniformOfFintype_apply,
    uniformOfFintype_apply, Fintype.card_congr e]

/-- The product of two uniform laws is the uniform law on the product. -/
lemma toMeasure_uniformOfFintype_prod :
    (uniformOfFintype α).toMeasure.prod (uniformOfFintype β).toMeasure
      = (uniformOfFintype (α × β)).toMeasure := by
  refine Measure.ext_of_singleton fun p ↦ ?_
  rw [← Set.singleton_prod_singleton, Measure.prod_prod,
    toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    toMeasure_apply_singleton _ _ (measurableSet_singleton _), Set.singleton_prod_singleton,
    toMeasure_apply_singleton _ _ (measurableSet_singleton _), uniformOfFintype_apply,
    uniformOfFintype_apply, uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))]

end PMF
