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

Complements to Mathlib's uniform laws `Measure.uniformOfFinset` and `Measure.ofMultiset`.

## Main statements

* `Measure.isProbabilityMeasure_uniformOfFinset`, `Measure.isProbabilityMeasure_ofMultiset`: the
  uniform law on a nonempty finset or multiset is a probability measure;
* `Measure.uniformOfFinset_univ_setOf`: the uniform probability of an event is its number of
  elements divided by the number of elements of the space;
* `Measure.map_uniformOfFinset_univ_equiv`: the image of the uniform law by a bijection is the
  uniform law;
* `Measure.uniformOfFinset_univ_prod`: the product of two uniform laws is the uniform law on the
  product.
-/

@[expose] public section

open Finset

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]
  [MeasurableSingletonClass β]

/-- The uniform law on a nonempty finset is a probability measure. -/
lemma isProbabilityMeasure_uniformOfFinset {s : Finset α} (hs : s.Nonempty) :
    IsProbabilityMeasure (uniformOfFinset s) := by
  classical
  constructor
  rw [uniformOfFinset_apply]
  simp [ENNReal.div_self (Nat.cast_ne_zero.2 hs.card_pos.ne') (ENNReal.natCast_ne_top _)]

instance [Fintype α] [Nonempty α] : IsProbabilityMeasure (uniformOfFinset (univ : Finset α)) :=
  isProbabilityMeasure_uniformOfFinset univ_nonempty

omit [MeasurableSingletonClass α] in
/-- The uniform law on a nonempty multiset is a probability measure. -/
lemma isProbabilityMeasure_ofMultiset {s : Multiset α} (hs : s ≠ 0) :
    IsProbabilityMeasure (ofMultiset s) := by
  classical
  constructor
  have hc : (Multiset.card s : ℝ≥0∞) ≠ 0 := by simpa using hs
  rw [ofMultiset, sum_apply]
  simp only [smul_apply, measure_univ, smul_eq_mul, mul_one]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum, Multiset.toFinset_sum_count_eq,
    ENNReal.mul_inv_cancel hc (ENNReal.natCast_ne_top _)]

variable [Fintype α] [Fintype β]

/-- The uniform probability of an event: the number of its elements divided by the number of
elements of the space. -/
lemma uniformOfFinset_univ_setOf (p : α → Prop) [DecidablePred p] :
    uniformOfFinset (univ : Finset α) {a | p a}
      = #(univ.filter p) * (Fintype.card α : ℝ≥0∞)⁻¹ := by
  classical
  rw [uniformOfFinset_apply, div_eq_mul_inv, card_univ]
  congr 3
  ext a
  simp

/-- The image of the uniform law by a measurable bijection is the uniform law. -/
lemma map_uniformOfFinset_univ_equiv (e : α ≃ β) (he : Measurable e) :
    (uniformOfFinset (univ : Finset α)).map e = uniformOfFinset (univ : Finset β) := by
  refine ext_of_singleton fun b ↦ ?_
  rw [map_apply he (measurableSet_singleton b),
    show e ⁻¹' {b} = {e.symm b} by ext; simp [Equiv.eq_symm_apply]]
  simp [Fintype.card_congr e]

/-- The product of two uniform laws is the uniform law on the product. -/
lemma uniformOfFinset_univ_prod [Nonempty α] :
    (uniformOfFinset (univ : Finset α)).prod (uniformOfFinset (univ : Finset β))
      = uniformOfFinset (univ : Finset (α × β)) := by
  refine ext_of_singleton fun p ↦ ?_
  rw [← Set.singleton_prod_singleton, prod_prod, Set.singleton_prod_singleton]
  simp only [uniformOfFinset_apply_singleton, mem_univ, ite_true, card_univ, Fintype.card_prod,
    Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))]

end MeasureTheory.Measure
