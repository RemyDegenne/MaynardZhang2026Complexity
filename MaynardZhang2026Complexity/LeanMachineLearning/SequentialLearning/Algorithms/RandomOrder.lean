/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.Mathlib.Probability.Kernel.Basic
public import MaynardZhang2026Complexity.LeanMachineLearning.SequentialLearning.FactorsThrough
public import Mathlib.Probability.Distributions.Uniform

/-!
# Playing a fixed allocation in uniformly random order

Given an allocation `x : Fin T → 𝓐` of `T` arms (a static design, for instance obtained by rounding
a design distribution), `Algorithm.randomOrder x` is the algorithm playing `x_{π(0)}, …, x_{π(T-1)}`
for a uniformly random permutation `π`. It is written as a sequential algorithm by sampling without
replacement: the next arm is uniform on the multiset of arms of the allocation not yet played
(`remaining x h`). After the `T` rounds, or on histories inconsistent with the allocation, it plays
a uniform arm.

## Main definitions

* `multisetUniform s`: the uniform law on the multiset `s` (uniform on `𝓐` if `s` is empty).
* `remaining x h`: the multiset of the arms of the allocation `x` not yet played in `h`.
* `Algorithm.randomOrder x`: the algorithm playing the allocation `x` in uniformly random order;
  it reads only the past actions (`factorsThrough_randomOrder`).

## See also

The law of the actions of a run: `SequentialLearning/Algorithms/RandomOrderLaw.lean` (the arm of
round `t` is `x (π t)` for a uniformly random permutation `π`, `hasCondDistrib_permArm`) and
`Online/Bandit/Linear/ActionModel.lean` (an explicit model of a run against a non-stationary
linear bandit, with a uniform permutation independent of the noises).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace Learning

variable {𝓞 𝓐 𝓨 : Type*} [MeasurableSpace 𝓞] [MeasurableSpace 𝓐] [MeasurableSpace 𝓨]
  [Fintype 𝓐] [Nonempty 𝓐] [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐]

/-- The uniform law on a multiset (the uniform law on `𝓐` if the multiset is empty). -/
noncomputable def multisetUniform (s : Multiset 𝓐) : Measure 𝓐 :=
  if hs : s = 0 then (PMF.uniformOfFintype 𝓐).toMeasure else (PMF.ofMultiset s hs).toMeasure

instance (s : Multiset 𝓐) : IsProbabilityMeasure (multisetUniform s) := by
  unfold multisetUniform
  split_ifs <;> infer_instance

omit [Nonempty 𝓐] [MeasurableSingletonClass 𝓐] in
/-- The multiset of arms of the allocation `x` not yet played after the arms `h`. -/
def remaining {T n : ℕ} (x : Fin T → 𝓐) (h : Fin n → 𝓐) : Multiset 𝓐 :=
  Multiset.map x univ.val - Multiset.map h univ.val

/-- The algorithm playing the allocation `x` in uniformly random order, as sampling without
replacement: the next arm is uniform on the arms of the allocation not yet played. -/
noncomputable def Algorithm.randomOrder {T : ℕ} (x : Fin T → 𝓐) : Algorithm 𝓞 𝓐 𝓨 where
  policy n := (Kernel.ofFunOfCountable fun h : Fin n → 𝓐 ↦ multisetUniform (remaining x h)).comap
    (fun p ↦ fun i ↦ (p.1 i).action) (by fun_prop)

/-- At round `n`, `Algorithm.randomOrder x` plays a uniform arm among the arms of the allocation
not yet played. -/
@[simp]
lemma Algorithm.policy_randomOrder_apply {T : ℕ} (x : Fin T → 𝓐) (n : ℕ) (p : Hist 𝓞 𝓐 𝓨 n × 𝓞) :
    (Algorithm.randomOrder x).policy n p
      = multisetUniform (remaining x fun i ↦ (p.1 i).action) := rfl

/-- `Algorithm.randomOrder x` reads only the past actions. -/
lemma factorsThrough_randomOrder {T : ℕ} (x : Fin T → 𝓐) :
    (Algorithm.randomOrder (𝓞 := 𝓞) (𝓨 := 𝓨) x).FactorsThrough (𝓑 := fun n ↦ Fin n → 𝓐)
      fun _ p i ↦ (p.1 i).action :=
  fun n ↦ ⟨Kernel.ofFunOfCountable fun h : Fin n → 𝓐 ↦ multisetUniform (remaining x h),
    fun _ ↦ rfl⟩

end Learning
