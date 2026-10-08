/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg
public import LeanMachineLearning.Online.Bandit.Regret

/-!
# Best arms

LML's `Bandits.bestArm ν` is an arm with the highest mean for a reward kernel `ν` (a choice by
`exists_max_image`), with `gap ν a = μ⋆ - μ_a`. Identification problems are parametrized by the
vector of means `μ : 𝓐 → ℝ` rather than by a kernel, and need the best arm of a vector: this file
defines it and relates the two.

## Main definitions

* `HasUniqueBest μ`: the vector of means `μ` has a unique optimal arm;
* `bestMeanArm μ = argmax μ`: an optimal arm of the vector of means `μ` (for any finite arm type).

## Main results

* `gap_eq_bestMeanArm_sub`, `gap_bestMeanArm`: LML's gap is measured from the best arm of the
  vector of means of the kernel, which has gap `0`;
* `bestArm_eq_bestMeanArm`: with a unique optimal arm, LML's `bestArm ν` is `bestMeanArm` of the
  vector of means of `ν`.

The non-stationary analogue (best arm for the cumulative means over `T` rounds) is
`IsBestArm` in `Nonstationary.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace Bandits

section Vector

variable {α : Type*}

/-- The vector of means `μ` has a unique optimal arm. -/
def HasUniqueBest (μ : α → ℝ) : Prop := ∃ a, ∀ b ≠ a, μ b < μ a

/-- The optimal arm `a*(μ)` of the vector of means `μ` (an arbitrary maximizer if not unique).
LML's `Bandits.bestArm ν` is the analogue for a reward kernel `ν` (`bestArm_eq_bestMeanArm`). -/
noncomputable def bestMeanArm [Fintype α] [Nonempty α] (μ : α → ℝ) : α := argmax μ

variable [Fintype α] [Nonempty α]

lemma le_bestMeanArm (μ : α → ℝ) (a : α) : μ a ≤ μ (bestMeanArm μ) :=
  isMaxOn_argmax μ a

/-- The best arm of a vector of means with a unique optimal arm `a` is `a`. -/
lemma bestMeanArm_eq_of_forall_lt {μ : α → ℝ} {a : α} (h : ∀ b ≠ a, μ b < μ a) :
    bestMeanArm μ = a := by
  by_contra hne
  exact absurd (le_bestMeanArm μ a) (not_le.2 (h _ hne))

lemma HasUniqueBest.forall_lt_bestMeanArm {μ : α → ℝ} (h : HasUniqueBest μ) :
    ∀ b ≠ bestMeanArm μ, μ b < μ (bestMeanArm μ) := by
  obtain ⟨a, ha⟩ := h
  rw [bestMeanArm_eq_of_forall_lt ha]
  exact ha

/-- With a unique optimal arm, every maximizer of the vector of means is `bestMeanArm μ`. -/
lemma HasUniqueBest.eq_bestMeanArm {μ : α → ℝ} (h : HasUniqueBest μ) {a : α}
    (ha : ∀ b, μ b ≤ μ a) : a = bestMeanArm μ := by
  by_contra hne
  exact absurd (ha (bestMeanArm μ)) (not_le.2 (h.forall_lt_bestMeanArm a hne))

end Vector

section Kernel

variable {𝓐 : Type*} [MeasurableSpace 𝓐] [Fintype 𝓐] [Nonempty 𝓐] {ν : Kernel 𝓐 ℝ}

/-- LML's gap of the arm `a` is the difference between the mean of the best arm of the vector
of means and the mean of `a`. -/
lemma gap_eq_bestMeanArm_sub (a : 𝓐) :
    gap ν a = (ν (bestMeanArm fun b ↦ (ν b)[id]))[id] - (ν a)[id] := by
  rw [gap_eq_bestArm_sub]
  congr 1
  exact le_antisymm (le_bestMeanArm (fun b ↦ (ν b)[id]) _) (le_bestArm _)

lemma gap_bestMeanArm : gap ν (bestMeanArm fun a ↦ (ν a)[id]) = 0 := by
  rw [gap_eq_bestMeanArm_sub, sub_self]

/-- With a unique optimal arm, LML's `bestArm ν` is the best arm of the vector of means of
`ν`. -/
lemma bestArm_eq_bestMeanArm (h : HasUniqueBest fun a ↦ (ν a)[id]) :
    bestArm ν = bestMeanArm fun a ↦ (ν a)[id] :=
  h.eq_bestMeanArm le_bestArm

end Kernel

end Bandits
