/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Independence.InfinitePi

/-!
# Independence of the coordinates of an infinite product measure

Under a product `⊗ₙ μ n` of probability measures on `∀ n : ℕ, X n`, the coordinate `n` is
independent of the coordinates `0, …, n - 1` (`indepFun_eval_restrict_infinitePi`).
-/

@[expose] public section

open MeasureTheory Finset

namespace ProbabilityTheory

/-- Under a product of probability measures, the coordinate `n` is independent of the coordinates
`0, …, n - 1`. -/
lemma indepFun_eval_restrict_infinitePi {X : ℕ → Type*} {mX : ∀ n, MeasurableSpace (X n)}
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)] (n : ℕ) :
    IndepFun (fun ω : (∀ k, X k) ↦ ω n) (fun ω (i : Fin n) ↦ ω i) (Measure.infinitePi μ) := by
  have h := (iIndepFun_infinitePi (P := μ) (X := fun _ x ↦ x)
    (fun _ ↦ measurable_id)).indepFun_finset {n} (range n) (by simp)
    (fun _ ↦ measurable_pi_apply _)
  have h1 : Measurable fun (y : ∀ i : ({n} : Finset ℕ), X i) ↦
      (y ⟨n, mem_singleton_self n⟩ : X n) := measurable_pi_apply _
  have h2 : Measurable fun (y : ∀ i : range n, X i) (i : Fin n) ↦
      (y ⟨i, mem_range.2 i.2⟩ : X i) := by fun_prop
  exact h.comp h1 h2

end ProbabilityTheory
