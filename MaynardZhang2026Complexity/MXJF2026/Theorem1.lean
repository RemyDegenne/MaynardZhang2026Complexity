/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.MXJF2026.Setting
public import MaynardZhang2026Complexity.MXJF2026.Lemma3

/-!
# Theorem 1: the arm-set-dependent lower bound

For every fixed-budget algorithm there are two parameter sequences with min-gap at least `Δ` under
one of which the error probability is at least `(1/4) exp(-4T / H_Adjacent(𝒳, Δ))`.

The proof is Lemma 3 (`exists_minGapGE_le_max_error_optValue`) and the bound
`f(𝒳, Δ) ≤ 4 / H_Adjacent(𝒳, Δ)` (`optValue_le`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits.Linear Real Set
open scoped RealInnerProductSpace

universe u

namespace MaynardZhang2026Complexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Theorem 1** (arm-set-dependent lower bound, Maynard-Zhang, Xiong, Jamieson, Fazel 2026).
Fix a finite spanning arm set `𝒳 ⊆ ℝ^d` and `Δ > 0`. For every identification algorithm with
budget `T` there are parameter sequences `θ`, `θ'`, both with min-gap at least `Δ`, such that
`max(P_θ(x̂ ≠ x⋆), P_θ'(x̂ ≠ x⋆')) ≥ (1/4) exp(-4T / H_Adjacent(𝒳, Δ))` (with standard Gaussian
noise, for all runs of the algorithm).

The paper leaves implicit that `T ≥ 1` and that `𝒳` has at least two points: for `T = 0` no
parameter sequence has min-gap `Δ > 0`, and for a single arm `H_Adjacent(𝒳, Δ) = 0` (no adjacent
pairs) while every algorithm is always right. -/
theorem exists_minGapGE_le_max_error (𝒳 : Finset (EuclideanSpace ℝ ι))
    (h𝒳 : 𝒳.Nontrivial) (hspan : Submodule.span ℝ (𝒳 : Set (EuclideanSpace ℝ ι)) = ⊤)
    {Δ : ℝ} (hΔ : 0 < Δ) {T : ℕ} (hT : T ≠ 0)
    (A : IdentAlg Unit (𝒳 : Set (EuclideanSpace ℝ ι)) ℝ (𝒳 : Set (EuclideanSpace ℝ ι)))
    (hA : A.IsFixedBudget T) :
    ∃ θ θ' : ℕ → EuclideanSpace ℝ ι, MinGapGE 𝒳 θ T Δ ∧ MinGapGE 𝒳 θ' T Δ ∧
      ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (X : ℕ → Ω → 𝒳) (Y : ℕ → Ω → ℝ) (out : Ω → 𝒳)
        {Ω' : Type u} {_mΩ' : MeasurableSpace Ω'} (P' : Measure Ω') [IsProbabilityMeasure P']
        (X' : ℕ → Ω' → 𝒳) (Y' : ℕ → Ω' → ℝ) (out' : Ω' → 𝒳),
        A.IsRun (nonstationaryLinearEnv 𝒳 θ fun _ ↦ gaussianReal 0 1) (fun _ _ ↦ ()) X Y out P →
        A.IsRun (nonstationaryLinearEnv 𝒳 θ' fun _ ↦ gaussianReal 0 1) (fun _ _ ↦ ())
          X' Y' out' P' →
        1 / 4 * exp (-(4 * T / hAdjacent (𝒳 : Set (EuclideanSpace ℝ ι)) Δ)) ≤
          max (P.real {ω | ¬ IsBestArm 𝒳 θ T (out ω)})
            (P'.real {ω | ¬ IsBestArm 𝒳 θ' T (out' ω)}) := by
  obtain ⟨θ, θ', hθ, hθ', h⟩ := exists_minGapGE_le_max_error_optValue 𝒳 h𝒳 hΔ hT A hA
  refine ⟨θ, θ', hθ, hθ', ?_⟩
  intro Ω _ P _ X Y out Ω' _ P' _ X' Y' out' hrun hrun'
  refine le_trans ?_ (h P X Y out P' X' Y' out' hrun hrun')
  gcongr
  calc (T : ℝ) * optValue (𝒳 : Set (EuclideanSpace ℝ ι)) Δ
      ≤ T * (4 / hAdjacent (𝒳 : Set (EuclideanSpace ℝ ι)) Δ) := by
        gcongr
        exact optValue_le 𝒳 h𝒳 hspan hΔ
    _ = 4 * T / hAdjacent (𝒳 : Set (EuclideanSpace ℝ ι)) Δ := by ring

end MaynardZhang2026Complexity
