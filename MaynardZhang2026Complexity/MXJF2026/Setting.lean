/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.LeanMachineLearning.Identification.FixedBudget
public import MaynardZhang2026Complexity.LeanMachineLearning.Online.Bandit.Linear.Basic
public import MaynardZhang2026Complexity.LeanMachineLearning.Design
public import MaynardZhang2026Complexity.Mathlib.Analysis.InnerProductSpace.Mahalanobis
public import MaynardZhang2026Complexity.Mathlib.Analysis.Convex.Adjacent
public import MaynardZhang2026Complexity.LeanMachineLearning.SequentialLearning.Algorithms.RandomOrder
public import MaynardZhang2026Complexity.LeanMachineLearning.Online.Bandit.Nonstationary
public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Setting of Maynard-Zhang, Xiong, Jamieson, Fazel (2026)

Fixed-budget best-arm identification in non-stationary linear bandits.

A finite arm set `𝒳 ⊆ ℝ^d` spanning the space, a horizon `T` and a parameter sequence
`θ_1, …, θ_T`; at round `t` the learner plays `x_t ∈ 𝒳` and observes `⟪x_t, θ_t⟫ + ε_t` with
independent centered `1`-sub-Gaussian noise (`nonstationaryLinearEnv 𝒳 θ ξ`; standard Gaussian
noise `ξ t = N(0, 1)` in the lower bounds). The learner must identify the hindsight best
arm `x⋆ = argmax_{x ∈ 𝒳} ⟪x, θ̄_T⟫`, `θ̄_T = (1/T) ∑_t θ_t` (`avgParam`, `IsBestArm`).

* `MinGapGE 𝒳 θ T Δ`: the *min-gap* `min_{x ∈ 𝒱 ∖ {x⋆}} ⟪x⋆ - x, θ̄_T⟫` over the vertices
  `𝒱` of `conv 𝒳` is at least `Δ` (`minGap` is the min-gap itself); `FeasibleSeqs` is
  Definition 2.
* The complexity `H_Adjacent(𝒳, Δ)`, equal to
  `min_{λ ∈ Δ_𝒳} max_{(x, x') ∈ ℐ} ‖x - x'‖²_{A(λ)⁻¹} / Δ²` (`hAdjacent`), where `ℐ` is the
  set of adjacent pairs of vertices and `A(λ) = ∑ λ_x x xᵀ` is the design matrix; the minimum
  is over designs with positive definite design matrix
  (`PosDefDesign`).
* The optimization problem of Lemma 3: `PairFeasible 𝒳 Δ x x' θ v` are its constraints,
  `pairValue 𝒳 Δ A x x'` the value `min vᵀ A v` of the inner problem, `optValue 𝒳 Δ` is
  `f(𝒳, Δ)`.
* Algorithm 1 (`Adjacent-BAI`): given an allocation `x_1, …, x_T` (obtained in the paper by
  rounding the adjacent-optimal design; `IsAdjacentRounding` is the guarantee of the rounding
  procedure), play it in uniformly random order (`Algorithm.randomOrder`), compute the least-squares
  estimator `θ̂_T = (∑_t x_t x_tᵀ)⁻¹ ∑_t x_{π(t)} r_t` (`lsEstimator`) and output
  `argmax_{x ∈ 𝒳} ⟪x, θ̂_T⟫` (`recommend`). `adjacentBAI 𝒳 x` is the fixed-budget identification
  algorithm.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits.Linear Matrix Set
open scoped RealInnerProductSpace

namespace MaynardZhang2026Complexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The average parameter `θ̄_T = (1/T) ∑_{t < T} θ_t`. -/
noncomputable def avgParam (θ : ℕ → EuclideanSpace ℝ ι) (T : ℕ) : EuclideanSpace ℝ ι :=
  (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, θ t

/-- `x` is a hindsight best arm: `x ∈ 𝒳` maximizes `⟪·, θ̄_T⟫` over `𝒳`. -/
def IsBestArm (𝒳 : Set (EuclideanSpace ℝ ι)) (θ : ℕ → EuclideanSpace ℝ ι) (T : ℕ)
    (x : EuclideanSpace ℝ ι) : Prop :=
  x ∈ 𝒳 ∧ ∀ y ∈ 𝒳, ⟪y, avgParam θ T⟫ ≤ ⟪x, avgParam θ T⟫

/-- The min-gap `Δ_(1) = min_{x ∈ 𝒱 ∖ {x⋆}} ⟪x⋆ - x, θ̄_T⟫` of the best arm `x⋆`, over the
vertices `𝒱` of `conv 𝒳`. -/
noncomputable def minGap (𝒳 : Set (EuclideanSpace ℝ ι)) (θ : ℕ → EuclideanSpace ℝ ι) (T : ℕ)
    (xstar : EuclideanSpace ℝ ι) : ℝ :=
  ⨅ x : {x // x ∈ vertices 𝒳 ∧ x ≠ xstar}, ⟪xstar - x, avgParam θ T⟫

/-- The parameter sequence `θ` has min-gap at least `Δ` over `T` rounds: some arm `x⋆ ∈ 𝒳`
beats every other vertex of `conv 𝒳` by at least `Δ` for `θ̄_T` (for `Δ > 0`, `x⋆` is then the
unique best arm). -/
def MinGapGE (𝒳 : Set (EuclideanSpace ℝ ι)) (θ : ℕ → EuclideanSpace ℝ ι) (T : ℕ) (Δ : ℝ) :
    Prop :=
  ∃ x ∈ 𝒳, ∀ y ∈ vertices 𝒳, y ≠ x → Δ ≤ ⟪x - y, avgParam θ T⟫

/-- **Definition 2**: two parameter sequences are *feasible* for `(𝒳, Δ)` if they have different
best arms and each has min-gap at least `Δ`. -/
def FeasibleSeqs (𝒳 : Set (EuclideanSpace ℝ ι)) (T : ℕ) (Δ : ℝ) (θ θ' : ℕ → EuclideanSpace ℝ ι) :
    Prop :=
  (∃ x x', IsBestArm 𝒳 θ T x ∧ IsBestArm 𝒳 θ' T x' ∧ x ≠ x') ∧
    MinGapGE 𝒳 θ T Δ ∧ MinGapGE 𝒳 θ' T Δ

/-! ### The adjacency complexity -/

/-- The design distributions on `𝒳` with positive definite design matrix. -/
def PosDefDesign (𝒳 : Set (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι →₀ ℝ) :=
  {w | IsDesign 𝒳 w ∧ (designMatrix w).PosDef}

/-- `max_{(x, x') ∈ ℐ} ‖x - x'‖²_{A⁻¹}` over the adjacent pairs of vertices of `conv 𝒳`. -/
noncomputable def adjValue (𝒳 : Set (EuclideanSpace ℝ ι)) (A : Matrix ι ι ℝ) : ℝ :=
  ⨆ p : adjacentPairs 𝒳, mahalanobisSq A⁻¹ (p.1.1 - p.1.2)

/-- `min_{λ ∈ Δ_𝒳} max_{(x, x') ∈ ℐ} ‖x - x'‖²_{A(λ)⁻¹}`, the value of the adjacent-optimal
design. -/
noncomputable def adjDesignValue (𝒳 : Set (EuclideanSpace ℝ ι)) : ℝ :=
  ⨅ w : PosDefDesign 𝒳, adjValue 𝒳 (designMatrix (w : EuclideanSpace ℝ ι →₀ ℝ))

/-- The complexity `H_Adjacent(𝒳, Δ) = min_λ max_{(x, x') ∈ ℐ} ‖x - x'‖²_{A(λ)⁻¹} / Δ²`. -/
noncomputable def hAdjacent (𝒳 : Set (EuclideanSpace ℝ ι)) (Δ : ℝ) : ℝ :=
  adjDesignValue 𝒳 / Δ ^ 2

/-! ### The optimization problem of Lemma 3 -/

/-- The constraints of the inner optimization problem for the pair `(x, x')`: `x` beats every
other vertex by `Δ` for `θ`, and `x'` beats every other vertex by `Δ` for `θ + v`. -/
def PairFeasible (𝒳 : Set (EuclideanSpace ℝ ι)) (Δ : ℝ) (x x' θ v : EuclideanSpace ℝ ι) : Prop :=
  (∀ y ∈ vertices 𝒳, y ≠ x → Δ ≤ ⟪x - y, θ⟫) ∧ (∀ y ∈ vertices 𝒳, y ≠ x' → Δ ≤ ⟪x' - y, θ + v⟫)

/-- The value `min_{θ, v} vᵀ A v` of the inner optimization problem for the pair `(x, x')`,
subject to `PairFeasible 𝒳 Δ x x' θ v`. -/
noncomputable def pairValue (𝒳 : Set (EuclideanSpace ℝ ι)) (Δ : ℝ) (A : Matrix ι ι ℝ)
    (x x' : EuclideanSpace ℝ ι) : ℝ :=
  ⨅ q : {q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι // PairFeasible 𝒳 Δ x x' q.1 q.2},
    mahalanobisSq A q.1.2

/-- `f(𝒳, Δ) = max_{λ ∈ Δ_𝒳} min_{(x, x') ∈ 𝒴} min_{θ, v} vᵀ A(λ) v`, the optimization problem
of Lemma 3, over designs `λ` and pairs of distinct vertices. -/
noncomputable def optValue (𝒳 : Set (EuclideanSpace ℝ ι)) (Δ : ℝ) : ℝ :=
  ⨆ w : {w // IsDesign 𝒳 w}, ⨅ p : vertexPairs 𝒳,
    pairValue 𝒳 Δ (designMatrix (w : EuclideanSpace ℝ ι →₀ ℝ)) p.1.1 p.1.2

/-! ### Algorithm 1: Adjacent-BAI -/

section Algorithm

variable {𝒳 : Set (EuclideanSpace ℝ ι)} {T : ℕ}

/-- The matrix `A = ∑_t x_t x_tᵀ` of an allocation. -/
noncomputable def allocMatrix (x : Fin T → 𝒳) : Matrix ι ι ℝ :=
  ∑ t, outerSelf (x t : EuclideanSpace ℝ ι)

/-- The allocation `x_1, …, x_T` satisfies the guarantee of the rounding procedure applied to the
adjacent-optimal design: its normalized matrix is positive definite and
`max_{(x, x') ∈ ℐ} ‖x - x'‖²_{((1/T) ∑_t x_t x_tᵀ)⁻¹}` is at most
`2 min_λ max_{(x, x') ∈ ℐ} ‖x - x'‖²_{A(λ)⁻¹}`. -/
def IsAdjacentRounding (𝒳 : Set (EuclideanSpace ℝ ι)) (x : Fin T → 𝒳) : Prop :=
  ((T : ℝ)⁻¹ • allocMatrix x).PosDef ∧
    adjValue 𝒳 ((T : ℝ)⁻¹ • allocMatrix x) ≤ 2 * adjDesignValue 𝒳

/-- The least-squares estimator of Step 9 of Algorithm 1,
`θ̂_T = (∑_t x_t x_tᵀ)⁻¹ ∑_t x_{π(t)} r_t`, from the history of the `T` rounds (arms played and
rewards). -/
noncomputable def lsEstimator (x : Fin T → 𝒳) (h : Hist Unit 𝒳 ℝ T) : EuclideanSpace ℝ ι :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (allocMatrix x)⁻¹
    (∑ t, (h t).feedback • ((h t).action : EuclideanSpace ℝ ι))

@[fun_prop]
lemma measurable_lsEstimator (x : Fin T → 𝒳) : Measurable (lsEstimator x) := by
  unfold lsEstimator
  fun_prop

/-- The output rule of Algorithm 1: the arm `argmax_{x ∈ 𝒳} ⟪x, θ̂_T⟫`. -/
noncomputable def recommend [Fintype 𝒳] [Nonempty 𝒳] (x : Fin T → 𝒳) (h : Hist Unit 𝒳 ℝ T) : 𝒳 :=
  argmax fun y : 𝒳 ↦ ⟪(y : EuclideanSpace ℝ ι), lsEstimator x h⟫

lemma measurable_recommend [Fintype 𝒳] [Nonempty 𝒳] (x : Fin T → 𝒳) :
    Measurable (recommend x) := by
  unfold recommend
  fun_prop

/-- **Algorithm 1** (`Adjacent-BAI`) for the allocation `x_1, …, x_T`: play the allocation in
uniformly random order, then output `argmax_{x ∈ 𝒳} ⟪x, θ̂_T⟫` for the least-squares estimator
`θ̂_T`. -/
noncomputable def adjacentBAI [Fintype 𝒳] [Nonempty 𝒳] (x : Fin T → 𝒳) : IdentAlg Unit 𝒳 ℝ 𝒳 :=
  haveI : DecidableEq 𝒳 := Classical.decEq _
  IdentAlg.fixedBudget (Algorithm.randomOrder x) T
    (Kernel.deterministic (recommend x) (measurable_recommend x))

end Algorithm

end MaynardZhang2026Complexity
