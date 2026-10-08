/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.Mathlib.Analysis.InnerProductSpace.SupportFn
public import MaynardZhang2026Complexity.LeanMachineLearning.Identification.PAC
public import MaynardZhang2026Complexity.Mathlib.Probability.Kernel.Composition.Prod
public import MaynardZhang2026Complexity.LeanMachineLearning.Online.Bandit.Nonstationary
public import LeanMachineLearning.Online.Bandit.Regret
public import LeanMachineLearning.SequentialLearning.Comap
public import LeanMachineLearning.SequentialLearning.IdentificationAlg
public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Stochastic linear bandits

In a stochastic linear bandit, the actions `a` have features `φ a` in a real inner product space
`E` and there is an unknown reward vector `θ : E`: playing `a` gives the feedback `⟪φ a, θ⟫ + ε`
for a centered noise `ε` (Lattimore–Szepesvári, Chapter 19). The two usual presentations are an
action set `𝒳 ⊆ E` (the actions are the points of `𝒳`, `φ = Subtype.val`) and a finite arm type
with a feature map.

## Main definitions

* `featureKernel φ θ ξ`: the reward kernel `a ↦ law of ⟪φ a, θ⟫ + ε`, `ε ∼ ξ` (i.i.d. noise), and
  `featureEnv φ θ ξ` the corresponding stationary environment;
* `linearKernel 𝒳 θ ξ`, `linearEnv 𝒳 θ ξ`: the case of an action set `𝒳 ⊆ E`;
  `linearGaussianEnv 𝒳 θ` for standard Gaussian noise; `nonstationaryLinearEnv 𝒳 θ ξ`: reward
  vectors `θ t` and noise laws `ξ t` depending on the round;
* `IsSubgaussianLinearEnv φ θ σ2 env`: the environment `env` (any environment, the noise may
  depend on the past) has conditionally `σ2`-sub-Gaussian noise around `⟪φ a, θ⟫`;
* `simpleRegret 𝒳 θ x = sup_{y ∈ 𝒳} ⟪y, θ⟫ - ⟪x, θ⟫` and
  `pseudoRegret 𝒳 θ x n = ∑_{t < n} simpleRegret 𝒳 θ (x t)`;
* `IsLinMaxSelection 𝒳 sel`: `sel θ` maximizes `x ↦ ⟪x, θ⟫` on `𝒳` (a measurable tie-breaking
  rule for the `argmax` of linear bandit algorithms on infinite action sets);
* `IsPAC 𝒳 ξ A ε δ`: `(ε, δ)`-PAC identification in the linear bandit (LML's `IdentAlg.IsPAC`).

## Main results

* `integral_featureKernel_apply`: with integrable centered noise, the mean reward of `a` is
  `⟪φ a, θ⟫`; hence LML's gap and regret of the linear bandit are the simple regret and the
  pseudo-regret (`gap_featureKernel`, `gap_linearKernel`, `regret_linearKernel`), and the
  cumulative means of the non-stationary linear bandit are `⟪x, ∑_t θ t⟫`
  (`cumMean_linearKernel`).
* `isSubgaussianLinearEnv_featureEnv`, `isSubgaussianLinearEnv_linearEnv`: i.i.d.
  `σ2`-sub-Gaussian noise gives a conditionally sub-Gaussian environment;
  `IsSubgaussianLinearEnv.comapAction`: the class is stable under `Environment.comapAction`, so
  that it applies to the environment seen by an algorithm announcing some of its variables.
* `IsLinMaxSelection.inner_eq_supportFn`: a maximizer selection attains the support function.
* `integral_simpleRegret_le_of_measureReal_le`: a recommendation which is `ε`-optimal with
  probability at least `1 - δ` has expected simple regret at most `ε + (Z - ε) δ` when the simple
  regret is bounded by `Z`.
* `IsPAC.one_sub_le_measureReal_of_isRun`, `isPAC_of_forall_isRun`: `A` is `(ε, δ)`-PAC iff, for
  every `θ` and every run of `A` in `linearEnv 𝒳 θ ξ` (on a probability space in the universe of
  `E` for the converse), the recommendation has simple regret at most `ε` with probability at
  least `1 - δ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning

open scoped RealInnerProductSpace NNReal

namespace Bandits.Linear

variable {𝓐 E : Type*} [MeasurableSpace 𝓐] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Reward kernels -/

section Kernel

/-- The reward kernel of the linear bandit with features `φ`, reward vector `θ` and noise law
`ξ`: playing `a` gives the feedback `⟪φ a, θ⟫ + ε` with `ε ∼ ξ`. -/
noncomputable def featureKernel (φ : 𝓐 → E) (θ : E) (ξ : Measure ℝ) : Kernel 𝓐 ℝ :=
  (Kernel.id ×ₖ Kernel.const 𝓐 ξ).map fun p ↦ ⟪φ p.1, θ⟫ + p.2

variable [MeasurableSpace E] [OpensMeasurableSpace E] {φ : 𝓐 → E}

lemma measurable_featureReward (hφ : Measurable φ) (θ : E) :
    Measurable fun p : 𝓐 × ℝ ↦ ⟪φ p.1, θ⟫ + p.2 := by
  fun_prop

lemma isMarkovKernel_featureKernel (hφ : Measurable φ) (θ : E) (ξ : Measure ℝ)
    [IsProbabilityMeasure ξ] : IsMarkovKernel (featureKernel φ θ ξ) :=
  Kernel.IsMarkovKernel.map _ (measurable_featureReward hφ θ)

instance [Countable 𝓐] [MeasurableSingletonClass 𝓐] (φ : 𝓐 → E) (θ : E) (ξ : Measure ℝ)
    [IsProbabilityMeasure ξ] : IsMarkovKernel (featureKernel φ θ ξ) :=
  isMarkovKernel_featureKernel (measurable_of_countable φ) θ ξ

lemma featureKernel_apply (hφ : Measurable φ) (θ : E) (ξ : Measure ℝ) [SFinite ξ] (a : 𝓐) :
    featureKernel φ θ ξ a = ξ.map fun ε ↦ ⟪φ a, θ⟫ + ε :=
  Kernel.map_id_prod_const_apply ξ (measurable_featureReward hφ θ) a

/-- With centered Gaussian noise of variance `v`, playing `a` gives a feedback with law
`N(⟪φ a, θ⟫, v)`. -/
lemma featureKernel_gaussianReal_apply (hφ : Measurable φ) (θ : E) (v : ℝ≥0) (a : 𝓐) :
    featureKernel φ θ (gaussianReal 0 v) a = gaussianReal ⟪φ a, θ⟫ v := by
  rw [featureKernel_apply hφ, gaussianReal_map_const_add, zero_add]

/-- With integrable centered noise, the mean feedback of the action `a` is `⟪φ a, θ⟫`. -/
lemma integral_featureKernel_apply (hφ : Measurable φ) (θ : E) {ξ : Measure ℝ}
    [IsProbabilityMeasure ξ] (hξ : Integrable id ξ) (hξ0 : ξ[id] = 0) (a : 𝓐) :
    (featureKernel φ θ ξ a)[id] = ⟪φ a, θ⟫ := by
  rw [featureKernel_apply hφ, integral_map (by fun_prop) (by fun_prop)]
  have hξ' : Integrable (fun x : ℝ ↦ x) ξ := hξ
  simp only [id_eq]
  rw [integral_add (integrable_const _) hξ', integral_const]
  simpa using hξ0

/-- The reward kernel of the linear bandit on the action set `𝒳 ⊆ E` with reward vector `θ` and
noise law `ξ`: playing `x ∈ 𝒳` gives the feedback `⟪x, θ⟫ + ε` with `ε ∼ ξ`. -/
noncomputable abbrev linearKernel (𝒳 : Set E) (θ : E) (ξ : Measure ℝ) : Kernel 𝒳 ℝ :=
  featureKernel (Subtype.val : 𝒳 → E) θ ξ

instance (𝒳 : Set E) (θ : E) (ξ : Measure ℝ) [IsProbabilityMeasure ξ] :
    IsMarkovKernel (linearKernel 𝒳 θ ξ) :=
  isMarkovKernel_featureKernel measurable_subtype_coe θ ξ

lemma linearKernel_apply (𝒳 : Set E) (θ : E) (ξ : Measure ℝ) [SFinite ξ] (x : 𝒳) :
    linearKernel 𝒳 θ ξ x = ξ.map fun ε ↦ ⟪(x : E), θ⟫ + ε :=
  featureKernel_apply measurable_subtype_coe θ ξ x

/-- With centered Gaussian noise of variance `v`, playing `x` gives a feedback with law
`N(⟪x, θ⟫, v)`. -/
@[simp]
lemma linearKernel_gaussianReal_apply (𝒳 : Set E) (θ : E) (v : ℝ≥0) (x : 𝒳) :
    linearKernel 𝒳 θ (gaussianReal 0 v) x = gaussianReal ⟪(x : E), θ⟫ v :=
  featureKernel_gaussianReal_apply measurable_subtype_coe θ v x

/-- With integrable centered noise, the mean feedback of the action `x ∈ 𝒳` is `⟪x, θ⟫`. -/
lemma integral_linearKernel_apply (𝒳 : Set E) (θ : E) {ξ : Measure ℝ} [IsProbabilityMeasure ξ]
    (hξ : Integrable id ξ) (hξ0 : ξ[id] = 0) (x : 𝒳) :
    (linearKernel 𝒳 θ ξ x)[id] = ⟪(x : E), θ⟫ :=
  integral_featureKernel_apply measurable_subtype_coe θ hξ hξ0 x

end Kernel

/-! ### Environments -/

section Environment

/-- The linear bandit environment with features `φ`, reward vector `θ` and noise law `ξ`: the
stationary environment with reward kernel `featureKernel φ θ ξ`. -/
noncomputable def featureEnv (φ : 𝓐 → E) (θ : E) (ξ : Measure ℝ)
    [IsMarkovKernel (featureKernel φ θ ξ)] : Environment Unit 𝓐 ℝ :=
  Environment.bandit (featureKernel φ θ ξ)

@[simp]
lemma feedback_featureEnv (φ : 𝓐 → E) (θ : E) (ξ : Measure ℝ)
    [IsMarkovKernel (featureKernel φ θ ξ)] (n : ℕ) :
    (featureEnv φ θ ξ).feedback n = (featureKernel φ θ ξ).prodMkLeft _ := rfl

variable [MeasurableSpace E] [OpensMeasurableSpace E]

/-- The linear environment on the action set `𝒳 ⊆ E` with reward vector `θ` and noise law `ξ`:
the stationary environment with reward kernel `linearKernel 𝒳 θ ξ`. -/
noncomputable abbrev linearEnv (𝒳 : Set E) (θ : E) (ξ : Measure ℝ) [IsProbabilityMeasure ξ] :
    Environment Unit 𝒳 ℝ :=
  featureEnv (Subtype.val : 𝒳 → E) θ ξ

/-- The linear Gaussian environment on `𝒳` with reward vector `θ`: playing `x` gives a feedback
with law `N(⟪x, θ⟫, 1)`. -/
noncomputable abbrev linearGaussianEnv (𝒳 : Set E) (θ : E) : Environment Unit 𝒳 ℝ :=
  linearEnv 𝒳 θ (gaussianReal 0 1)

/-- The non-stationary linear environment on `𝒳` with reward vectors `θ t` and noise laws `ξ t`:
the oblivious environment in which the feedback of playing `x` at round `t` is `⟪x, θ t⟫ + ε_t`,
`ε_t ~ ξ t`. -/
noncomputable def nonstationaryLinearEnv (𝒳 : Set E) (θ : ℕ → E) (ξ : ℕ → Measure ℝ)
    [∀ t, IsProbabilityMeasure (ξ t)] : Environment Unit 𝒳 ℝ :=
  Environment.banditSeq fun t ↦ linearKernel 𝒳 (θ t) (ξ t)

@[simp]
lemma feedback_nonstationaryLinearEnv (𝒳 : Set E) (θ : ℕ → E) (ξ : ℕ → Measure ℝ)
    [∀ t, IsProbabilityMeasure (ξ t)] (n : ℕ) :
    (nonstationaryLinearEnv 𝒳 θ ξ).feedback n = (linearKernel 𝒳 (θ n) (ξ n)).prodMkLeft _ := rfl

lemma linearEnv_eq_nonstationaryLinearEnv (𝒳 : Set E) (θ : E) (ξ : Measure ℝ)
    [IsProbabilityMeasure ξ] :
    linearEnv 𝒳 θ ξ = nonstationaryLinearEnv 𝒳 (fun _ ↦ θ) (fun _ ↦ ξ) := rfl

end Environment

/-! ### Conditionally sub-Gaussian noise -/

section SubGaussian

variable {𝓞 𝓑 : Type*} [MeasurableSpace 𝓞] [MeasurableSpace 𝓑]

/-- The environment `env` is a *linear bandit environment with parameter `θ` and conditionally
`σ2`-sub-Gaussian noise*, for the feature map `φ` of the actions: whatever the past rounds `h`, the
current observation `o` and the action `a`, the feedback `y ∼ env.feedback n ((h, o), a)` is such
that `y - ⟪φ a, θ⟫` is `σ2`-sub-Gaussian (in particular its mean is `⟪φ a, θ⟫`). -/
def IsSubgaussianLinearEnv (φ : 𝓐 → E) (θ : E) (σ2 : ℝ≥0) (env : Environment 𝓞 𝓐 ℝ) : Prop :=
  ∀ (n : ℕ) (h : Hist 𝓞 𝓐 ℝ n) (o : 𝓞) (a : 𝓐),
    HasSubgaussianMGF (fun y ↦ y - ⟪φ a, θ⟫) σ2 (env.feedback n ((h, o), a))

/-- The environment seen by an algorithm with actions in `𝓑`, read through `f : 𝓑 → 𝓐` (for
example an algorithm announcing variables alongside its action, `f = Prod.snd`), is again a
linear bandit environment with conditionally sub-Gaussian noise, for the features `φ ∘ f`. -/
lemma IsSubgaussianLinearEnv.comapAction {φ : 𝓐 → E} {θ : E} {σ2 : ℝ≥0}
    {env : Environment 𝓞 𝓐 ℝ} (h : IsSubgaussianLinearEnv φ θ σ2 env) (f : 𝓑 → 𝓐)
    (hf : Measurable f) :
    IsSubgaussianLinearEnv (φ ∘ f) θ σ2 (env.comapAction f hf) := by
  intro n hist o b
  rw [Environment.feedback_comapAction, Kernel.comap_apply]
  exact h n _ o (f b)

variable [MeasurableSpace E] [OpensMeasurableSpace E]

/-- The linear environment `featureEnv φ θ ξ`, whose feedback is `⟪φ a, θ⟫ + ε` with `ε ∼ ξ`
independent of the past, has conditionally `σ2`-sub-Gaussian noise if `ξ` is `σ2`-sub-Gaussian. -/
lemma isSubgaussianLinearEnv_featureEnv {φ : 𝓐 → E} (hφ : Measurable φ) (θ : E)
    (ξ : Measure ℝ) [IsProbabilityMeasure ξ] [IsMarkovKernel (featureKernel φ θ ξ)] {σ2 : ℝ≥0}
    (hξ : HasSubgaussianMGF id σ2 ξ) :
    IsSubgaussianLinearEnv φ θ σ2 (featureEnv φ θ ξ) := by
  intro n h o a
  rw [feedback_featureEnv, Kernel.prodMkLeft_apply, featureKernel_apply hφ,
    ← HasSubgaussianMGF.id_map_iff (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  have hid : ((fun y ↦ y - ⟪φ a, θ⟫) ∘ fun ε ↦ ⟪φ a, θ⟫ + ε) = id := by
    ext ε
    simp
  rwa [hid, Measure.map_id]

/-- The linear environment `linearEnv 𝒳 θ ξ` has conditionally `σ2`-sub-Gaussian noise if `ξ` is
`σ2`-sub-Gaussian. -/
lemma isSubgaussianLinearEnv_linearEnv (𝒳 : Set E) (θ : E) (ξ : Measure ℝ)
    [IsProbabilityMeasure ξ] {σ2 : ℝ≥0} (hξ : HasSubgaussianMGF id σ2 ξ) :
    IsSubgaussianLinearEnv (Subtype.val : 𝒳 → E) θ σ2 (linearEnv 𝒳 θ ξ) :=
  isSubgaussianLinearEnv_featureEnv measurable_subtype_coe θ ξ hξ

end SubGaussian

/-! ### Regret -/

section Regret

/-- The simple regret of the action `x` for the reward vector `θ` on the action set `𝒳`:
`sup_{y ∈ 𝒳} ⟪y, θ⟫ - ⟪x, θ⟫`. -/
noncomputable def simpleRegret (𝒳 : Set E) (θ x : E) : ℝ :=
  (⨆ y : 𝒳, ⟪(y : E), θ⟫) - ⟪x, θ⟫

lemma simpleRegret_eq_supportFn_sub (𝒳 : Set E) (θ x : E) :
    simpleRegret 𝒳 θ x = supportFn 𝒳 θ - ⟪x, θ⟫ := rfl

@[fun_prop]
lemma continuous_simpleRegret (𝒳 : Set E) (θ : E) : Continuous (simpleRegret 𝒳 θ) :=
  continuous_const.sub (continuous_id.inner continuous_const)

@[fun_prop]
lemma measurable_simpleRegret [MeasurableSpace E] [OpensMeasurableSpace E] (𝒳 : Set E) (θ : E) :
    Measurable (simpleRegret 𝒳 θ) :=
  (continuous_simpleRegret 𝒳 θ).measurable

/-- The simple regret of an action of a bounded action set is nonnegative. -/
lemma simpleRegret_nonneg {𝒳 : Set E} {R : ℝ} (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R) (θ : E) {x : E}
    (hx : x ∈ 𝒳) : 0 ≤ simpleRegret 𝒳 θ x :=
  sub_nonneg.2 (inner_le_supportFn hR hx θ)

/-- The pseudo-regret after `n` rounds of the action sequence `x` on the action set `𝒳` with
reward vector `θ`: `∑_{t < n} (sup_{y ∈ 𝒳} ⟪y, θ⟫ - ⟪x_t, θ⟫)`, that is
`max_{x⋆ ∈ 𝒳} ∑_{t < n} ⟪x⋆ - x_t, θ⟫` for a bounded `𝒳`. -/
noncomputable def pseudoRegret (𝒳 : Set E) (θ : E) (x : ℕ → E) (n : ℕ) : ℝ :=
  ∑ t ∈ range n, simpleRegret 𝒳 θ (x t)

@[simp]
lemma pseudoRegret_zero (𝒳 : Set E) (θ : E) (x : ℕ → E) : pseudoRegret 𝒳 θ x 0 = 0 := by
  simp [pseudoRegret]

lemma pseudoRegret_succ (𝒳 : Set E) (θ : E) (x : ℕ → E) (n : ℕ) :
    pseudoRegret 𝒳 θ x (n + 1) = pseudoRegret 𝒳 θ x n + simpleRegret 𝒳 θ (x n) := by
  simp [pseudoRegret, sum_range_succ]

variable [MeasurableSpace E] [OpensMeasurableSpace E] {ξ : Measure ℝ} [IsProbabilityMeasure ξ]

/-- With integrable centered noise, LML's gap of the action `a` in the linear bandit with
features `φ` is the simple regret of its feature on the set of features. -/
lemma gap_featureKernel {φ : 𝓐 → E} (hφ : Measurable φ) (θ : E) (hξ : Integrable id ξ)
    (hξ0 : ξ[id] = 0) (a : 𝓐) :
    gap (featureKernel φ θ ξ) a = simpleRegret (Set.range φ) θ (φ a) := by
  simp only [gap, integral_featureKernel_apply hφ θ hξ hξ0, simpleRegret]
  rw [iSup_range' (fun y : E ↦ ⟪y, θ⟫) φ]

/-- With integrable centered noise, LML's gap of the action `x ∈ 𝒳` in the linear bandit on `𝒳`
is its simple regret. -/
lemma gap_linearKernel (𝒳 : Set E) (θ : E) (hξ : Integrable id ξ) (hξ0 : ξ[id] = 0) (x : 𝒳) :
    gap (linearKernel 𝒳 θ ξ) x = simpleRegret 𝒳 θ x := by
  simp only [gap, integral_linearKernel_apply 𝒳 θ hξ hξ0, simpleRegret]

/-- With integrable centered noise, LML's regret of an action sequence in the linear bandit on
`𝒳` is its pseudo-regret. -/
lemma regret_linearKernel {Ω : Type*} (𝒳 : Set E) (θ : E) (hξ : Integrable id ξ)
    (hξ0 : ξ[id] = 0) (A : ℕ → Ω → 𝒳) (t : ℕ) (ω : Ω) :
    regret (linearKernel 𝒳 θ ξ) A t ω = pseudoRegret 𝒳 θ (fun s ↦ (A s ω : E)) t := by
  simp only [regret_eq_sum_gap, gap_linearKernel 𝒳 θ hξ hξ0, pseudoRegret]

/-- With integrable centered noise, the cumulative mean over `T` rounds of the action `x` in the
non-stationary linear bandit with reward vectors `θ t` is `⟪x, ∑_{t < T} θ t⟫`. -/
lemma cumMean_linearKernel (𝒳 : Set E) (θ : ℕ → E) {ξ : ℕ → Measure ℝ}
    [∀ t, IsProbabilityMeasure (ξ t)] (hξ : ∀ t, Integrable id (ξ t)) (hξ0 : ∀ t, (ξ t)[id] = 0)
    (T : ℕ) (x : 𝒳) :
    cumMean (fun t ↦ linearKernel 𝒳 (θ t) (ξ t)) T x = ⟪(x : E), ∑ t ∈ range T, θ t⟫ := by
  rw [cumMean, inner_sum]
  exact Finset.sum_congr rfl fun t _ ↦ integral_linearKernel_apply 𝒳 (θ t) (hξ t) (hξ0 t) x

end Regret

/-! ### Maximizer selections -/

/-- `sel` selects, for every `θ`, a maximizer `sel θ ∈ 𝒳` of the linear function `x ↦ ⟪x, θ⟫`
on `𝒳`: a tie-breaking rule for `argmax_{x ∈ 𝒳} ⟪x, θ⟫`. -/
def IsLinMaxSelection (𝒳 : Set E) (sel : E → 𝒳) : Prop :=
  ∀ θ : E, ∀ x ∈ 𝒳, ⟪x, θ⟫ ≤ ⟪(sel θ : E), θ⟫

/-- A maximizer selection attains the support function of a bounded set. -/
lemma IsLinMaxSelection.inner_eq_supportFn {𝒳 : Set E} {sel : E → 𝒳} {R : ℝ}
    (h : IsLinMaxSelection 𝒳 sel) (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R) (θ : E) :
    ⟪(sel θ : E), θ⟫ = supportFn 𝒳 θ :=
  le_antisymm (inner_le_supportFn hR (sel θ).2 θ) (supportFn_le ⟨_, (sel θ).2⟩ (h θ))

/-- The action selected by a maximizer selection has simple regret zero on a bounded set. -/
lemma IsLinMaxSelection.simpleRegret_eq_zero {𝒳 : Set E} {sel : E → 𝒳} {R : ℝ}
    (h : IsLinMaxSelection 𝒳 sel) (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R) (θ : E) :
    simpleRegret 𝒳 θ (sel θ) = 0 := by
  rw [simpleRegret_eq_supportFn_sub, h.inner_eq_supportFn hR, sub_self]

/-! ### `(ε, δ)`-PAC identification -/

/-- An identification algorithm (with actions in `𝒳`, real feedbacks and recommendations in
`𝒳`) is `(ε, δ)`-PAC on `𝒳` for the noise law `ξ` if for every reward vector `θ`, run against
the linear environment `linearEnv 𝒳 θ ξ`, its recommendation has simple regret larger than `ε`
with probability at most `δ` (for the law of the output, LML's `IdentAlg.IsPAC`). -/
def IsPAC [MeasurableSpace E] [OpensMeasurableSpace E] (𝒳 : Set E) (ξ : Measure ℝ)
    [IsProbabilityMeasure ξ] (A : IdentAlg Unit 𝒳 ℝ 𝒳) (ε δ : ℝ) : Prop :=
  A.IsPAC (fun θ ↦ linearEnv 𝒳 θ ξ) (fun θ x ↦ ε < simpleRegret 𝒳 θ x) δ

section IsPAC

variable [MeasurableSpace E] [OpensMeasurableSpace E] {𝒳 : Set E} {ξ : Measure ℝ}
  [IsProbabilityMeasure ξ] {A : IdentAlg Unit 𝒳 ℝ 𝒳} {ε δ : ℝ}

/-- For an `(ε, δ)`-PAC algorithm, the recommendation of any run in the linear environment with
reward vector `θ` has simple regret at most `ε` with probability at least `1 - δ`. -/
lemma IsPAC.one_sub_le_measureReal_of_isRun (hpac : IsPAC 𝒳 ξ A ε δ) {θ : E} {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → Unit}
    {X : ℕ → Ω → 𝒳} {Y : ℕ → Ω → ℝ} {out : Ω → 𝒳} (h : A.IsRun (linearEnv 𝒳 θ ξ) O X Y out P) :
    1 - δ ≤ P.real {ω | simpleRegret 𝒳 θ (out ω) ≤ ε} := by
  simpa only [not_lt] using IdentAlg.IsPAC.one_sub_le_measureReal_of_isRun hpac (θ := θ)
    (measurableSet_lt measurable_const (by fun_prop)) h

end IsPAC

/-- **From a PAC guarantee to a bound on the expected simple regret**: if the recommendation
`out` has simple regret at most `ε` with probability at least `1 - δ` and the simple regret on the
instance `θ` is between `0` and `Z ≥ ε` on `𝒳`, then the expected simple regret is at most
`ε + (Z - ε) δ`. -/
lemma integral_simpleRegret_le_of_measureReal_le [MeasurableSpace E] [OpensMeasurableSpace E]
    {𝒳 : Set E} {θ : E} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {out : Ω → 𝒳} (hout : Measurable out) {ε δ Z : ℝ}
    (h0 : ∀ x ∈ 𝒳, 0 ≤ simpleRegret 𝒳 θ x) (hZ : ∀ x ∈ 𝒳, simpleRegret 𝒳 θ x ≤ Z)
    (hεZ : ε ≤ Z) (hpac : 1 - δ ≤ P.real {ω | simpleRegret 𝒳 θ (out ω) ≤ ε}) :
    ∫ ω, simpleRegret 𝒳 θ (out ω) ∂P ≤ ε + (Z - ε) * δ := by
  have hmeas : Measurable fun ω ↦ simpleRegret 𝒳 θ (out ω) := by fun_prop
  set G : Set Ω := {ω | simpleRegret 𝒳 θ (out ω) ≤ ε} with hG
  have hGm : MeasurableSet G := measurableSet_le hmeas measurable_const
  have hint : Integrable (fun ω ↦ simpleRegret 𝒳 θ (out ω)) P :=
    Integrable.of_bound hmeas.aestronglyMeasurable |Z|
      (Filter.Eventually.of_forall fun ω ↦ by
        rw [Real.norm_of_nonneg (h0 _ (out ω).2)]
        exact (hZ _ (out ω).2).trans (le_abs_self Z))
  have hind : Integrable (Gᶜ.indicator fun _ ↦ (Z - ε)) P :=
    (integrable_const (Z - ε)).indicator hGm.compl
  have hbound : (fun ω ↦ simpleRegret 𝒳 θ (out ω)) ≤
      fun ω ↦ ε + Gᶜ.indicator (fun _ ↦ (Z - ε)) ω := by
    intro ω
    change simpleRegret 𝒳 θ (out ω) ≤ ε + Gᶜ.indicator (fun _ ↦ (Z - ε)) ω
    by_cases hω : ω ∈ G
    · rw [Set.indicator_of_notMem (by simpa using hω)]
      have hε : simpleRegret 𝒳 θ (out ω) ≤ ε := hω
      linarith
    · rw [Set.indicator_of_mem hω]
      linarith [hZ _ (out ω).2]
  have hδ : P.real Gᶜ ≤ δ := by
    rw [measureReal_compl hGm, probReal_univ]
    linarith
  calc ∫ ω, simpleRegret 𝒳 θ (out ω) ∂P
      ≤ ∫ ω, ε + Gᶜ.indicator (fun _ ↦ (Z - ε)) ω ∂P :=
        integral_mono hint ((integrable_const ε).add hind) hbound
    _ = ε + P.real Gᶜ * (Z - ε) := by
        rw [integral_add (integrable_const ε) hind, integral_const,
          integral_indicator_const _ hGm.compl]
        simp [measureReal_def]
    _ ≤ ε + (Z - ε) * δ := by
        have : 0 ≤ Z - ε := by linarith
        nlinarith

/-- **`(ε, δ)`-PAC from a bound on every run**: `A` is `(ε, δ)`-PAC on `𝒳` for the noise law `ξ`
as soon as, for every reward vector `θ` and every run of `A` in the linear environment
`linearEnv 𝒳 θ ξ` on a probability space in the universe of `E` (the universe of the canonical run
`IdentAlg.runMeasure`), the recommendation has simple regret at most `ε` with probability at least
`1 - δ`. -/
lemma isPAC_of_forall_isRun.{u} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {𝒳 : Set E} {ξ : Measure ℝ}
    [IsProbabilityMeasure ξ] {A : IdentAlg Unit 𝒳 ℝ 𝒳} {ε δ : ℝ}
    (h : ∀ θ : E, ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (O : ℕ → Ω → Unit) (X : ℕ → Ω → 𝒳) (Y : ℕ → Ω → ℝ) (out : Ω → 𝒳),
      A.IsRun (linearEnv 𝒳 θ ξ) O X Y out P →
        1 - δ ≤ P.real {ω | simpleRegret 𝒳 θ (out ω) ≤ ε}) :
    IsPAC 𝒳 ξ A ε δ := by
  refine IdentAlg.IsPAC.of_forall_isRun (fun θ ↦ measurableSet_lt measurable_const (by fun_prop))
    fun θ Ω _ P _ O X Y out hrun ↦ ?_
  have hmeas : MeasurableSet {x : 𝒳 | simpleRegret 𝒳 θ x ≤ ε} :=
    measurableSet_le (by fun_prop) measurable_const
  have h1 := h θ P O X Y out hrun
  rw [hrun.hasLaw_output.measureReal_eq hmeas] at h1
  rw [hrun.hasLaw_output.measureReal_eq (p := fun x : 𝒳 ↦ ε < simpleRegret 𝒳 θ x)
      (measurableSet_lt measurable_const (by fun_prop)),
    show {x : 𝒳 | ε < simpleRegret 𝒳 θ x} = {x : 𝒳 | simpleRegret 𝒳 θ x ≤ ε}ᶜ by ext; simp,
    measureReal_compl hmeas, probReal_univ]
  linarith

end Bandits.Linear
