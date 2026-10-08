/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.Probability.HasCondDistrib
public import LeanMachineLearning.ForMathlib.Probability.Independence.IndepFun
public import LeanMachineLearning.ForMathlib.Probability.Independence.IndepInfinitePi
public import MaynardZhang2026Complexity.LeanMachineLearning.Online.Bandit.Linear.Basic
public import MaynardZhang2026Complexity.LeanMachineLearning.SequentialLearning.Algorithms.RandomOrderLaw
public import MaynardZhang2026Complexity.Mathlib.Probability.HasCondDistrib
public import MaynardZhang2026Complexity.Mathlib.Probability.Independence.InfinitePi

/-!
# Explicit models of runs of action-only algorithms in non-stationary linear bandits

For an algorithm whose policy only reads the past actions (as `Algorithm.randomOrder x`), the
run in the non-stationary linear environment `nonstationaryLinearEnv 𝒳 θ ξ` can be built on an
explicit probability space: draw the "action randomness" `u ∼ μ` and an independent noise
sequence `ε ∼ ⊗ₜ ξ t`, play `a n u` at round `n` and observe `⟪a n u, θ n⟫ + ε n`. Since the law
of the history of a run is unique (LML's `isAlgEnvSeqUntil_unique`), this identifies the law of
the history of every run.

## Main statements

* `Bandits.Linear.isAlgEnvSeqUntil_prod_infinitePi`: the explicit model is an
  algorithm-environment sequence until `N` as soon as `a n` has, under `μ`, the conditional law
  prescribed by the policy given the previous actions;
* `Bandits.Linear.isAlgEnvSeqUntil_randomOrder_prod_infinitePi`: for `Algorithm.randomOrder x`,
  the explicit model with a uniformly random permutation `π` and the actions `x (π n)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Finset
open scoped RealInnerProductSpace

namespace Bandits.Linear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {𝒳 : Set E} {𝓤 : Type*} {m𝓤 : MeasurableSpace 𝓤}

/-- **Explicit model of an algorithm reading only the past actions in a non-stationary linear
environment.** On `𝓤 × (ℕ → ℝ)` with the law `μ ⊗ (⊗ₜ ξ t)`, let the action of round `n` be
`a n u` and its feedback `⟪a n u, θ n⟫ + ε n`. If the policy of `alg` at round `n` is the kernel
`κ n` applied to the past actions, and `a n` has conditional law `κ n` given `a 0, …, a (n - 1)`
under `μ` for `n < N`, then these processes form an algorithm-environment sequence until `N`. -/
lemma isAlgEnvSeqUntil_prod_infinitePi (μ : Measure 𝓤) [IsProbabilityMeasure μ]
    (θ : ℕ → E) (ξ : ℕ → Measure ℝ) [∀ t, IsProbabilityMeasure (ξ t)]
    {a : ℕ → 𝓤 → 𝒳} (ha : ∀ n, Measurable (a n)) {alg : Algorithm Unit 𝒳 ℝ}
    {κ : (n : ℕ) → Kernel (Fin n → 𝒳) 𝒳} [∀ n, IsMarkovKernel (κ n)] {N : ℕ}
    (hpolicy : ∀ n < N, ∀ p, alg.policy n p = κ n (fun i ↦ (p.1 i).action))
    (hκ : ∀ n < N, HasCondDistrib (a n) (fun u (i : Fin n) ↦ a i u) (κ n) μ) :
    IsAlgEnvSeqUntil (fun _ _ ↦ ()) (fun n ω ↦ a n ω.1)
      (fun n ω ↦ ⟪(a n ω.1 : E), θ n⟫ + ω.2 n) alg (nonstationaryLinearEnv 𝒳 θ ξ)
      (μ.prod (Measure.infinitePi ξ)) N where
  measurable_obs n := measurable_const
  measurable_action n := (ha n).comp measurable_fst
  measurable_feedback n := by fun_prop
  hasCondDistrib_obs n hn :=
    hasCondDistrib_unit (measurable_history (fun _ ↦ measurable_const)
      (fun n ↦ (ha n).comp measurable_fst) (fun n ↦ by fun_prop) n).aemeasurable _ _
  hasCondDistrib_action n hn := by
    set P := μ.prod (Measure.infinitePi ξ)
    have hR : Measurable fun (ω : 𝓤 × (ℕ → ℝ)) (i : Fin n) ↦ ω.2 i := by fun_prop
    -- the action given the past actions
    have h1 : HasCondDistrib (fun ω : 𝓤 × (ℕ → ℝ) ↦ a n ω.1)
        (fun ω (i : Fin n) ↦ a i ω.1) (κ n) P :=
      (hκ n hn).comp_hasLaw (g := Prod.fst) (hasLaw_fst_prod μ _)
    -- the past noises are independent of the past and current actions
    have h2 : HasCondDistrib (fun ω : 𝓤 × (ℕ → ℝ) ↦ fun i : Fin n ↦ ω.2 i)
        (fun ω ↦ ((fun i : Fin n ↦ a i ω.1), a n ω.1))
        ((Kernel.const (Fin n → 𝒳) (P.map fun ω (i : Fin n) ↦ ω.2 i)).prodMkRight 𝒳) P := by
      rw [show (Kernel.const (Fin n → 𝒳) (P.map fun ω (i : Fin n) ↦ ω.2 i)).prodMkRight 𝒳
          = Kernel.const _ (P.map fun ω (i : Fin n) ↦ ω.2 i) by ext; simp]
      refine IndepFun.hasCondDistrib_const ?_ (by fun_prop) ⟨hR.aemeasurable, rfl⟩
      exact indepFun_prod (X := fun u ↦ ((fun i : Fin n ↦ a i u), a n u))
        (Y := fun (e : ℕ → ℝ) (i : Fin n) ↦ e i) (by fun_prop) (by fun_prop)
    have h3 := h1.prodMk_right_of_comap_fst h2
    refine h3.map_of_forall_map_eq (G := fun p ↦
      ((fun i : Fin n ↦ (((), p.1 i, ⟪(p.1 i : E), θ i⟫ + p.2 i) : Round Unit 𝒳 ℝ)), ()))
      (by fun_prop) (F := fun _ y ↦ y) measurable_snd _ fun p ↦ ?_
    rw [hpolicy n hn, Kernel.prodMkRight_apply, Measure.map_id']
    rfl
  hasCondDistrib_feedback n hn := by
    set P := μ.prod (Measure.infinitePi ξ)
    -- the current noise is independent of the action randomness and of the past noises
    have h1 : HasCondDistrib (fun ω : 𝓤 × (ℕ → ℝ) ↦ ω.2 n)
        (fun ω ↦ (ω.1, fun i : Fin n ↦ ω.2 i)) (Kernel.const _ (ξ n)) P := by
      refine IndepFun.hasCondDistrib_const ?_ (by fun_prop)
        ((hasLaw_eval_infinitePi ξ n).comp (hasLaw_snd_prod μ _))
      exact ((indepFun_eval_restrict_infinitePi ξ n).snd_prod (μ := μ) (measurable_pi_apply n)
        (by fun_prop)).symm
    refine h1.map_of_forall_map_eq (G := fun p ↦
      (((fun i : Fin n ↦ (((), a i p.1, ⟪(a i p.1 : E), θ i⟫ + p.2 i) : Round Unit 𝒳 ℝ)), ()),
        a n p.1)) (by fun_prop) (F := fun p e ↦ ⟪(a n p.1 : E), θ n⟫ + e) (by fun_prop) _
      fun p ↦ ?_
    rw [feedback_nonstationaryLinearEnv, Kernel.prodMkLeft_apply, linearKernel_apply,
      Kernel.const_apply]

section RandomOrder

variable [Fintype 𝒳] [Nonempty 𝒳] [MeasurableSingletonClass 𝒳] [DecidableEq 𝒳]

/-- **Law of a run of `Algorithm.randomOrder x`** in the non-stationary linear environment: on
`Equiv.Perm (Fin T) × (ℕ → ℝ)` with the law `unif ⊗ (⊗ₜ ξ t)`, playing `x (π n)` at round `n`
and observing `⟪x (π n), θ n⟫ + ε n` is an algorithm-environment sequence until `T`. -/
lemma isAlgEnvSeqUntil_randomOrder_prod_infinitePi {T : ℕ} (x : Fin T → 𝒳) (θ : ℕ → E)
    (ξ : ℕ → Measure ℝ) [∀ t, IsProbabilityMeasure (ξ t)] :
    IsAlgEnvSeqUntil (fun _ _ ↦ ()) (fun n ω ↦ permArm x n ω.1)
      (fun n ω ↦ ⟪((permArm x n ω.1 : 𝒳) : E), θ n⟫ + ω.2 n) (Algorithm.randomOrder x)
      (nonstationaryLinearEnv 𝒳 θ ξ)
      ((PMF.uniformOfFintype (Equiv.Perm (Fin T))).toMeasure.prod (Measure.infinitePi ξ)) T := by
  have : ∀ n, IsMarkovKernel
      (Kernel.ofFunOfCountable fun h : Fin n → 𝒳 ↦ multisetUniform (remaining x h)) :=
    fun n ↦ ⟨fun h ↦ (inferInstance : IsProbabilityMeasure (multisetUniform (remaining x h)))⟩
  exact isAlgEnvSeqUntil_prod_infinitePi _ θ ξ (measurable_permArm x) (fun _ _ _ ↦ rfl)
    fun n hn ↦ hasCondDistrib_permArm hn x

end RandomOrder

end Bandits.Linear
