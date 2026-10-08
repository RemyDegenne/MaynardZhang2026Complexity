/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.LeanMachineLearning.Online.Bandit.Nonstationary
public import MaynardZhang2026Complexity.LeanMachineLearning.SequentialLearning.EnvironmentDensity
public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace

/-!
# Change of measure for non-stationary bandits

Let `ν`, `ν'` be non-stationary bandits with countably many arms whose reward laws `ν t a` and
`ν' t a` are mutually absolutely continuous, and let `P_ν`, `P_ν'` be the laws of the trajectory of
an algorithm against them (on the trajectory space of the Ionescu-Tulcea construction). The
log-likelihood ratio of the rewards of the first `n` rounds is
`L_n = ∑_{s < n} log (dν_{s, A_s} / dν'_{s, A_s}) (Y_s)` (`llrProcess`).

The history filtration `IT.filtration` is indexed so that its `n`-th σ-algebra `𝓕_n` is generated
by the rounds `0, …, n`, that is by the `n + 1` first rounds. Hence the change of measure for an
event `E ∈ 𝓕_n` involves `L_{n + 1}`: `P_ν'(E) = E_ν[1_E exp(-L_{n + 1})]`, and for a stopping
time `σ` of this filtration, finite everywhere, and `E ∈ 𝓕_σ`,
`P_ν'(E) = E_ν[1_E exp(-L_{σ + 1})]` (Lemma 18 of Kaufmann, Cappé, Garivier 2016, whose rounds
are numbered from `1`).

## Main statements

* `Bandits.feedback_banditSeq_eq_withDensity`: the feedback kernels of `ν'` have density
  `exp(-llr)` with respect to those of `ν`.
* `Bandits.trajMeasure_banditSeq_apply_eq_setLIntegral`: the change of measure for events of
  `𝓕_n`.
* `Bandits.trajMeasure_banditSeq_apply_eq_setLIntegral_of_isStoppingTime`: the change of measure
  at a stopping time.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Real Finset
open scoped ENNReal

namespace Bandits

variable {𝓐 : Type*} [Countable 𝓐] [MeasurableSpace 𝓐] [DiscreteMeasurableSpace 𝓐]
  {ν ν' : ℕ → Kernel 𝓐 ℝ} [∀ t, IsMarkovKernel (ν t)] [∀ t, IsMarkovKernel (ν' t)]

/-- The density `(a, y) ↦ exp(-llr(ν t a, ν' t a)(y))` is jointly measurable (countably many
arms). -/
lemma measurable_ofReal_exp_neg_llr (ν ν' : ℕ → Kernel 𝓐 ℝ) (t : ℕ) :
    Measurable fun p : 𝓐 × ℝ ↦ ENNReal.ofReal (exp (-llr (ν t p.1) (ν' t p.1) p.2)) := by
  refine measurable_from_prod_countable_right fun a ↦ ?_
  change Measurable fun y ↦ ENNReal.ofReal (exp (-llr (ν t a) (ν' t a) y))
  exact (measurable_llr _ _).neg.exp.ennreal_ofReal

/-- For mutually absolutely continuous reward laws, the feedback kernel of the non-stationary
bandit `ν'` at round `t` has density `exp(-llr(ν t a, ν' t a))` with respect to that of `ν`. -/
lemma feedback_banditSeq_eq_withDensity (hac : ∀ t a, ν t a ≪ ν' t a)
    (hac' : ∀ t a, ν' t a ≪ ν t a) (t : ℕ) :
    (Environment.banditSeq ν').feedback t = ((Environment.banditSeq ν).feedback t).withDensity
      fun p y ↦ ENNReal.ofReal (exp (-llr (ν t p.2) (ν' t p.2) y)) := by
  have hm : Measurable (Function.uncurry fun (p : (Hist Unit 𝓐 ℝ t × Unit) × 𝓐) (y : ℝ) ↦
      ENNReal.ofReal (exp (-llr (ν t p.2) (ν' t p.2) y))) := by
    have hg : Measurable fun q : ((Hist Unit 𝓐 ℝ t × Unit) × 𝓐) × ℝ ↦ (q.1.2, q.2) :=
      (measurable_snd.comp measurable_fst).prodMk measurable_snd
    -- elaborating the composition before unifying with the goal avoids a costly `isDefEq`
    have h := (measurable_ofReal_exp_neg_llr ν ν' t).comp hg
    exact h
  ext p : 1
  rw [Kernel.withDensity_apply _ hm]
  change ν' t p.2 = (ν t p.2).withDensity fun y ↦ ENNReal.ofReal (exp (-llr (ν t p.2) (ν' t p.2) y))
  conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ (hac' t p.2)]
  refine withDensity_congr_ae ?_
  filter_upwards [exp_neg_llr (hac t p.2), Measure.rnDeriv_lt_top (ν' t p.2) (ν t p.2)]
    with y hy hy_lt
  rw [hy, ENNReal.ofReal_toReal hy_lt.ne]

variable (alg : Algorithm Unit 𝓐 ℝ)

omit [Countable 𝓐] [DiscreteMeasurableSpace 𝓐] [∀ t, IsMarkovKernel (ν t)]
  [∀ t, IsMarkovKernel (ν' t)] in
/-- The density of the law of the history of the first `n` rounds against `ν'` with respect to
that against `ν`, evaluated at the history of a trajectory, is `exp(-L_n)`. -/
lemma prod_ofReal_exp_neg_llr_hist (n : ℕ) (ω : ℕ → Round Unit 𝓐 ℝ) :
    ∏ s : Fin n, ENNReal.ofReal (exp (-llr (ν s (IT.hist n ω s).2.1) (ν' s (IT.hist n ω s).2.1)
      (IT.hist n ω s).2.2)) =
      ENNReal.ofReal (exp (-llrProcess ν ν' IT.action IT.feedback n ω)) := by
  rw [← ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (exp_pos _).le, ← exp_sum, llrProcess,
    ← sum_neg_distrib]
  exact congrArg (fun x ↦ ENNReal.ofReal (exp x)) (Fin.sum_univ_eq_sum_range
    (fun s ↦ -llr (ν s (IT.action s ω)) (ν' s (IT.action s ω)) (IT.feedback s ω)) n)

/-- **Change of measure for events of `𝓕_n`**: for mutually absolutely continuous reward laws and
an event `E` determined by the rounds `0, …, n`, `P_ν'(E) = E_ν[1_E exp(-L_{n + 1})]`. -/
lemma trajMeasure_banditSeq_apply_eq_setLIntegral (hac : ∀ t a, ν t a ≪ ν' t a)
    (hac' : ∀ t a, ν' t a ≪ ν t a) {n : ℕ} {S : Set (ℕ → Round Unit 𝓐 ℝ)}
    (hS : MeasurableSet[IT.filtration Unit 𝓐 ℝ n] S) :
    trajMeasure alg (Environment.banditSeq ν') S =
      ∫⁻ ω in S, ENNReal.ofReal (exp (-llrProcess ν ν' IT.action IT.feedback (n + 1) ω))
        ∂(trajMeasure alg (Environment.banditSeq ν)) := by
  rw [IT.filtration_eq_comap] at hS
  obtain ⟨B, hB, rfl⟩ := hS
  set ρ : ℕ → Round Unit 𝓐 ℝ → ℝ≥0∞ :=
    fun t r ↦ ENNReal.ofReal (exp (-llr (ν t r.2.1) (ν' t r.2.1) r.2.2)) with hρ_def
  have hρ : ∀ t, Measurable (ρ t) := fun t ↦ by
    have hg : Measurable fun r : Round Unit 𝓐 ℝ ↦ (r.2.1, r.2.2) :=
      measurable_snd.fst.prodMk measurable_snd.snd
    have h := (measurable_ofReal_exp_neg_llr ν ν' t).comp hg
    exact h
  have hobs : ∀ t, (Environment.banditSeq ν').obs t = (Environment.banditSeq ν).obs t :=
    fun _ ↦ rfl
  have hfeedback : ∀ t, (Environment.banditSeq ν').feedback t =
      ((Environment.banditSeq ν).feedback t).withDensity fun p y ↦ ρ t (p.1.2, p.2, y) :=
    feedback_banditSeq_eq_withDensity hac hac'
  have hlaw := IsAlgEnvSeq.hasLaw_history_withDensity_of_feedback_eq
    (IT.isAlgEnvSeq_trajMeasure alg (Environment.banditSeq ν)) (IT.isAlgEnvSeq_trajMeasure alg _)
    hρ hobs hfeedback (n + 1)
  have hD : Measurable fun hn : Hist Unit 𝓐 ℝ (n + 1) ↦ ∏ s : Fin (n + 1), ρ s (hn s) :=
    Finset.measurable_prod _ fun s _ ↦ (hρ s).comp (measurable_pi_apply s)
  rw [IT.history_obs_action_feedback] at hlaw
  rw [← Measure.map_apply (IT.measurable_hist (n + 1)) hB, hlaw.map_eq,
    withDensity_apply _ hB, setLIntegral_map hB hD (IT.measurable_hist (n + 1))]
  exact setLIntegral_congr_fun ((IT.measurable_hist (n + 1)) hB) fun ω _ ↦
    prod_ofReal_exp_neg_llr_hist (n + 1) ω

/-- **Change of measure at a stopping time**: for mutually absolutely continuous reward laws, a
stopping time `σ` of the history filtration which is finite everywhere and an event `E ∈ 𝓕_σ`,
`P_ν'(E) = E_ν[1_E exp(-L_{σ + 1})]`. -/
lemma trajMeasure_banditSeq_apply_eq_setLIntegral_of_isStoppingTime
    (hac : ∀ t a, ν t a ≪ ν' t a) (hac' : ∀ t a, ν' t a ≪ ν t a)
    {σ : (ℕ → Round Unit 𝓐 ℝ) → ℕ∞} (hσ : IsStoppingTime (IT.filtration Unit 𝓐 ℝ) σ)
    (hfin : ∀ ω, σ ω ≠ ⊤) {S : Set (ℕ → Round Unit 𝓐 ℝ)}
    (hS : MeasurableSet[hσ.measurableSpace] S) :
    trajMeasure alg (Environment.banditSeq ν') S =
      ∫⁻ ω in S,
        ENNReal.ofReal (exp (-llrProcess ν ν' IT.action IT.feedback ((σ ω).toNat + 1) ω))
        ∂(trajMeasure alg (Environment.banditSeq ν)) := by
  set E : ℕ → Set (ℕ → Round Unit 𝓐 ℝ) := fun n ↦ S ∩ {ω | σ ω = n} with hE
  have hE_meas : ∀ n, MeasurableSet[IT.filtration Unit 𝓐 ℝ n] (E n) := fun n ↦
    (hσ.measurableSet_inter_eq_iff S n).1 (hS.inter (hσ.measurableSet_eq_of_countable' n))
  have hE_meas' : ∀ n, MeasurableSet (E n) := fun n ↦
    (IT.filtration Unit 𝓐 ℝ).le n _ (hE_meas n)
  have hdisj : Pairwise (Function.onFun Disjoint E) := by
    intro i j hij
    refine Set.disjoint_left.2 fun ω hωi hωj ↦ hij ?_
    have h := hωi.2.symm.trans hωj.2
    exact_mod_cast h
  have hU : S = ⋃ n, E n := by
    ext ω
    simp only [hE, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, exists_and_left,
      iff_self_and]
    intro _
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (hfin ω)
    exact ⟨n, hn.symm⟩
  rw [hU, measure_iUnion hdisj hE_meas', lintegral_iUnion hE_meas' hdisj]
  refine tsum_congr fun n ↦ ?_
  rw [trajMeasure_banditSeq_apply_eq_setLIntegral alg hac hac' (hE_meas n)]
  refine setLIntegral_congr_fun (hE_meas' n) fun ω hω ↦ ?_
  have hσn : σ ω = n := hω.2
  rw [hσn, ENat.toNat_natCast]

end Bandits
