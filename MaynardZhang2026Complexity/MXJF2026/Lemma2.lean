/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.MXJF2026.Setting
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import MaynardZhang2026Complexity.Mathlib.InformationTheory.KullbackLeibler.BretagnolleHuber
public import MaynardZhang2026Complexity.LeanMachineLearning.Identification.ChangeOfMeasure
public import MaynardZhang2026Complexity.LeanMachineLearning.SequentialLearning.DivergenceDecomposition

/-!
# Lemma 2: the change-of-measure lower bound for non-stationary bandits

For two non-stationary bandit models `ν`, `ν'` with different best arms over `T` rounds and a
fixed-budget identification algorithm with budget `T`,
`max(P_ν(k̂ ≠ k⋆), P_ν'(k̂ ≠ k⋆'))` is at least
`(1/4) exp(-∑_k ∑_{t < T} P_ν(A_t = k) KL(ν_{t, k}, ν'_{t, k}))`.
This generalizes Lemma 15 of Kaufmann, Cappé, Garivier (2016).

The proof applies the Bretagnolle–Huber inequality to the laws of the outputs, whose divergence
is at most that of the laws of the histories of the `T` rounds (data processing for fixed-budget
algorithms, `IdentAlg.IsRun.klDiv_map_out_le`), computed by the divergence decomposition for
non-stationary bandits (`IsAlgEnvSeq.klDiv_map_history_banditSeq_eq_sum`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Learning Real
open scoped ENNReal

universe u

namespace MaynardZhang2026Complexity

variable {𝓐 : Type*} [Fintype 𝓐] [MeasurableSpace 𝓐] [DiscreteMeasurableSpace 𝓐]

/-- **Lemma 2** (Maynard-Zhang, Xiong, Jamieson, Fazel 2026). Let `ν`, `ν'` be non-stationary
bandit models (with finite Kullback–Leibler divergences), `k ≠ k'` two arms (in the paper, the
best arms of `ν` and `ν'` over `T` rounds; the proof only uses `k ≠ k'`) and `A` an identification
algorithm with budget `T`. For all runs of `A` under `ν` and under `ν'`,
`max(P_ν(k̂ ≠ k), P_ν'(k̂ ≠ k'))` is at least
`(1/4) exp(-∑_k ∑_{t < T} P_ν(A_t = k) KL(ν_{t, k} ‖ ν'_{t, k}))`. -/
theorem le_max_prob_ne (ν ν' : ℕ → Kernel 𝓐 ℝ) [∀ t, IsMarkovKernel (ν t)]
    [∀ t, IsMarkovKernel (ν' t)] (T : ℕ) (hkl : ∀ t k, klDiv (ν t k) (ν' t k) ≠ ∞)
    {k k' : 𝓐} (hne : k ≠ k')
    (A : IdentAlg Unit 𝓐 ℝ 𝓐) (hA : A.IsFixedBudget T)
    {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (out : Ω → 𝓐)
    {Ω' : Type u} {_mΩ' : MeasurableSpace Ω'} (P' : Measure Ω') [IsProbabilityMeasure P']
    (X' : ℕ → Ω' → 𝓐) (Y' : ℕ → Ω' → ℝ) (out' : Ω' → 𝓐)
    (h : A.IsRun (Environment.banditSeq ν) (fun _ _ ↦ ()) X Y out P)
    (h' : A.IsRun (Environment.banditSeq ν') (fun _ _ ↦ ()) X' Y' out' P') :
    1 / 4 * exp (-(∑ a, ∑ t ∈ Finset.range T,
        P.real {ω | X t ω = a} * (klDiv (ν t a) (ν' t a)).toReal)) ≤
      max (P.real {ω | out ω ≠ k}) (P'.real {ω | out' ω ≠ k'}) := by
  set S := ∑ a, ∑ t ∈ Finset.range T, P.real {ω | X t ω = a} * (klDiv (ν t a) (ν' t a)).toReal
  set D := ∑ t ∈ Finset.range T, ∑ a, P {ω | X t ω = a} * klDiv (ν t a) (ν' t a) with hD
  have hout : AEMeasurable out P := h.hasCondDistrib_output.aemeasurable_snd
  have hout' : AEMeasurable out' P' := h'.hasCondDistrib_output.aemeasurable_snd
  have h_term : ∀ t a, P {ω | X t ω = a} * klDiv (ν t a) (ν' t a) ≠ ∞ := fun t a ↦
    ENNReal.mul_ne_top (measure_ne_top _ _) (hkl t a)
  have h_fin : D ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun t _ ↦ ENNReal.sum_ne_top.2 fun a _ ↦ h_term t a
  have h_toReal : D.toReal = S := by
    rw [hD, ENNReal.toReal_sum fun t _ ↦ ENNReal.sum_ne_top.2 fun a _ ↦ h_term t a]
    simp_rw [ENNReal.toReal_sum fun a _ ↦ h_term _ a, ENNReal.toReal_mul, ← measureReal_def]
    exact Finset.sum_comm
  have h_le : klDiv (P.map out) (P'.map out') ≤ D :=
    (h.klDiv_map_out_le hA h').trans_eq
      (h.isAlgEnvSeq.klDiv_map_history_banditSeq_eq_sum h'.isAlgEnvSeq T)
  have h_ne : klDiv (P.map out) (P'.map out') ≠ ∞ := ne_top_of_le_ne_top h_fin h_le
  have h_kl : (klDiv (P.map out) (P'.map out')).toReal ≤ S :=
    h_toReal ▸ ENNReal.toReal_mono h_fin h_le
  have hBH := bretagnolle_huber (μ := P.map out) (ν := P'.map out') (A := {a | a ≠ k})
    (DiscreteMeasurableSpace.forall_measurableSet _) h_ne
  rw [map_measureReal_apply_of_aemeasurable hout (DiscreteMeasurableSpace.forall_measurableSet _),
    map_measureReal_apply_of_aemeasurable hout' (DiscreteMeasurableSpace.forall_measurableSet _)]
    at hBH
  have h_sub : P'.real (out' ⁻¹' {a | a ≠ k}ᶜ) ≤ P'.real {ω | out' ω ≠ k'} := by
    refine measureReal_mono (fun ω hω ↦ ?_)
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] at hω
    simpa [hω] using hne
  have h_exp : exp (-S) ≤ exp (-(klDiv (P.map out) (P'.map out')).toReal) :=
    exp_le_exp.2 (neg_le_neg h_kl)
  have h1 := le_max_left (P.real {ω | out ω ≠ k}) (P'.real {ω | out' ω ≠ k'})
  have h2 := le_max_right (P.real {ω | out ω ≠ k}) (P'.real {ω | out' ω ≠ k'})
  change exp (-(klDiv (P.map out) (P'.map out')).toReal) / 2 ≤
    P.real {ω | out ω ≠ k} + P'.real (out' ⁻¹' {a | a ≠ k}ᶜ) at hBH
  linarith

end MaynardZhang2026Complexity
