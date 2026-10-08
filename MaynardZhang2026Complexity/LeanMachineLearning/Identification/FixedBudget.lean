/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.LeanMachineLearning.Identification.PAC
public import MaynardZhang2026Complexity.LeanMachineLearning.SequentialLearning.Algorithms.OfSeq
public import MaynardZhang2026Complexity.LeanMachineLearning.SequentialLearning.Algorithms.ThenRepeat

/-!
# Fixed-budget and fixed-design identification algorithms

A *fixed-budget* identification algorithm with budget `T` stops after exactly `T` rounds; a
*fixed-confidence* algorithm stops adaptively. A *fixed-design* (non-adaptive) algorithm plays a
fixed sequence of actions, whatever the observations and feedbacks.

## Main definitions

* `IdentAlg.IsFixedBudget A T`: the stopping rule of `A` is "stop after exactly `T` rounds".
* `IdentAlg.fixedBudget alg T ρ`: the fixed-budget identification algorithm with sampling rule
  `alg`, budget `T` and output kernel `ρ` on the histories of `T` rounds.
* `IdentAlg.thenCommit A T`: for an identification algorithm `A` whose outputs are actions, the
  algorithm which plays the sampling rule of `A` for `T` rounds, then commits to the
  recommendation of `A` (`Algorithm.thenRepeat`).
* `Algorithm.IsFixedDesign alg`, `IdentAlg.IsFixedDesign A`: the (sampling rule of the) algorithm
  plays a fixed sequence of actions, that is, it is `Algorithm.ofSeq x` for some `x`.

## Main results

* `IdentAlg.IsFixedBudget.stoppingTime_eq`, `IdentAlg.IsFixedBudget.stoppedHist_eq`: the stopping
  time of a fixed-budget algorithm is its budget, and the stopped history is the history of the
  first `T` rounds.
* `IdentAlg.IsFixedBudget.stoppedHistMeasure_eq`, `IdentAlg.IsFixedBudget.outputMeasure_eq`: the
  laws of the stopped history and of the output.
* `IdentAlg.IsFixedBudget.stopsAS`: a fixed-budget algorithm stops almost surely.
* `IdentAlg.IsRun.hasCondDistrib_output_history`: in a run of a fixed-budget algorithm, the
  output has conditional law `A.outputAt T` given the history of the first `T` rounds.
* `IdentAlg.IsFixedBudget.hasLaw_output_of_isAlgEnvSeqUntil`,
  `IdentAlg.IsPAC.measureReal_bad_of_isAlgEnvSeqUntil`: an output drawn from `A.outputAt T` after
  `T` rounds of the sampling rule of `A` (in a longer interaction) has the law of the output of
  `A`, hence the PAC guarantees of `A` apply to it;
  `IdentAlg.IsPAC.measureReal_bad_action_of_thenCommit` is the case of the action committed to by
  `A.thenCommit T`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓞 𝓐 𝓨 𝓓 Ω : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {m𝓓 : MeasurableSpace 𝓓} {mΩ : MeasurableSpace Ω}
  {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {P : Measure Ω}

/-! ### Fixed budget -/

namespace IdentAlg

/-- The identification algorithm `A` is *fixed-budget* with budget `T`: it stops after exactly
`T` rounds. -/
def IsFixedBudget (A : IdentAlg 𝓞 𝓐 𝓨 𝓓) (T : ℕ) : Prop := A.stopSet = {h | h.1 = T}

section IsFixedBudget

variable {A : IdentAlg 𝓞 𝓐 𝓨 𝓓} {T : ℕ}

lemma IsFixedBudget.mem_stopSet_iff (hA : A.IsFixedBudget T) {h : Σ n, Hist 𝓞 𝓐 𝓨 n} :
    h ∈ A.stopSet ↔ h.1 = T := by
  rw [hA, Set.mem_ofPred_eq]

/-- The stopping time of a fixed-budget algorithm with budget `T` is `T`. -/
lemma IsFixedBudget.stoppingTime_eq (hA : A.IsFixedBudget T) (ω : Ω) :
    A.stoppingTime O X Y ω = T := by
  rw [stoppingTime_eq_coe_iff, hA.mem_stopSet_iff]
  exact ⟨rfl, fun j hj h ↦ hj.ne (hA.mem_stopSet_iff.1 h)⟩

/-- The stopping time of a fixed-budget algorithm is finite. -/
lemma IsFixedBudget.stoppingTime_ne_top (hA : A.IsFixedBudget T) (ω : Ω) :
    A.stoppingTime O X Y ω ≠ ⊤ := by
  rw [hA.stoppingTime_eq]
  exact ENat.natCast_ne_top T

/-- The history at the stopping time of a fixed-budget algorithm with budget `T` is the history
of the first `T` rounds. -/
lemma IsFixedBudget.stoppedHist_eq (hA : A.IsFixedBudget T) (ω : Ω) :
    A.stoppedHist O X Y ω = ⟨T, history O X Y T ω⟩ :=
  stoppedHist_eq_of_stoppingTime_eq (hA.stoppingTime_eq ω)

/-- The law of the history at the stopping time of a fixed-budget algorithm with budget `T` is
the law of the history of the first `T` rounds. -/
lemma IsFixedBudget.stoppedHistMeasure_eq (hA : A.IsFixedBudget T) (env : Environment 𝓞 𝓐 𝓨) :
    stoppedHistMeasure A.alg env A.stopSet
      = (trajMeasure A.alg env).map (sigmaHistory IT.obs IT.action IT.feedback T) := by
  rw [stoppedHistMeasure]
  congr 1
  funext traj
  exact (hA.stoppedHist_eq (O := IT.obs) (X := IT.action) (Y := IT.feedback) traj)

/-- The law of the output of a fixed-budget algorithm with budget `T`: the output rule on the
histories of `T` rounds applied to the law of the history of the first `T` rounds. -/
lemma IsFixedBudget.outputMeasure_eq (hA : A.IsFixedBudget T) (env : Environment 𝓞 𝓐 𝓨) :
    A.outputMeasure env = A.outputAt T ∘ₘ (trajMeasure A.alg env).map (IT.hist T) := by
  rw [outputMeasure, hA.stoppedHistMeasure_eq,
    show sigmaHistory IT.obs IT.action IT.feedback T = Sigma.mk T ∘ IT.hist T from rfl,
    ← Measure.map_map (measurable_sigma_mk T) (IT.measurable_hist T),
    ← Measure.deterministic_comp_eq_map (measurable_sigma_mk T), Measure.comp_assoc,
    Kernel.comp_deterministic_eq_comap, outputAt]

/-- The law of the output of a fixed-budget algorithm with budget `0` is the output rule applied
to the empty history. -/
lemma outputMeasure_of_isFixedBudget_zero (hA : A.IsFixedBudget 0) (env : Environment 𝓞 𝓐 𝓨) :
    A.outputMeasure env = A.output ⟨0, default⟩ := by
  rw [hA.outputMeasure_eq, IT.hist_zero, Measure.map_const, measure_univ, one_smul,
    Measure.dirac_bind (Kernel.measurable _), outputAt_apply]

/-- A fixed-budget algorithm stops almost surely. -/
lemma IsFixedBudget.stopsAS (hA : A.IsFixedBudget T) (env : Environment 𝓞 𝓐 𝓨) :
    A.StopsAS env := by
  rw [StopsAS, hA.stoppedHistMeasure_eq]
  exact (ae_map_iff (measurable_sigmaHistory IT.measurable_obs IT.measurable_action
    IT.measurable_feedback T).aemeasurable A.measurableSet_stopSet).2
    (.of_forall fun _ ↦ hA.mem_stopSet_iff.2 rfl)

end IsFixedBudget

/-! ### Runs of fixed-budget algorithms -/

section Run

variable {A : IdentAlg 𝓞 𝓐 𝓨 𝓓} {T : ℕ} {env : Environment 𝓞 𝓐 𝓨} {out : Ω → 𝓓}

/-- **In a run of a fixed-budget algorithm with budget `T`, the output has conditional law
`A.outputAt T` given the history of the first `T` rounds.** -/
lemma IsRun.hasCondDistrib_output_history [IsFiniteMeasure P] (hA : A.IsFixedBudget T)
    (h : A.IsRun env O X Y out P) :
    HasCondDistrib out (history O X Y T) (A.outputAt T) P := by
  have h1 := h.hasCondDistrib_output
  rw [show A.stoppedHist O X Y = Sigma.mk T ∘ history O X Y T from funext hA.stoppedHist_eq] at h1
  exact h1.of_measurableEmbedding_comp_right (measurableEmbedding_sigma_mk T)

/-- For a fixed-budget algorithm whose output rule on the histories of `T` rounds is the
deterministic map `g`, the output of a run is almost surely `g` of the history of the first `T`
rounds. -/
lemma IsRun.output_ae_eq_of_outputAt_eq_deterministic [MeasurableEq 𝓓] [IsFiniteMeasure P]
    (hA : A.IsFixedBudget T) (h : A.IsRun env O X Y out P) {g : Hist 𝓞 𝓐 𝓨 T → 𝓓}
    (hg : Measurable g) (hout : A.outputAt T = Kernel.deterministic g hg) :
    out =ᵐ[P] fun ω ↦ g (history O X Y T ω) := by
  have h1 := h.hasCondDistrib_output_history hA
  rw [hout] at h1
  exact ae_eq_of_hasCondDistrib_deterministic hg (h.isAlgEnvSeq.measurable_history T).aemeasurable
    h.hasCondDistrib_output.aemeasurable_snd h1

/-- For a run of a fixed-budget algorithm with budget `0`, the law of the output is the output
rule applied to the empty history. -/
lemma IsRun.map_out_eq_of_isFixedBudget_zero [IsProbabilityMeasure P] (hA : A.IsFixedBudget 0)
    (h : A.IsRun env O X Y out P) :
    P.map out = A.output ⟨0, default⟩ := by
  rw [h.hasLaw_output.map_eq, outputMeasure_of_isFixedBudget_zero hA]

/-- If `A` has budget `T`, `(O, X, Y)` is an algorithm-environment sequence for the sampling rule
of `A` until time `T` (the interaction may go on after time `T` with another algorithm) and `out`
has conditional law `A.outputAt T` given the history of the first `T` rounds, then `out` has the
law of the output of `A`. -/
lemma IsFixedBudget.hasLaw_output_of_isAlgEnvSeqUntil [IsProbabilityMeasure P]
    (hA : A.IsFixedBudget T) (h : IsAlgEnvSeqUntil O X Y A.alg env P T)
    (hout : HasCondDistrib out (history O X Y T) (A.outputAt T) P) :
    HasLaw out (A.outputMeasure env) P := by
  have h_comp := hout.hasLaw_comp
  rwa [h.map_history, ← hA.outputMeasure_eq] at h_comp

variable {Θ : Type*} {env : Θ → Environment 𝓞 𝓐 𝓨} {bad : Θ → 𝓓 → Prop} {δ : ℝ} {θ : Θ}

/-- **Transfer of a PAC guarantee to a partial run.** If `A` is PAC at level `δ` with budget `T`,
`(O, X, Y)` is an algorithm-environment sequence for the sampling rule of `A` until time `T` in
`env θ` and `out` has conditional law `A.outputAt T` given the history of the first `T` rounds,
then `out` is `bad θ` with probability at most `δ`. -/
lemma IsPAC.measureReal_bad_of_isAlgEnvSeqUntil [IsProbabilityMeasure P]
    (hpac : A.IsPAC env bad δ) (hA : A.IsFixedBudget T) (hbad : MeasurableSet {d | bad θ d})
    (h : IsAlgEnvSeqUntil O X Y A.alg (env θ) P T)
    (hout : HasCondDistrib out (history O X Y T) (A.outputAt T) P) :
    P.real {ω | bad θ (out ω)} ≤ δ := by
  rw [(hA.hasLaw_output_of_isAlgEnvSeqUntil h hout).measureReal_eq hbad]
  exact hpac θ

end Run

/-- The output rule of `fixedBudget alg T ρ` after `n` rounds: `ρ` if `n = T`, and an arbitrary
constant otherwise (never used). -/
noncomputable def fixedBudgetOutput [Nonempty 𝓓] (T : ℕ) (ρ : Kernel (Hist 𝓞 𝓐 𝓨 T) 𝓓)
    (n : ℕ) : Kernel (Hist 𝓞 𝓐 𝓨 n) 𝓓 :=
  if h : n = T then ρ.comap (fun x i ↦ x (Fin.cast h.symm i)) (by fun_prop)
  else Kernel.const _ (Measure.dirac (Classical.arbitrary 𝓓))

instance [Nonempty 𝓓] (T : ℕ) (ρ : Kernel (Hist 𝓞 𝓐 𝓨 T) 𝓓) [IsMarkovKernel ρ] (n : ℕ) :
    IsMarkovKernel (fixedBudgetOutput T ρ n) := by
  unfold fixedBudgetOutput
  split <;> infer_instance

@[simp]
lemma fixedBudgetOutput_self [Nonempty 𝓓] (T : ℕ) (ρ : Kernel (Hist 𝓞 𝓐 𝓨 T) 𝓓) :
    fixedBudgetOutput T ρ T = ρ := by
  ext h : 1
  simp [fixedBudgetOutput]

/-- The fixed-budget identification algorithm with sampling rule `alg`, budget `T` and output
kernel `ρ` on the histories of `T` rounds. -/
noncomputable def fixedBudget [Nonempty 𝓓] (alg : Algorithm 𝓞 𝓐 𝓨) (T : ℕ)
    (ρ : Kernel (Hist 𝓞 𝓐 𝓨 T) 𝓓) [IsMarkovKernel ρ] : IdentAlg 𝓞 𝓐 𝓨 𝓓 :=
  ofStop alg (fun n _ ↦ n = T) (fun n ↦ by by_cases h : n = T <;> simp [h])
    (fixedBudgetOutput T ρ)

section FixedBudget

variable [Nonempty 𝓓] (alg : Algorithm 𝓞 𝓐 𝓨) (T : ℕ) (ρ : Kernel (Hist 𝓞 𝓐 𝓨 T) 𝓓)
  [IsMarkovKernel ρ]

@[simp]
lemma alg_fixedBudget : (fixedBudget alg T ρ).alg = alg := rfl

lemma isFixedBudget_fixedBudget : (fixedBudget alg T ρ).IsFixedBudget T := rfl

/-- The output rule of `fixedBudget alg T ρ` after `T` rounds is `ρ`. -/
@[simp]
lemma output_fixedBudget_mk (h : Hist 𝓞 𝓐 𝓨 T) :
    (fixedBudget alg T ρ).output ⟨T, h⟩ = ρ h := by
  rw [fixedBudget, output_ofStop_mk, fixedBudgetOutput_self]

/-- The output rule of `fixedBudget alg T ρ` on the histories of `T` rounds is `ρ`. -/
@[simp]
lemma outputAt_fixedBudget : (fixedBudget alg T ρ).outputAt T = ρ := by
  rw [fixedBudget, outputAt_ofStop, fixedBudgetOutput_self]

end FixedBudget

/-! ### Committing to the recommendation -/

section ThenCommit

variable {A : IdentAlg 𝓞 𝓐 𝓨 𝓐} {T : ℕ}

/-- For an identification algorithm `A` whose outputs are actions, the algorithm which plays the
sampling rule of `A` for `T` rounds, then commits to the recommendation of `A`: it draws an action
from the output rule of `A` on the history of these `T` rounds and plays it forever. -/
noncomputable def thenCommit (A : IdentAlg 𝓞 𝓐 𝓨 𝓐) (T : ℕ) : Algorithm 𝓞 𝓐 𝓨 :=
  A.alg.thenRepeat T (A.outputAt T)

/-- For a fixed-budget algorithm `A` with budget `T`, the action committed to by `A.thenCommit T`
(played at every round from round `T` on) has the law of the output of `A`. -/
lemma IsFixedBudget.hasLaw_action_thenCommit [IsProbabilityMeasure P] {env : Environment 𝓞 𝓐 𝓨}
    (hA : A.IsFixedBudget T) (h : IsAlgEnvSeq O X Y (A.thenCommit T) env P) :
    HasLaw (X T) (A.outputMeasure env) P :=
  hA.hasLaw_output_of_isAlgEnvSeqUntil h.isAlgEnvSeqUntil_of_thenRepeat
    h.hasCondDistrib_action_of_thenRepeat

/-- **The PAC guarantee of `A` applies to the action committed to by `A.thenCommit T`.** -/
lemma IsPAC.measureReal_bad_action_of_thenCommit [IsProbabilityMeasure P] {Θ : Type*}
    {env : Θ → Environment 𝓞 𝓐 𝓨} {bad : Θ → 𝓐 → Prop} {δ : ℝ} {θ : Θ}
    (hpac : A.IsPAC env bad δ) (hA : A.IsFixedBudget T) (hbad : MeasurableSet {a | bad θ a})
    (h : IsAlgEnvSeq O X Y (A.thenCommit T) (env θ) P) :
    P.real {ω | bad θ (X T ω)} ≤ δ :=
  hpac.measureReal_bad_of_isAlgEnvSeqUntil hA hbad h.isAlgEnvSeqUntil_of_thenRepeat
    h.hasCondDistrib_action_of_thenRepeat

end ThenCommit

end IdentAlg

/-! ### Fixed design -/

section FixedDesign

include m𝓞 m𝓐 m𝓨

/-- The algorithm `alg` is a *fixed-design* (non-adaptive) algorithm: it plays a fixed sequence
of actions. -/
def Algorithm.IsFixedDesign (alg : Algorithm 𝓞 𝓐 𝓨) : Prop := ∃ x : ℕ → 𝓐, alg = Algorithm.ofSeq x

lemma isFixedDesign_ofSeq (x : ℕ → 𝓐) :
    (Algorithm.ofSeq x : Algorithm 𝓞 𝓐 𝓨).IsFixedDesign :=
  ⟨x, rfl⟩

/-- The identification algorithm `A` is a *fixed-design* (non-adaptive) algorithm: its sampling
rule plays a fixed sequence of actions; its stopping and output rules are arbitrary. -/
abbrev IdentAlg.IsFixedDesign (A : IdentAlg 𝓞 𝓐 𝓨 𝓓) : Prop := A.alg.IsFixedDesign

end FixedDesign

end Learning
