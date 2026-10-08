/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.LeanMachineLearning.Identification.Basic

/-!
# Stopping almost surely, `δ`-PAC and `δ`-correct identification algorithms

Complements to the PAC property `IdentAlg.IsPAC` of LML's identification algorithms. As for
`IsPAC`, the properties are stated on the laws of the runs of the algorithm, which are determined
by the algorithm and the environment: the law `stoppedHistMeasure` of the history at the stopping
time and the joint law `IdentAlg.histOutputMeasure` of that history and of the output. Each
property comes with a statement about every run of the algorithm (`IdentAlg.IsRun`).

## Main definitions

* `IdentAlg.histOutputMeasure A env`: the joint law of the history at the stopping time and of
  the output of `A` in the environment `env`.
* `IdentAlg.StopsAS A env`: `A` stops almost surely in `env`.
* `IdentAlg.IsDeltaPAC A env bad δ`: `A` is PAC at level `δ` for the family of environments `env`
  and the badness predicate `bad`, and stops almost surely in every `env θ` (the `δ`-PAC property
  of the fixed-confidence literature).
* `IdentAlg.IsDeltaCorrect A env bad δ`: for every `θ`, with probability at most `δ`, `A` does
  not stop or its output is `bad θ` (the `δ`-correctness of Degenne–Koolen 2019, which allows
  non-termination with probability at most `δ`).

## Main results

* `IdentAlg.IsRun.hasLaw_stoppedHist_output`: the joint law of the stopped history and the output
  of every run of `A` in `env` is `A.histOutputMeasure env`.
* `IdentAlg.stopsAS_iff_ae_stoppingTime_ne_top`: `A` stops almost surely iff its stopping time is
  almost surely finite along any algorithm-environment sequence of its sampling rule.
* `IdentAlg.IsDeltaPAC.isDeltaCorrect`, `IdentAlg.IsDeltaCorrect.isPAC`: `δ`-PAC implies
  `δ`-correct, which implies PAC at level `δ`.
* `IdentAlg.IsPAC.of_forall_isRun`: conversely to LML's `IdentAlg.IsPAC.measureReal_bad_of_isRun`,
  a bound on the probability of a bad output for every run (in the universe of the canonical run
  `IdentAlg.runMeasure`) implies the PAC property.
* `IdentAlg.IsPAC.one_sub_le_measureReal_of_isRun`,
  `IdentAlg.IsDeltaCorrect.measureReal_stoppingTime_eq_top_or_bad_of_isRun`,
  `IdentAlg.IsDeltaCorrect.one_sub_le_measureReal_of_isRun`: the properties for every run.
* Monotonicity in the level and in the badness predicate, restriction to subfamilies of
  environments (`IsPAC.mono`, `IsPAC.mono_bad`, `IsPAC.comp` and similarly for the others).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped ENat

namespace Learning.IdentAlg

variable {𝓞 𝓐 𝓨 𝓓 Ω Θ Θ' : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {m𝓓 : MeasurableSpace 𝓓} {mΩ : MeasurableSpace Ω}
  {A : IdentAlg 𝓞 𝓐 𝓨 𝓓} {env : Environment 𝓞 𝓐 𝓨} {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → 𝓐}
  {Y : ℕ → Ω → 𝓨} {out : Ω → 𝓓} {P : Measure Ω}

/-! ### The joint law of the stopped history and the output -/

/-- The joint law of the history at the stopping time and of the output of the identification
algorithm `A` in the environment `env`. -/
noncomputable def histOutputMeasure (A : IdentAlg 𝓞 𝓐 𝓨 𝓓) (env : Environment 𝓞 𝓐 𝓨) :
    Measure ((Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n) × 𝓓) :=
  stoppedHistMeasure A.alg env A.stopSet ⊗ₘ A.output
deriving IsProbabilityMeasure

lemma histOutputMeasure_def :
    A.histOutputMeasure env = stoppedHistMeasure A.alg env A.stopSet ⊗ₘ A.output := rfl

@[simp]
lemma fst_histOutputMeasure :
    (A.histOutputMeasure env).fst = stoppedHistMeasure A.alg env A.stopSet :=
  Measure.fst_compProd _ _

@[simp]
lemma snd_histOutputMeasure : (A.histOutputMeasure env).snd = A.outputMeasure env :=
  Measure.snd_compProd _ _

/-- The joint law of the history at the stopping time and of the output of any run of `A` in
`env` is `A.histOutputMeasure env`. -/
lemma IsRun.hasLaw_stoppedHist_output [IsProbabilityMeasure P] (h : A.IsRun env O X Y out P) :
    HasLaw (fun ω ↦ (A.stoppedHist O X Y ω, out ω)) (A.histOutputMeasure env) P :=
  h.hasLaw_stoppedHist.prodMk_of_hasCondDistrib h.hasCondDistrib_output

/-! ### Stopping almost surely -/

/-- The identification algorithm `A` *stops almost surely* in the environment `env`: almost
surely, the history at the stopping time belongs to the stopping rule, that is, the stopping time
is finite (`stopsAS_iff_ae_stoppingTime_ne_top`). -/
def StopsAS (A : IdentAlg 𝓞 𝓐 𝓨 𝓓) (env : Environment 𝓞 𝓐 𝓨) : Prop :=
  ∀ᵐ h ∂(stoppedHistMeasure A.alg env A.stopSet), h ∈ A.stopSet

/-- `A` stops almost surely in `env` iff its stopping time is almost surely finite along an
algorithm-environment sequence of its sampling rule in `env`. -/
lemma stopsAS_iff_ae_stoppingTime_ne_top [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O X Y A.alg env P) :
    A.StopsAS env ↔ ∀ᵐ ω ∂P, A.stoppingTime O X Y ω ≠ ⊤ := by
  have h_law := (h.hasLaw_stoppedValue_sigmaHistory A.measurableSet_stopSet).ae_iff
    (p := (· ∈ A.stopSet)) (measurableSet_setOfPred.1 A.measurableSet_stopSet)
  rw [StopsAS, ← h_law]
  exact Filter.eventually_congr (.of_forall fun _ ↦ stoppedHist_mem_stopSet_iff)

/-- If `A` stops almost surely in `env`, its stopping time is almost surely finite along every
algorithm-environment sequence of its sampling rule in `env`. -/
lemma StopsAS.ae_stoppingTime_ne_top [IsProbabilityMeasure P] (hA : A.StopsAS env)
    (h : IsAlgEnvSeq O X Y A.alg env P) :
    ∀ᵐ ω ∂P, A.stoppingTime O X Y ω ≠ ⊤ :=
  (stopsAS_iff_ae_stoppingTime_ne_top h).1 hA

/-- If `A` stops almost surely in `env`, its stopping time is finite with probability one along
every algorithm-environment sequence of its sampling rule in `env`. -/
lemma StopsAS.measureReal_stoppingTime_eq_top [IsProbabilityMeasure P] (hA : A.StopsAS env)
    (h : IsAlgEnvSeq O X Y A.alg env P) :
    P.real {ω | A.stoppingTime O X Y ω = ⊤} = 0 := by
  have h_ae := hA.ae_stoppingTime_ne_top h
  rw [ae_iff] at h_ae
  simp only [ne_eq, not_not] at h_ae
  simp [measureReal_def, h_ae]

/-! ### `δ`-PAC and `δ`-correct algorithms -/

/-- `A` is *`δ`-PAC* for the family of environments `env : Θ → Environment 𝓞 𝓐 𝓨` and the
badness predicate `bad : Θ → 𝓓 → Prop`: it is PAC at level `δ` (for every `θ`, its output in
`env θ` is `bad θ` with probability at most `δ`) and it stops almost surely in every `env θ`. -/
def IsDeltaPAC (A : IdentAlg 𝓞 𝓐 𝓨 𝓓) (env : Θ → Environment 𝓞 𝓐 𝓨) (bad : Θ → 𝓓 → Prop)
    (δ : ℝ) : Prop :=
  A.IsPAC env bad δ ∧ ∀ θ, A.StopsAS (env θ)

/-- `A` is *`δ`-correct* for the family of environments `env : Θ → Environment 𝓞 𝓐 𝓨` and the
badness predicate `bad : Θ → 𝓓 → Prop`: for every `θ`, with probability at most `δ`, `A` does
not stop in `env θ` or its output is `bad θ` (the `δ`-correctness of Degenne–Koolen 2019, which
allows non-termination with probability at most `δ`).
See `IsDeltaCorrect.measureReal_stoppingTime_eq_top_or_bad_of_isRun` for the corresponding
statement about any run of `A`. -/
def IsDeltaCorrect (A : IdentAlg 𝓞 𝓐 𝓨 𝓓) (env : Θ → Environment 𝓞 𝓐 𝓨)
    (bad : Θ → 𝓓 → Prop) (δ : ℝ) : Prop :=
  ∀ θ, (A.histOutputMeasure (env θ)).real {p | p.1 ∉ A.stopSet ∨ bad θ p.2} ≤ δ

variable {env : Θ → Environment 𝓞 𝓐 𝓨} {bad bad' : Θ → 𝓓 → Prop} {δ δ' : ℝ}

section IsPAC

/-- The PAC property is monotone in the level. -/
lemma IsPAC.mono (h : A.IsPAC env bad δ) (hδ : δ ≤ δ') : A.IsPAC env bad δ' :=
  fun θ ↦ (h θ).trans hδ

/-- The PAC property is antitone in the badness predicate. -/
lemma IsPAC.mono_bad (h : A.IsPAC env bad δ) (hbad : ∀ θ d, bad' θ d → bad θ d) :
    A.IsPAC env bad' δ :=
  fun θ ↦ (measureReal_mono fun d hd ↦ hbad θ d hd).trans (h θ)

/-- The PAC property is inherited by subfamilies of environments. -/
lemma IsPAC.comp (h : A.IsPAC env bad δ) (f : Θ' → Θ) : A.IsPAC (env ∘ f) (bad ∘ f) δ :=
  fun θ ↦ h (f θ)

/-- For a PAC algorithm at level `δ`, the output of any run in `env θ` is not `bad θ` with
probability at least `1 - δ`. -/
lemma IsPAC.one_sub_le_measureReal_of_isRun [IsProbabilityMeasure P] (hA : A.IsPAC env bad δ)
    {θ : Θ} (hbad : MeasurableSet {d | bad θ d}) (h : A.IsRun (env θ) O X Y out P) :
    1 - δ ≤ P.real {ω | ¬ bad θ (out ω)} := by
  rw [h.hasLaw_output.measureReal_eq (p := fun d ↦ ¬ bad θ d) hbad.compl]
  have h_compl := probReal_compl_eq_one_sub (μ := A.outputMeasure (env θ)) hbad
  rw [Set.compl_ofPred] at h_compl
  rw [h_compl]
  linarith [hA θ]

end IsPAC

/-- **PAC from a bound on every run.** To prove that `A` is PAC at level `δ` it suffices to
bound by `δ` the probability of a bad output for every run of `A` on a probability space in the
universe of the canonical run `runMeasure` (the converse, for runs in any universe, is
`IsPAC.measureReal_bad_of_isRun`). -/
lemma IsPAC.of_forall_isRun.{u, v, w, z} {𝓞 : Type u} {𝓐 : Type v} {𝓨 : Type w} {𝓓 : Type z}
    {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
    {m𝓓 : MeasurableSpace 𝓓} {A : IdentAlg 𝓞 𝓐 𝓨 𝓓} {env : Θ → Environment 𝓞 𝓐 𝓨}
    {bad : Θ → 𝓓 → Prop} {δ : ℝ} (hbad : ∀ θ, MeasurableSet {d | bad θ d})
    (h : ∀ θ, ∀ {Ω : Type (max u v w z)} {_mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (O : ℕ → Ω → 𝓞) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (out : Ω → 𝓓),
      A.IsRun (env θ) O X Y out P → P.real {ω | bad θ (out ω)} ≤ δ) :
    A.IsPAC env bad δ := by
  intro θ
  have hrun := A.isRun_runMeasure (env θ)
  rw [← hrun.hasLaw_output.measureReal_eq (hbad θ)]
  exact h θ _ _ _ _ _ hrun

section StopsAS

lemma IsDeltaPAC.isPAC (h : A.IsDeltaPAC env bad δ) : A.IsPAC env bad δ := h.1

lemma IsDeltaPAC.stopsAS (h : A.IsDeltaPAC env bad δ) (θ : Θ) : A.StopsAS (env θ) := h.2 θ

/-- The `δ`-PAC property is monotone in the level. -/
lemma IsDeltaPAC.mono (h : A.IsDeltaPAC env bad δ) (hδ : δ ≤ δ') : A.IsDeltaPAC env bad δ' :=
  ⟨h.1.mono hδ, h.2⟩

/-- The `δ`-PAC property is antitone in the badness predicate. -/
lemma IsDeltaPAC.mono_bad (h : A.IsDeltaPAC env bad δ) (hbad : ∀ θ d, bad' θ d → bad θ d) :
    A.IsDeltaPAC env bad' δ :=
  ⟨h.1.mono_bad hbad, h.2⟩

/-- The `δ`-PAC property is inherited by subfamilies of environments. -/
lemma IsDeltaPAC.comp (h : A.IsDeltaPAC env bad δ) (f : Θ' → Θ) :
    A.IsDeltaPAC (env ∘ f) (bad ∘ f) δ :=
  ⟨h.1.comp f, fun θ ↦ h.2 (f θ)⟩

end StopsAS

section IsDeltaCorrect

/-- The `δ`-correctness is monotone in the level. -/
lemma IsDeltaCorrect.mono (h : A.IsDeltaCorrect env bad δ) (hδ : δ ≤ δ') :
    A.IsDeltaCorrect env bad δ' :=
  fun θ ↦ (h θ).trans hδ

/-- The `δ`-correctness is antitone in the badness predicate. -/
lemma IsDeltaCorrect.mono_bad (h : A.IsDeltaCorrect env bad δ)
    (hbad : ∀ θ d, bad' θ d → bad θ d) : A.IsDeltaCorrect env bad' δ :=
  fun θ ↦ (measureReal_mono fun _ hp ↦ hp.imp_right (hbad θ _)).trans (h θ)

/-- The `δ`-correctness is inherited by subfamilies of environments. -/
lemma IsDeltaCorrect.comp (h : A.IsDeltaCorrect env bad δ) (f : Θ' → Θ) :
    A.IsDeltaCorrect (env ∘ f) (bad ∘ f) δ :=
  fun θ ↦ h (f θ)

/-- A `δ`-correct algorithm is PAC at level `δ`. -/
lemma IsDeltaCorrect.isPAC (h : A.IsDeltaCorrect env bad δ)
    (hbad : ∀ θ, MeasurableSet {d | bad θ d}) : A.IsPAC env bad δ := by
  intro θ
  refine le_trans ?_ (h θ)
  rw [← snd_histOutputMeasure, measureReal_def, Measure.snd_apply (hbad θ), ← measureReal_def]
  exact measureReal_mono fun _ hp ↦ Or.inr hp

/-- A `δ`-PAC algorithm (PAC at level `δ` and stopping almost surely) is `δ`-correct. -/
lemma IsDeltaPAC.isDeltaCorrect (h : A.IsDeltaPAC env bad δ) : A.IsDeltaCorrect env bad δ := by
  intro θ
  set μ := A.histOutputMeasure (env θ)
  have h_stop : μ.real (Prod.fst ⁻¹' A.stopSetᶜ) = 0 := by
    have h_ae := h.2 θ
    rw [StopsAS, ae_iff] at h_ae
    rw [measureReal_def, ← Measure.fst_apply A.measurableSet_stopSet.compl, fst_histOutputMeasure]
    simp [Set.compl_def, h_ae]
  have h_bad : μ.real (Prod.snd ⁻¹' {d | bad θ d})
      ≤ (A.outputMeasure (env θ)).real {d | bad θ d} := by
    rw [← snd_histOutputMeasure]
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (Measure.le_map_apply measurable_snd.aemeasurable _)
  calc μ.real {p | p.1 ∉ A.stopSet ∨ bad θ p.2}
  _ ≤ μ.real (Prod.fst ⁻¹' A.stopSetᶜ) + μ.real (Prod.snd ⁻¹' {d | bad θ d}) :=
    measureReal_union_le _ _
  _ ≤ δ := by linarith [h.1 θ]

variable [IsProbabilityMeasure P] {θ : Θ}

lemma measurableSet_not_mem_stopSet_or (hbad : MeasurableSet {d | bad θ d}) :
    MeasurableSet {p : (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n) × 𝓓 | p.1 ∉ A.stopSet ∨ bad θ p.2} :=
  (measurable_fst A.measurableSet_stopSet.compl).union (measurable_snd hbad)

/-- For a `δ`-correct algorithm, in any run in `env θ`, with probability at most `δ` the algorithm
does not stop or its output is `bad θ`. -/
lemma IsDeltaCorrect.measureReal_stoppingTime_eq_top_or_bad_of_isRun
    (hA : A.IsDeltaCorrect env bad δ) (hbad : MeasurableSet {d | bad θ d})
    (h : A.IsRun (env θ) O X Y out P) :
    P.real {ω | A.stoppingTime O X Y ω = ⊤ ∨ bad θ (out ω)} ≤ δ := by
  have h_eq := h.hasLaw_stoppedHist_output.measureReal_eq
    (measurableSet_not_mem_stopSet_or (A := A) hbad)
  simp only [stoppedHist_mem_stopSet_iff, not_not] at h_eq
  exact h_eq ▸ hA θ

/-- For a `δ`-correct algorithm, in any run in `env θ`, with probability at least `1 - δ` the
algorithm stops and its output is not `bad θ`. -/
lemma IsDeltaCorrect.one_sub_le_measureReal_of_isRun (hA : A.IsDeltaCorrect env bad δ)
    (hbad : MeasurableSet {d | bad θ d}) (h : A.IsRun (env θ) O X Y out P) :
    1 - δ ≤ P.real {ω | A.stoppingTime O X Y ω ≠ ⊤ ∧ ¬ bad θ (out ω)} := by
  have hS := measurableSet_not_mem_stopSet_or (A := A) hbad
  have h_eq := h.hasLaw_stoppedHist_output.measureReal_eq
    (p := fun q ↦ ¬ (q.1 ∉ A.stopSet ∨ bad θ q.2)) hS.compl
  have h_compl := probReal_compl_eq_one_sub (μ := A.histOutputMeasure (env θ)) hS
  rw [Set.compl_ofPred] at h_compl
  rw [h_compl] at h_eq
  calc 1 - δ
  _ ≤ 1 - (A.histOutputMeasure (env θ)).real {p | p.1 ∉ A.stopSet ∨ bad θ p.2} := by
    linarith [hA θ]
  _ = P.real {ω | A.stoppingTime O X Y ω ≠ ⊤ ∧ ¬ bad θ (out ω)} := by
    rw [← h_eq]
    simp only [not_or, not_not, stoppedHist_mem_stopSet_iff]

end IsDeltaCorrect

end Learning.IdentAlg
