/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.Algorithm

/-!
# Playing an algorithm, then repeating an action drawn from the history

`Algorithm.thenRepeat alg T ρ` is the algorithm which plays `alg` for the first `T` rounds, then
draws an action from the kernel `ρ` applied to the history of these rounds and plays that action
forever. When `ρ` is the output rule of an identification algorithm whose outputs are actions,
this is the algorithm which commits to the recommendation of the identification algorithm
(`IdentAlg.thenCommit`, in
`MaynardZhang2026Complexity.LeanMachineLearning.Identification.FixedBudget`).

## Main definitions

* `Algorithm.thenRepeat alg T ρ`: play `alg` for `T` rounds, then repeat an action drawn from `ρ`
  applied to the history of these rounds.

## Main statements

For an algorithm-environment sequence `(O, X, Y)` of `alg.thenRepeat T ρ`:
* `IsAlgEnvSeq.isAlgEnvSeqUntil_of_thenRepeat`: it is an algorithm-environment sequence for
  `alg` until time `T`;
* `IsAlgEnvSeq.hasCondDistrib_action_of_thenRepeat`: the action at round `T` has conditional law
  `ρ` given the history of the first `T` rounds;
* `IsAlgEnvSeq.action_ae_eq_of_thenRepeat`, `IsAlgEnvSeq.action_add_ae_eq_of_thenRepeat`,
  `IsAlgEnvSeq.ae_forall_action_add_eq_of_thenRepeat`: the actions at the rounds after `T` are
  almost surely the action at round `T`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓞 𝓐 𝓨 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨}

namespace Algorithm

variable (alg : Algorithm 𝓞 𝓐 𝓨) (T : ℕ) (ρ : Kernel (Hist 𝓞 𝓐 𝓨 T) 𝓐) [IsMarkovKernel ρ]

/-- The policy at round `t` of `alg.thenRepeat T ρ`: the policy of `alg` for `t < T`, the kernel
`ρ` applied to the history of the first `T` rounds for `t = T`, and the deterministic choice of
the action played at round `T` for `t > T`. -/
noncomputable def thenRepeatPolicy (t : ℕ) : Kernel (Hist 𝓞 𝓐 𝓨 t × 𝓞) 𝓐 :=
  if h : T < t then
    Kernel.deterministic (fun x ↦ (x.1 ⟨T, h⟩).action) (by fun_prop)
  else if ht : t = T then
    ρ.comap (fun x (i : Fin T) ↦ x.1 (Fin.castLE ht.ge i)) (by fun_prop)
  else alg.policy t

instance (t : ℕ) : IsMarkovKernel (thenRepeatPolicy alg T ρ t) := by
  unfold thenRepeatPolicy
  split_ifs <;> infer_instance

/-- The algorithm which plays `alg` for the first `T` rounds, then draws an action from `ρ`
applied to the history of these rounds and plays that action forever. -/
noncomputable def thenRepeat : Algorithm 𝓞 𝓐 𝓨 where
  policy := thenRepeatPolicy alg T ρ

lemma thenRepeat_policy_of_lt {t : ℕ} (ht : t < T) :
    (alg.thenRepeat T ρ).policy t = alg.policy t := by
  change thenRepeatPolicy alg T ρ t = _
  rw [thenRepeatPolicy, dite_eq_right (by omega), dite_eq_right (by omega)]

lemma thenRepeat_policy_self : (alg.thenRepeat T ρ).policy T = ρ.prodMkRight 𝓞 := by
  simp only [thenRepeat, thenRepeatPolicy, lt_self_iff_false, ↓reduceDIte]
  rfl

lemma thenRepeat_policy_of_gt {t : ℕ} (ht : T < t) :
    (alg.thenRepeat T ρ).policy t =
      Kernel.deterministic (fun x ↦ (x.1 ⟨T, ht⟩).action) (by fun_prop) := by
  simp [thenRepeat, thenRepeatPolicy, ht]

end Algorithm

section Run

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {alg : Algorithm 𝓞 𝓐 𝓨}
  {env : Environment 𝓞 𝓐 𝓨} {T : ℕ} {ρ : Kernel (Hist 𝓞 𝓐 𝓨 T) 𝓐} [IsMarkovKernel ρ]

/-- An algorithm-environment sequence of `alg.thenRepeat T ρ` is an algorithm-environment
sequence for `alg` until time `T`. -/
lemma IsAlgEnvSeq.isAlgEnvSeqUntil_of_thenRepeat
    (h : IsAlgEnvSeq O X Y (alg.thenRepeat T ρ) env P) : IsAlgEnvSeqUntil O X Y alg env P T :=
  h.isAlgEnvSeqUntil_of_policy_eq fun _ ht ↦ alg.thenRepeat_policy_of_lt T ρ ht

/-- Under `alg.thenRepeat T ρ`, the action at round `T` has conditional law `ρ` given the history
of the first `T` rounds. -/
lemma IsAlgEnvSeq.hasCondDistrib_action_of_thenRepeat
    (h : IsAlgEnvSeq O X Y (alg.thenRepeat T ρ) env P) :
    HasCondDistrib (X T) (history O X Y T) ρ P := by
  have h1 := h.hasCondDistrib_action T
  rw [Algorithm.thenRepeat_policy_self] at h1
  exact h1.comp_right

/-- Under `alg.thenRepeat T ρ`, the action at a round `t > T` is almost surely the action at
round `T`. -/
lemma IsAlgEnvSeq.action_ae_eq_of_thenRepeat [MeasurableEq 𝓐]
    (h : IsAlgEnvSeq O X Y (alg.thenRepeat T ρ) env P) {t : ℕ} (ht : T < t) :
    X t =ᵐ[P] X T := by
  have h1 := h.hasCondDistrib_action t
  rw [Algorithm.thenRepeat_policy_of_gt alg T ρ ht] at h1
  exact ae_eq_of_hasCondDistrib_deterministic
    (f := fun x : Hist 𝓞 𝓐 𝓨 t × 𝓞 ↦ (x.1 ⟨T, ht⟩).action) (by fun_prop)
    ((h.measurable_history t).prodMk (h.measurable_obs t)).aemeasurable
    (h.measurable_action t).aemeasurable h1

/-- Under `alg.thenRepeat T ρ`, the action at round `T + s` is almost surely the action at
round `T`. -/
lemma IsAlgEnvSeq.action_add_ae_eq_of_thenRepeat [MeasurableEq 𝓐]
    (h : IsAlgEnvSeq O X Y (alg.thenRepeat T ρ) env P) (s : ℕ) :
    X (T + s) =ᵐ[P] X T := by
  cases s with
  | zero => rfl
  | succ s => exact h.action_ae_eq_of_thenRepeat (t := T + (s + 1)) (by omega)

/-- Under `alg.thenRepeat T ρ`, almost surely, the actions at all the rounds after `T` are the
action at round `T`. -/
lemma IsAlgEnvSeq.ae_forall_action_add_eq_of_thenRepeat [MeasurableEq 𝓐]
    (h : IsAlgEnvSeq O X Y (alg.thenRepeat T ρ) env P) :
    ∀ᵐ ω ∂P, ∀ s, X (T + s) ω = X T ω :=
  ae_all_iff.2 fun s ↦ h.action_add_ae_eq_of_thenRepeat s

end Run

end Learning
