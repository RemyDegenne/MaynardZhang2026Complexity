/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.MXJF2026.Setting
public import MaynardZhang2026Complexity.MXJF2026.Lemma2
public import MaynardZhang2026Complexity.MXJF2026.Optimization
public import MaynardZhang2026Complexity.LeanMachineLearning.Design
public import MaynardZhang2026Complexity.LeanMachineLearning.SequentialLearning.AgreeingEnvironments
public import MaynardZhang2026Complexity.Mathlib.InformationTheory.KullbackLeibler.Gaussian

/-!
# Lemma 3: the optimization-based lower bound

The lower bound of Theorem 1 with the optimization value `f(𝒳, Δ)` (`optValue`) in place of
`4 / H_Adjacent(𝒳, Δ)`.

## Construction

The construction differs from the paper's (which splits the horizon in two halves). Given the
algorithm, let `λ_x = (1/T) ∑_{t < T} P_0(X_t = x)` be the design of the expected arm frequencies
of a run against `θ ≡ 0`, and `(θ̃, ṽ)` a feasible point of a pair of distinct vertices with
`ṽᵀ A(λ) ṽ < 2 f(𝒳, Δ)` (`exists_pairFeasible_lt_two_mul_optValue`). The two instances are
`θ_t = 0`, `θ'_t = ṽ` for `t < T - 1` and `θ_{T-1} = T θ̃`, `θ'_{T-1} = T θ̃ + ṽ`: their averages
are `θ̃` and `θ̃ + ṽ`, which have min-gap at least `Δ` with best arms `x ≠ x'`, and the actions of
the first `T` rounds against `θ` have the same laws as against `0`
(`IsAlgEnvSeq.identDistrib_action_of_env_eq`), so that Lemma 2 (`le_max_prob_ne`) applies with
the exponent `∑_{t < T} ∑_a P_0(X_t = a) ⟪a, ṽ⟫² / 2 = (T/2) ṽᵀ A(λ) ṽ < T f(𝒳, Δ)`.

## Main statements

* `isBestArm_iff_eq_of_forall_vertices`: an arm beating every other vertex by `Δ > 0` is the
  unique best arm.
* `avgParam_ite_eq`, `avgParam_add_const`: the averages of the two parameter sequences.
* `exists_minGapGE_le_max_error_optValue`: Lemma 3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Learning Bandits.Linear Real Set Matrix
open scoped RealInnerProductSpace

universe u

namespace MaynardZhang2026Complexity

variable {ι : Type*} [Fintype ι]

/-- If `x ∈ 𝒳` beats every other vertex of `conv 𝒳` by `Δ > 0` for `θ̄_T`, it is the unique best
arm. -/
lemma isBestArm_iff_eq_of_forall_vertices {𝒳 : Set (EuclideanSpace ℝ ι)} (h𝒳 : 𝒳.Finite)
    {Δ : ℝ} (hΔ : 0 < Δ) {θ : ℕ → EuclideanSpace ℝ ι} {T : ℕ} {x : EuclideanSpace ℝ ι}
    (hx : x ∈ 𝒳) (h : ∀ y ∈ vertices 𝒳, y ≠ x → Δ ≤ ⟪x - y, avgParam θ T⟫)
    {z : EuclideanSpace ℝ ι} :
    IsBestArm 𝒳 θ T z ↔ z = x := by
  have hlt : ∀ y ∈ 𝒳, y ≠ x → ⟪y, avgParam θ T⟫ < ⟪x, avgParam θ T⟫ := fun y hy hyx ↦
    h𝒳.inner_lt_of_forall_mem_vertices (fun v hv hvx ↦ by
      have := h v hv hvx
      rw [inner_sub_left] at this
      linarith) hy hyx
  refine ⟨fun ⟨hz, hzmax⟩ ↦ ?_, ?_⟩
  · by_contra hzx
    exact (hlt z hz hzx).not_ge (hzmax x hx)
  · rintro rfl
    refine ⟨hx, fun y hy ↦ ?_⟩
    rcases eq_or_ne y z with rfl | hyz
    · exact le_rfl
    · exact (hlt y hy hyz).le

omit [Fintype ι] in
/-- The average of the parameter sequence equal to `T θ` at round `T - 1` and to `0` before is
`θ`. -/
lemma avgParam_ite_eq {T : ℕ} (hT : T ≠ 0) (θ : EuclideanSpace ℝ ι) :
    avgParam (fun t ↦ if t = T - 1 then (T : ℝ) • θ else 0) T = θ := by
  have hT' : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hT
  simp only [avgParam, Finset.sum_ite_eq', Finset.mem_range, Nat.sub_one_lt hT, ite_true,
    smul_smul, inv_mul_cancel₀ hT', one_smul]

omit [Fintype ι] in
/-- Adding a constant vector to every parameter adds it to the average. -/
lemma avgParam_add_const {T : ℕ} (hT : T ≠ 0) (θ : ℕ → EuclideanSpace ℝ ι)
    (v : EuclideanSpace ℝ ι) :
    avgParam (fun t ↦ θ t + v) T = avgParam θ T + v := by
  have hT' : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hT
  rw [avgParam, avgParam, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_add,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hT', one_smul]

/-- **Lemma 3** (optimization-based lower bound, Maynard-Zhang, Xiong, Jamieson, Fazel 2026).
Fix a finite arm set `𝒳 ⊆ ℝ^d` and `Δ > 0`. For every identification algorithm with
budget `T` there are parameter sequences `θ`, `θ'`, both with min-gap at least `Δ`, such that
`max(P_θ(x̂ ≠ x⋆), P_θ'(x̂ ≠ x⋆')) ≥ (1/4) exp(-T f(𝒳, Δ))`.

The paper leaves implicit that `T ≥ 1` and that `𝒳` has at least two points (for `T = 0` no
parameter sequence has min-gap `Δ > 0`; for a single arm `f(𝒳, Δ) = 0`, an infimum over no pairs,
while every algorithm is always right). The arm set need not span the space. -/
theorem exists_minGapGE_le_max_error_optValue (𝒳 : Finset (EuclideanSpace ℝ ι))
    (h𝒳 : 𝒳.Nontrivial) {Δ : ℝ} (hΔ : 0 < Δ) {T : ℕ} (hT : T ≠ 0)
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
        1 / 4 * exp (-(T * optValue (𝒳 : Set (EuclideanSpace ℝ ι)) Δ)) ≤
          max (P.real {ω | ¬ IsBestArm 𝒳 θ T (out ω)})
            (P'.real {ω | ¬ IsBestArm 𝒳 θ' T (out' ω)}) := by
  classical
  have hT' : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hT
  -- the design of the expected arm frequencies of a run against `θ ≡ 0`
  set env₀ := nonstationaryLinearEnv (𝒳 : Set (EuclideanSpace ℝ ι)) (fun _ ↦ 0)
    (fun _ ↦ gaussianReal 0 1) with henv₀
  set P₀ := trajMeasure A.alg env₀
  have h₀ : IsAlgEnvSeq IT.obs IT.action IT.feedback A.alg env₀ P₀ :=
    IT.isAlgEnvSeq_trajMeasure _ _
  set q : 𝒳 → ℝ := fun a ↦ (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, P₀.real {ω | IT.action t ω = a}
    with hq
  have hq0 : ∀ a, 0 ≤ q a := fun a ↦ by positivity
  have h1 : ∀ t, ∑ a : 𝒳, P₀.real {ω | IT.action t ω = a} = 1 := fun t ↦ by
    have h := sum_measureReal_preimage_singleton (μ := P₀) (Finset.univ : Finset 𝒳)
      (f := IT.action t) (fun y _ ↦ IT.measurable_action t (measurableSet_singleton y))
    rw [Finset.coe_univ, Set.preimage_univ, probReal_univ] at h
    exact h
  have hq1 : ∑ a, q a = 1 := by
    rw [hq, ← Finset.mul_sum, Finset.sum_comm, Finset.sum_congr rfl fun t _ ↦ h1 t]
    simp [hT']
  set w := designOfWeights 𝒳 q with hw_def
  have hw : IsDesign 𝒳 w := isDesign_designOfWeights hq0 hq1
  have hw_quad : ∀ v, mahalanobisSq (designMatrix w) v
      = ∑ a, q a * ⟪(a : EuclideanSpace ℝ ι), v⟫ ^ 2 :=
    mahalanobisSq_designMatrix_designOfWeights
  -- a pair of distinct vertices and a feasible point
  obtain ⟨x, x', θ₀, v, hxx', hfeas, hlt⟩ := exists_pairFeasible_lt_two_mul_optValue 𝒳 h𝒳 hΔ hw
  have hx : x ∈ 𝒳 := vertices_subset hxx'.1
  have hx' : x' ∈ 𝒳 := vertices_subset hxx'.2.1
  set θ : ℕ → EuclideanSpace ℝ ι := fun t ↦ if t = T - 1 then (T : ℝ) • θ₀ else 0 with hθ
  set θ' : ℕ → EuclideanSpace ℝ ι := fun t ↦ θ t + v with hθ'
  have havg : avgParam θ T = θ₀ := avgParam_ite_eq hT θ₀
  have havg' : avgParam θ' T = θ₀ + v := by rw [hθ', avgParam_add_const hT, havg]
  have hgap : ∀ y ∈ vertices (𝒳 : Set (EuclideanSpace ℝ ι)), y ≠ x →
      Δ ≤ ⟪x - y, avgParam θ T⟫ := havg ▸ hfeas.1
  have hgap' : ∀ y ∈ vertices (𝒳 : Set (EuclideanSpace ℝ ι)), y ≠ x' →
      Δ ≤ ⟪x' - y, avgParam θ' T⟫ := havg' ▸ hfeas.2
  refine ⟨θ, θ', ⟨x, hx, hgap⟩, ⟨x', hx', hgap'⟩, ?_⟩
  intro Ω _ P _ X Y out Ω' _ P' _ X' Y' out' h h'
  -- the error events
  have hE : {ω | ¬ IsBestArm 𝒳 θ T (out ω)} = {ω | out ω ≠ ⟨x, hx⟩} := by
    ext ω
    simp only [Set.mem_ofPred_eq, ne_eq,
      isBestArm_iff_eq_of_forall_vertices 𝒳.finite_toSet hΔ hx hgap, Subtype.ext_iff]
  have hE' : {ω | ¬ IsBestArm 𝒳 θ' T (out' ω)} = {ω | out' ω ≠ ⟨x', hx'⟩} := by
    ext ω
    simp only [Set.mem_ofPred_eq, ne_eq,
      isBestArm_iff_eq_of_forall_vertices 𝒳.finite_toSet hΔ hx' hgap', Subtype.ext_iff]
  -- the divergences
  have hkl : ∀ t (a : 𝒳), klDiv (linearKernel 𝒳 (θ t) (gaussianReal 0 1) a)
      (linearKernel 𝒳 (θ' t) (gaussianReal 0 1) a) =
        ENNReal.ofReal (⟪(a : EuclideanSpace ℝ ι), v⟫ ^ 2 / 2) := by
    intro t a
    rw [linearKernel_gaussianReal_apply, linearKernel_gaussianReal_apply,
      InformationTheory.klDiv_gaussianReal_one, hθ', inner_add_right]
    congr 2
    ring
  have hne : (⟨x, hx⟩ : 𝒳) ≠ ⟨x', hx'⟩ := fun h ↦ hxx'.2.2 (congrArg Subtype.val h)
  have hrun : A.IsRun (Environment.banditSeq fun t ↦ linearKernel (𝒳 : Set (EuclideanSpace ℝ ι))
      (θ t) (gaussianReal 0 1)) (fun _ _ ↦ ()) X Y out P := h
  have hrun' : A.IsRun (Environment.banditSeq fun t ↦ linearKernel (𝒳 : Set (EuclideanSpace ℝ ι))
      (θ' t) (gaussianReal 0 1)) (fun _ _ ↦ ()) X' Y' out' P' := h'
  have h2 := le_max_prob_ne _ _ T (fun t a ↦ by rw [hkl]; exact ENNReal.ofReal_ne_top) hne A hA
    P X Y out P' X' Y' out' hrun hrun'
  rw [hE, hE']
  refine le_trans ?_ h2
  gcongr
  -- the law of the actions of the first `T` rounds against `θ` is that against `0`
  have hlaw : ∀ t ∈ Finset.range T, ∀ a : 𝒳,
      P.real {ω | X t ω = a} = P₀.real {ω | IT.action t ω = a} := by
    intro t ht a
    have hfb : ∀ n < t, (nonstationaryLinearEnv (𝒳 : Set (EuclideanSpace ℝ ι)) θ
        fun _ ↦ gaussianReal 0 1).feedback n = env₀.feedback n := by
      intro n hn
      have hn' : n ≠ T - 1 := by
        have := Finset.mem_range.1 ht
        omega
      rw [henv₀, feedback_nonstationaryLinearEnv, feedback_nonstationaryLinearEnv, hθ]
      simp only [hn', ite_false]
    have hid := h.isAlgEnvSeq.identDistrib_action_of_env_eq h₀ (fun n _ ↦ rfl) hfb
    rw [measureReal_def, measureReal_def]
    exact congrArg ENNReal.toReal (hid.measure_mem_eq (measurableSet_singleton a))
  calc ∑ a : 𝒳, ∑ t ∈ Finset.range T, P.real {ω | X t ω = a} *
        (klDiv (linearKernel 𝒳 (θ t) (gaussianReal 0 1) a)
          (linearKernel 𝒳 (θ' t) (gaussianReal 0 1) a)).toReal
      = T / 2 * ∑ a : 𝒳, q a * ⟪(a : EuclideanSpace ℝ ι), v⟫ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        have hterm : ∀ t ∈ Finset.range T, P.real {ω | X t ω = a} *
            (klDiv (linearKernel 𝒳 (θ t) (gaussianReal 0 1) a)
              (linearKernel 𝒳 (θ' t) (gaussianReal 0 1) a)).toReal =
            P₀.real {ω | IT.action t ω = a} * (⟪(a : EuclideanSpace ℝ ι), v⟫ ^ 2 / 2) := by
          intro t ht
          rw [hkl, ENNReal.toReal_ofReal (by positivity), hlaw t ht a]
        rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, hq]
        field_simp
    _ = T / 2 * mahalanobisSq (designMatrix w) v := by rw [hw_quad]
    _ ≤ T / 2 * (2 * optValue (𝒳 : Set (EuclideanSpace ℝ ι)) Δ) := by gcongr
    _ = T * optValue (𝒳 : Set (EuclideanSpace ℝ ι)) Δ := by ring

end MaynardZhang2026Complexity
