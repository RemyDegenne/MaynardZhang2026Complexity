/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MaynardZhang2026Complexity.LeanMachineLearning.SequentialLearning.Algorithms.RandomOrder
public import MaynardZhang2026Complexity.Mathlib.MeasureTheory.MeasurableSpace.Instances
public import MaynardZhang2026Complexity.Mathlib.Probability.HasCondDistrib.Countable
public import MaynardZhang2026Complexity.Mathlib.Probability.ProbabilityMassFunction.Uniform

/-!
# Playing an allocation in the order of a uniformly random permutation

`Algorithm.randomOrder x` samples the arms of the allocation `x : Fin T → 𝓐` without replacement:
at round `n < T` it plays a uniform arm among those not yet played (`remaining x h`). This file
shows that the arms `x (π 0), …, x (π (T - 1))` for a uniformly random permutation `π` have these
conditional laws, which identifies the law of the actions of a run of `Algorithm.randomOrder x`
(see `Bandits.Linear.isAlgEnvSeqUntil_randomOrder_prod_infinitePi` for the run in a
non-stationary linear environment).

## Main definitions

* `permArm x n π`: the arm `x (π n)` of round `n < T` when `x` is played in the order `π`.

## Main statements

* `Learning.remaining_eq_map_Ici`: if `x ∘ π` starts with `h`, the arms not yet played are the
  values of `x ∘ π` at the positions `j ≥ n`;
* `Learning.card_filter_perm_mul`: the counting identity behind sampling without replacement;
* `Learning.hasCondDistrib_apply_perm`, `Learning.hasCondDistrib_permArm`: for a uniform
  permutation `π` and `n < T`, the conditional law of `x (π n)` given `x (π 0), …, x (π (n - 1))`
  is the uniform law on the arms not yet played.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

open scoped ENNReal

namespace Learning

section Counting

variable {𝓐 : Type*} [DecidableEq 𝓐] {T n : ℕ}

/-- If `x ∘ π` starts with `h` (on the positions `i < n`), the arms of the allocation `x` not yet
played are the values of `x ∘ π` at the positions `j ≥ n`. -/
lemma remaining_eq_map_Ici (hn : n < T) (x : Fin T → 𝓐) (h : Fin n → 𝓐)
    (π : Equiv.Perm (Fin T)) (hπ : ∀ i : Fin n, x (π (Fin.castLE hn.le i)) = h i) :
    remaining x h = Multiset.map (x ∘ π) (Ici (⟨n, hn⟩ : Fin T)).val := by
  have h1 : Multiset.map x univ.val = Multiset.map (x ∘ π) univ.val := by
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
  have h2 : (univ : Finset (Fin T)).val
      = (univ.filter fun j : Fin T ↦ j < ⟨n, hn⟩).val + (Ici (⟨n, hn⟩ : Fin T)).val := by
    rw [← Multiset.filter_add_not (fun j : Fin T ↦ j < ⟨n, hn⟩) univ.val, filter_val]
    congr 1
    rw [← filter_val]
    congr 1
    ext j
    simp
  have h3 : Multiset.map h univ.val
      = Multiset.map (x ∘ π) (univ.filter fun j : Fin T ↦ j < ⟨n, hn⟩).val := by
    have : (univ.filter fun j : Fin T ↦ j < ⟨n, hn⟩) = univ.map (Fin.castLEEmb hn.le) := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_map, Fin.coe_castLEEmb]
      refine ⟨fun hj ↦ ⟨⟨j, hj⟩, rfl⟩, ?_⟩
      rintro ⟨i, -, rfl⟩
      exact i.2
    rw [this, map_val, Multiset.map_map]
    congr 1
    funext i
    exact (hπ i).symm
  rw [remaining, h1, h2, Multiset.map_add, h3, add_tsub_cancel_left]

/-- Counting permutations: for `n < T`, the number of permutations `π` such that `x ∘ π` starts
with `h` and `x (π n) = y`, times `T - n`, is the number of permutations such that `x ∘ π` starts
with `h`, times the multiplicity of `y` among the arms not yet played. -/
lemma card_filter_perm_mul (hn : n < T) (x : Fin T → 𝓐) (h : Fin n → 𝓐) (y : 𝓐) :
    #(univ.filter fun π : Equiv.Perm (Fin T) ↦
        (∀ i : Fin n, x (π (Fin.castLE hn.le i)) = h i) ∧ x (π ⟨n, hn⟩) = y) * (T - n)
      = #(univ.filter fun π : Equiv.Perm (Fin T) ↦
        ∀ i : Fin n, x (π (Fin.castLE hn.le i)) = h i) * (remaining x h).count y := by
  set a : Fin T := ⟨n, hn⟩ with ha
  set A := univ.filter fun π : Equiv.Perm (Fin T) ↦ ∀ i : Fin n, x (π (Fin.castLE hn.le i)) = h i
    with hA
  have hfilter : (univ.filter fun π : Equiv.Perm (Fin T) ↦
      (∀ i : Fin n, x (π (Fin.castLE hn.le i)) = h i) ∧ x (π a) = y)
      = A.filter fun π ↦ x (π a) = y := by
    rw [hA, filter_filter]
  rw [hfilter]
  -- the number of permutations with `x (π j) = y` does not depend on the position `j ≥ n`
  have hswap (j : Fin T) (hj : j ∈ Ici a) :
      #(A.filter fun π ↦ x (π j) = y) = #(A.filter fun π ↦ x (π a) = y) := by
    rw [mem_Ici] at hj
    have hne (i : Fin n) : Fin.castLE hn.le i ≠ a ∧ Fin.castLE hn.le i ≠ j := by
      refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
      · have := congrArg Fin.val h'
        simp [ha] at this
        omega
      · have := congrArg Fin.val h'
        have hj' : n ≤ (j : ℕ) := hj
        simp at this
        omega
    refine card_bij' (fun π _ ↦ π * Equiv.swap a j) (fun π _ ↦ π * Equiv.swap a j) ?_ ?_ ?_ ?_
    · intro π hπ
      simp only [hA, mem_filter, mem_univ, true_and] at hπ ⊢
      refine ⟨fun i ↦ ?_, ?_⟩
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (hne i).1 (hne i).2]
        exact hπ.1 i
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        exact hπ.2
    · intro π hπ
      simp only [hA, mem_filter, mem_univ, true_and] at hπ ⊢
      refine ⟨fun i ↦ ?_, ?_⟩
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (hne i).1 (hne i).2]
        exact hπ.1 i
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        exact hπ.2
    · intro π _
      simp [mul_assoc]
    · intro π _
      simp [mul_assoc]
  -- double counting
  have hdouble : ∑ j ∈ Ici a, #(A.filter fun π ↦ x (π j) = y)
      = ∑ π ∈ A, #((Ici a).filter fun j ↦ x (π j) = y) := by
    simp only [card_filter]
    exact sum_comm
  have hcount (π : Equiv.Perm (Fin T)) (hπ : π ∈ A) :
      #((Ici a).filter fun j ↦ x (π j) = y) = (remaining x h).count y := by
    simp only [hA, mem_filter, mem_univ, true_and] at hπ
    rw [remaining_eq_map_Ici hn x h π hπ, Multiset.count_map, card_def, filter_val]
    congr 1
    exact Multiset.filter_congr fun j _ ↦ eq_comm
  rw [sum_congr rfl hswap, sum_congr rfl hcount, sum_const, sum_const, smul_eq_mul,
    smul_eq_mul, Fin.card_Ici] at hdouble
  rw [mul_comm, hdouble]

end Counting

section CondDistrib

variable {𝓐 : Type*} [MeasurableSpace 𝓐] [Fintype 𝓐] [Nonempty 𝓐] [MeasurableSingletonClass 𝓐]
  [DecidableEq 𝓐] {T n : ℕ}

/-- **Sampling without replacement.** For a uniformly random permutation `π` and `n < T`, the
conditional law of `x (π n)` given `x (π 0), …, x (π (n - 1))` is the uniform law on the arms of
the allocation `x` not yet played. -/
lemma hasCondDistrib_apply_perm (hn : n < T) (x : Fin T → 𝓐) :
    HasCondDistrib (fun π : Equiv.Perm (Fin T) ↦ x (π ⟨n, hn⟩))
      (fun π (i : Fin n) ↦ x (π (Fin.castLE hn.le i)))
      (Kernel.ofFunOfCountable fun h : Fin n → 𝓐 ↦ multisetUniform (remaining x h))
      (PMF.uniformOfFintype (Equiv.Perm (Fin T))).toMeasure := by
  refine hasCondDistrib_of_countable (measurable_of_countable _) (measurable_of_countable _)
    fun h y ↦ ?_
  have e1 : (fun (π : Equiv.Perm (Fin T)) (i : Fin n) ↦ x (π (Fin.castLE hn.le i))) ⁻¹' {h}
      ∩ (fun π : Equiv.Perm (Fin T) ↦ x (π ⟨n, hn⟩)) ⁻¹' {y}
      = {π | (∀ i : Fin n, x (π (Fin.castLE hn.le i)) = h i) ∧ x (π ⟨n, hn⟩) = y} := by
    ext π
    simp [funext_iff]
  have e0 : (fun (π : Equiv.Perm (Fin T)) (i : Fin n) ↦ x (π (Fin.castLE hn.le i))) ⁻¹' {h}
      = {π | ∀ i : Fin n, x (π (Fin.castLE hn.le i)) = h i} := by
    ext π
    simp [funext_iff]
  rw [e1, e0, PMF.toMeasure_uniformOfFintype_setOf, PMF.toMeasure_uniformOfFintype_setOf]
  change _ = _ * _ * multisetUniform (remaining x h) {y}
  have hkey := card_filter_perm_mul hn x h y
  set N1 := #(univ.filter fun π : Equiv.Perm (Fin T) ↦
    (∀ i : Fin n, x (π (Fin.castLE hn.le i)) = h i) ∧ x (π ⟨n, hn⟩) = y) with hN1
  set N0 := #(univ.filter fun π : Equiv.Perm (Fin T) ↦
    ∀ i : Fin n, x (π (Fin.castLE hn.le i)) = h i) with hN0
  rcases Nat.eq_zero_or_pos N0 with h0 | h0
  · have h1 : N1 = 0 := by
      refine Nat.eq_zero_of_le_zero (h0 ▸ card_le_card fun π hπ ↦ ?_)
      simp only [mem_filter, mem_univ, true_and] at hπ ⊢
      exact hπ.1
    simp [h0, h1]
  obtain ⟨π₀, hπ₀⟩ := card_pos.1 h0
  have hR := remaining_eq_map_Ici hn x h π₀ (by simpa using hπ₀)
  have hcard : Multiset.card (remaining x h) = T - n := by
    rw [hR, Multiset.card_map, ← card_def, Fin.card_Ici]
  have hR0 : remaining x h ≠ 0 := by
    rw [← Multiset.card_pos, hcard]
    omega
  have hofm : PMF.ofMultiset (remaining x h) hR0 y
      = (remaining x h).count y / (Multiset.card (remaining x h) : ℝ≥0∞) := by
    rw [PMF.ofMultiset_apply]
    congr
  rw [multisetUniform, dite_eq_right hR0,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton y), hofm, hcard]
  have hTn : ((T - n : ℕ) : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hN1 : (N1 : ℝ≥0∞) = N0 * (remaining x h).count y / (T - n : ℕ) := by
    rw [ENNReal.eq_div_iff hTn (ENNReal.natCast_ne_top _)]
    exact_mod_cast (mul_comm _ _).trans hkey
  rw [hN1, div_eq_mul_inv, div_eq_mul_inv]
  ac_rfl

/-- The arm of round `n` when the allocation `x` is played in the order `π`: `x (π n)` for
`n < T`, an arbitrary arm afterwards. -/
noncomputable def permArm (x : Fin T → 𝓐) (n : ℕ) (π : Equiv.Perm (Fin T)) : 𝓐 :=
  if h : n < T then x (π ⟨n, h⟩) else Classical.arbitrary 𝓐

omit [MeasurableSpace 𝓐] [Fintype 𝓐] [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐] in
/-- At a round `n < T`, the arm of `permArm x · π` is `x (π n)`. -/
lemma permArm_of_lt (x : Fin T → 𝓐) (hn : n < T) (π : Equiv.Perm (Fin T)) :
    permArm x n π = x (π ⟨n, hn⟩) := dite_eq_left hn

omit [Fintype 𝓐] [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐] in
/-- The arm of a round is a measurable function of the permutation (discrete σ-algebra). -/
@[fun_prop]
lemma measurable_permArm (x : Fin T → 𝓐) (n : ℕ) : Measurable (permArm x n) :=
  measurable_of_countable _

/-- For a uniformly random permutation `π` and `n < T`, the conditional law of the arm
`permArm x n π` of round `n` given the arms of the previous rounds is the uniform law on the arms
of the allocation not yet played: the policy of `Algorithm.randomOrder x`. -/
lemma hasCondDistrib_permArm (hn : n < T) (x : Fin T → 𝓐) :
    HasCondDistrib (permArm x n) (fun π (i : Fin n) ↦ permArm x i π)
      (Kernel.ofFunOfCountable fun h : Fin n → 𝓐 ↦ multisetUniform (remaining x h))
      (PMF.uniformOfFintype (Equiv.Perm (Fin T))).toMeasure := by
  have h1 : permArm x n = fun π : Equiv.Perm (Fin T) ↦ x (π ⟨n, hn⟩) :=
    funext fun π ↦ permArm_of_lt x hn π
  have h2 : (fun π (i : Fin n) ↦ permArm x i π)
      = fun (π : Equiv.Perm (Fin T)) (i : Fin n) ↦ x (π (Fin.castLE hn.le i)) :=
    funext fun π ↦ funext fun i ↦ permArm_of_lt x (i.2.trans hn) π
  rw [h1, h2]
  exact hasCondDistrib_apply_perm hn x

end CondDistrib

end Learning
