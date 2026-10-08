/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import MaynardZhang2026Complexity.Mathlib.MeasureTheory.MeasurableSpace.Instances
public import MaynardZhang2026Complexity.Mathlib.Probability.Moments.SubGaussian
public import MaynardZhang2026Complexity.Mathlib.Probability.ProbabilityMassFunction.Uniform

/-!
# Sums over a uniformly random permutation: sampling without replacement

For vectors `a_0, …, a_{n-1}` and `g_0, …, g_{n-1}` of a real inner product space with
`‖g_k‖ ≤ M`, and a uniformly random permutation `π` of `{0, …, n - 1}`, the statistic
`∑_s ⟪a_s, g_{π(s)} - ḡ⟫` (`ḡ` the mean of the `g_k`) is sub-Gaussian with variance proxy
`8 M² ∑_s ‖a_s - ā‖²`, `ā` the mean of the `a_s`: the positions `s` sample the values `g_k`
without replacement.

The proof is by induction on `n`: a uniform permutation of `{0, …, n}` is a uniform first value
`π(0)` and an independent uniform bijection between the remaining positions and values
(`Equiv.Perm.decomposeFin`); the statistic is the centered bounded term
`⟪a_0 - ā', g_{π(0)} - ḡ⟫` (`ā'` the mean of `a_1, …, a_n`, Hoeffding's lemma) plus the statistic
of the remaining positions and values (induction hypothesis), and the variance proxies add up
through the Helmert identity for the centered sums of squares (`sum_norm_sub_mean_sq_succ`).

## Main statements

* `sum_norm_sub_mean_sq`: `∑_s ‖a_s - ā‖² = ∑_s ‖a_s‖² - ‖∑_s a_s‖² / n`;
* `sum_norm_sub_mean_sq_succ`: the Helmert identity
  `∑_s ‖a_s - ā‖² = ∑_{s ≥ 1} ‖a_s - ā'‖² + n / (n + 1) ‖a_0 - ā'‖²`;
* `ProbabilityTheory.hasSubgaussianMGF_sum_inner_perm`: sampling without replacement.
-/

@[expose] public section

open MeasureTheory Finset

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The centered sum of squares: `∑_s ‖a_s - ā‖² = ∑_s ‖a_s‖² - ‖∑_s a_s‖² / n`. -/
lemma sum_norm_sub_mean_sq {n : ℕ} (a : Fin n → E) :
    ∑ s, ‖a s - (n : ℝ)⁻¹ • ∑ s', a s'‖ ^ 2 = ∑ s, ‖a s‖ ^ 2 - (n : ℝ)⁻¹ * ‖∑ s, a s‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp_rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [sum_add_distrib, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, ← mul_sum,
    ← mul_sum, ← sum_inner, nsmul_eq_mul, real_inner_self_eq_norm_sq]
  field_simp
  ring

/-- **Helmert identity.** Removing the first point of a family `a_0, …, a_n` decreases its
centered sum of squares by `n / (n + 1) ‖a_0 - ā'‖²`, where `ā'` is the mean of the remaining
points. -/
lemma sum_norm_sub_mean_sq_succ {n : ℕ} (hn : n ≠ 0) (a : Fin (n + 1) → E) :
    ∑ s, ‖a s - ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ s', a s'‖ ^ 2
      = ∑ s : Fin n, ‖a s.succ - (n : ℝ)⁻¹ • ∑ s' : Fin n, a s'.succ‖ ^ 2
        + n / (n + 1) * ‖a 0 - (n : ℝ)⁻¹ • ∑ s : Fin n, a s.succ‖ ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [sum_norm_sub_mean_sq, sum_norm_sub_mean_sq, Fin.sum_univ_succ, Fin.sum_univ_succ,
    norm_add_sq_real, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs]
  push_cast
  field_simp
  ring

namespace ProbabilityTheory

/-- **Sampling without replacement.** Let `a_0, …, a_{n-1}` and `g_0, …, g_{n-1}` be vectors with
`‖g_k‖ ≤ M` and `π` a uniformly random permutation of `{0, …, n - 1}`. Then
`∑_s ⟪a_s, g_{π(s)} - ḡ⟫` is sub-Gaussian with variance proxy `8 M² ∑_s ‖a_s - ā‖²`, where `ḡ`
and `ā` are the means of the `g_k` and of the `a_s`. -/
lemma hasSubgaussianMGF_sum_inner_perm {n : ℕ} (a g : Fin n → E) {M : ℝ}
    (hg : ∀ k, ‖g k‖ ≤ M) :
    HasSubgaussianMGF (fun π : Equiv.Perm (Fin n) ↦ ∑ s, ⟪a s, g (π s) - (n : ℝ)⁻¹ • ∑ k, g k⟫)
      (8 * M ^ 2 * ∑ s, ‖a s - (n : ℝ)⁻¹ • ∑ s', a s'‖ ^ 2).toNNReal
      (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure := by
  induction n with
  | zero =>
    simp only [univ_eq_empty, sum_empty]
    exact HasSubgaussianMGF.fun_zero.mono zero_le
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- a single position: the statistic vanishes
      have h0 : (fun π : Equiv.Perm (Fin (0 + 1)) ↦
          ∑ s, ⟪a s, g (π s) - ((0 + 1 : ℕ) : ℝ)⁻¹ • ∑ k, g k⟫) = fun _ ↦ 0 := by
        funext π
        simp [Fin.eq_zero (π 0)]
      rw [h0]
      exact HasSubgaussianMGF.fun_zero.mono zero_le
    have hM : 0 ≤ M := (norm_nonneg _).trans (hg 0)
    set S := ∑ k, g k with hS
    set gbar := ((n + 1 : ℕ) : ℝ)⁻¹ • S with hgbar
    set d := a 0 - (n : ℝ)⁻¹ • ∑ k : Fin n, a k.succ with hd
    -- the values left after `π 0 = p`, indexed by `Fin n`
    let τ : Fin (n + 1) → Fin n → Fin (n + 1) := fun p k ↦ Equiv.swap 0 p k.succ
    -- the statistic of the remaining positions and values
    let V : Fin (n + 1) → Equiv.Perm (Fin n) → ℝ := fun p σ ↦
      ∑ k, ⟪a k.succ, g (τ p (σ k)) - (n : ℝ)⁻¹ • ∑ k', g (τ p k')⟫
    -- the contribution of the first position
    let U : Fin (n + 1) → ℝ := fun p ↦ ⟪d, g p - gbar⟫
    have hsum_τ (p : Fin (n + 1)) : ∑ k, g (τ p k) = S - g p := by
      rw [hS, ← Equiv.sum_comp (Equiv.swap 0 p), Fin.sum_univ_succ, Equiv.swap_apply_left]
      abel
    have hgbar_norm : ‖gbar‖ ≤ M := by
      rw [hgbar, norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast,
        inv_mul_le_iff₀ (by positivity)]
      calc ‖S‖ ≤ ∑ k, ‖g k‖ := norm_sum_le _ _
        _ ≤ ∑ _k : Fin (n + 1), M := sum_le_sum fun k _ ↦ hg k
        _ = (n + 1 : ℕ) * M := by simp
    have h_decomp (p : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) :
        ∑ s, ⟪a s, g (Equiv.Perm.decomposeFin.symm (p, σ) s) - gbar⟫ = U p + V p σ := by
      have hsc : (n : ℝ)⁻¹ - ((n : ℝ) + 1)⁻¹ = (n : ℝ)⁻¹ * ((n : ℝ) + 1)⁻¹ := by
        field_simp
        ring
      have hvec : (n : ℝ)⁻¹ • ∑ k', g (τ p k') - gbar = -((n : ℝ)⁻¹ • (g p - gbar)) := by
        rw [hsum_τ, hgbar]
        push_cast
        linear_combination (norm := module) hsc • S
      have h1 (k : Fin n) : ⟪a k.succ, g (τ p (σ k)) - gbar⟫
          = ⟪a k.succ, g (τ p (σ k)) - (n : ℝ)⁻¹ • ∑ k', g (τ p k')⟫
            + ⟪a k.succ, (n : ℝ)⁻¹ • ∑ k', g (τ p k') - gbar⟫ := by
        rw [← inner_add_right]
        congr 1
        abel
      rw [Fin.sum_univ_succ, Equiv.Perm.decomposeFin_symm_apply_zero]
      simp_rw [Equiv.Perm.decomposeFin_symm_apply_succ]
      change _ + ∑ k, ⟪a k.succ, g (τ p (σ k)) - gbar⟫ = _
      rw [sum_congr rfl fun k _ ↦ h1 k, sum_add_distrib, ← sum_inner, hvec, inner_neg_right,
        real_inner_smul_right]
      simp only [U, V, d, inner_sub_left, real_inner_smul_left]
      ring
    -- Hoeffding's lemma for the first position
    have hU : HasSubgaussianMGF U ((‖2 * M * ‖d‖ - -(2 * M * ‖d‖)‖₊ / 2) ^ 2)
        (PMF.uniformOfFintype (Fin (n + 1))).toMeasure := by
      refine hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        (measurable_of_countable U).aemeasurable (ae_of_all _ fun p ↦ ?_) ?_
      · have h1 : |U p| ≤ 2 * M * ‖d‖ := by
          calc |U p| ≤ ‖d‖ * ‖g p - gbar‖ := abs_real_inner_le_norm _ _
            _ ≤ ‖d‖ * (2 * M) := by
              gcongr
              calc ‖g p - gbar‖ ≤ ‖g p‖ + ‖gbar‖ := norm_sub_le _ _
                _ ≤ M + M := add_le_add (hg p) hgbar_norm
                _ = 2 * M := by ring
            _ = 2 * M * ‖d‖ := by ring
        exact ⟨neg_le_of_abs_le h1, le_of_abs_le h1⟩
      · rw [PMF.integral_eq_sum]
        simp only [PMF.uniformOfFintype_apply]
        rw [← smul_sum]
        have : ∑ p, U p = 0 := by
          simp only [U, ← inner_sum, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin]
          rw [← hS, hgbar, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
            mul_inv_cancel₀ (by positivity), one_smul, sub_self, inner_zero_right]
        rw [this, smul_zero]
    -- the induction hypothesis for the remaining positions and values
    have hV (p : Fin (n + 1)) : HasSubgaussianMGF (V p)
        (8 * M ^ 2 * ∑ s : Fin n, ‖a s.succ - (n : ℝ)⁻¹ • ∑ s' : Fin n, a s'.succ‖ ^ 2).toNNReal
        (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure :=
      ih (fun k ↦ a k.succ) (fun k ↦ g (τ p k)) fun k ↦ hg _
    have hUV := hU.add_prod hV (measurable_of_countable _)
    -- transport along `Equiv.Perm.decomposeFin`
    have h_map : ((PMF.uniformOfFintype (Fin (n + 1))).toMeasure.prod
        (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure).map Equiv.Perm.decomposeFin.symm
        = (PMF.uniformOfFintype (Equiv.Perm (Fin (n + 1)))).toMeasure := by
      rw [PMF.toMeasure_uniformOfFintype_prod]
      exact PMF.map_toMeasure_uniformOfFintype_equiv _ (measurable_of_countable _)
    rw [← h_map, ← HasSubgaussianMGF.id_map_iff (measurable_of_countable _).aemeasurable,
      Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
      HasSubgaussianMGF.id_map_iff (measurable_of_countable _).aemeasurable]
    have h_fun : ((fun π : Equiv.Perm (Fin (n + 1)) ↦ ∑ s, ⟪a s, g (π s) - gbar⟫)
        ∘ Equiv.Perm.decomposeFin.symm) = fun q ↦ U q.1 + V q.1 q.2 := by
      funext q
      exact h_decomp q.1 q.2
    rw [h_fun]
    refine hUV.mono ?_
    -- the variance proxies add up (Helmert identity)
    rw [← NNReal.coe_le_coe, NNReal.coe_add, Real.coe_toNNReal _ (by positivity),
      Real.coe_toNNReal _ (by positivity), sum_norm_sub_mean_sq_succ hn.ne' a, ← hd]
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_ofNat]
    rw [show 2 * M * ‖d‖ - -(2 * M * ‖d‖) = 4 * M * ‖d‖ by ring,
      abs_of_nonneg (by positivity)]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (4 * M * ‖d‖ / 2) ^ 2 ≤ 8 * M ^ 2 * (n / (n + 1) * ‖d‖ ^ 2) := by
      rw [show (4 * M * ‖d‖ / 2) ^ 2 = 4 * M ^ 2 * ‖d‖ ^ 2 by ring]
      have h2 : (1 : ℝ) / 2 ≤ n / (n + 1) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        linarith
      nlinarith [sq_nonneg M, sq_nonneg ‖d‖, mul_nonneg (sq_nonneg M) (sq_nonneg ‖d‖)]
    nlinarith [this]

end ProbabilityTheory
