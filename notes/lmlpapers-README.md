# Maynard-Zhang, Xiong, Jamieson, Fazel — On The Complexity of Best-Arm Identification in Non-Stationary Linear Bandits

COLT 2026, paper #136 of the list. arXiv [2603.10346](https://arxiv.org/abs/2603.10346).
Leo Maynard-Zhang, Zhihan Xiong, Kevin Jamieson, Maryam Fazel.

Fixed-budget best-arm identification in a linear bandit whose parameter `θ_t` changes with the
round (adversarially, fixed in advance). The paper characterizes the arm-set-dependent complexity
of the problem as `H_Adjacent(𝒳, Δ) = min_λ max_{(x, x') adjacent} ‖x - x'‖²_{A(λ)⁻¹} / Δ²`, with
a lower bound for every algorithm (Theorem 1) matched by the Adjacent-BAI algorithm (Theorem 2).

Results are numbered with one global counter per environment type (Definitions 1–2, Lemmas 1–10,
Theorems 1–2, Proposition 1, Algorithm 1), in order of appearance (main text, then appendices).

## Formalization choices

* **Library additions** (`LMLPapers/LeanMachineLearning/`):
  `Online/Bandit/Linear/Basic.lean`: general noise laws `ξ` in the reward kernel `linearKernel 𝒳 θ ξ`
  (reward `⟪x, θ⟫ + ε`, `ε ~ ξ`) and the non-stationary environment `nonstationaryLinearEnv 𝒳 θ ξ`
  (oblivious environment with round-dependent parameters and noise laws); `Design.lean`:
  design distributions `IsDesign 𝒳 w` and design matrices `designMatrix w = ∑ w x • x xᵀ`
  (ported from colt-2026-83);
  `Online/Bandit/Nonstationary.lean`: cumulative means, best arm and log-likelihood ratio process of a
  non-stationary bandit; `SequentialLearning/Algorithms/RandomOrder.lean`: the algorithm playing a fixed allocation
  in uniformly random order (as sampling without replacement); `ForMathlib/`: the squared
  Mahalanobis norm `‖x‖²_A`, vertices (exposed points of the convex hull) and adjacent vertices
  (exposed segments) of a finite set, the discrete σ-algebra on permutations.
* **Arm set**: a `Finset (EuclideanSpace ℝ ι)`; the actions of the algorithms are its elements
  (LML's `IdentAlg Unit 𝒳 ℝ 𝒳`, fixed budget `T`: `IdentAlg.IsFixedBudget`, and Algorithm 1
  built with `IdentAlg.fixedBudget`, `Identification/FixedBudget.lean`); the parameter sequence
  is `θ : ℕ → EuclideanSpace ℝ ι` (only `θ_0, …, θ_{T-1}` matter). Noise: independent centered `1`-sub-Gaussian
  (`HasSubgaussianMGF id 1 (ξ t)`) in the upper bounds, standard Gaussian in the lower bounds
  (as in the paper's proofs).
* **Best arm, min-gap** (`Setting.lean`): `IsBestArm 𝒳 θ T x` (maximizer of `⟪·, θ̄_T⟫` over
  `𝒳`; for integrable centered noise, `T ⟪x, θ̄_T⟫` is the cumulative mean of `x` in the
  library's non-stationary bandit `fun t ↦ linearKernel 𝒳 (θ t) (ξ t)`, `cumMean_linearKernel`,
  so that on `𝒳` it is the library's `Bandits.IsBestArm`); `MinGapGE 𝒳 θ T Δ` says that some arm beats every other vertex of `conv 𝒳` by `Δ` (the
  min-gap is at least `Δ`; for `Δ > 0` this arm is the unique best arm). Theorem 2 is stated
  with `MinGapGE` for an arbitrary `Δ > 0`, which is equivalent to the statement with `Δ` equal to
  the min-gap.
* **Mahalanobis norms and designs**: `‖v‖²_{A(λ)⁻¹}` is `mahalanobisSq (designMatrix w)⁻¹ v`;
  the minima over designs are taken over designs with positive definite design matrix
  (`PosDefDesign`), which avoids pseudo-inverses (this does not change the values). The
  optimization problem of Lemma 3 is `optValue`, with inner problem `pairValue` under the
  constraints `PairFeasible`.
* **Algorithm 1** (`adjacentBAI x`): parametrized by the allocation `x_1, …, x_T`; the rounding
  step is replaced by the hypothesis `IsAdjacentRounding 𝒳 x` (the guarantee of Pukelsheim's
  rounding procedure, Eq. (roundingerror), which is all the proof uses). The random order is
  `Algorithm.randomOrder x`; the least-squares estimator (`lsEstimator`) uses the allocation matrix
  `∑_t x_t x_tᵀ` as in Step 9; the output is `argmax_{x ∈ 𝒳} ⟪x, θ̂_T⟫` (a fixed tie-breaking).
* **Lemma 2** is stated for arbitrary finite arm types, any best arms `k ≠ k'` of the two models,
  with the finiteness of the Kullback–Leibler divergences as hypothesis (the paper assumes
  densities). **Lemma 6** is stated on the trajectory space of LML's Ionescu–Tulcea construction
  (`trajMeasure`), for a stopping time of the history filtration which is finite everywhere.
* **Lemma 9**: the uniform permutation is `PMF.uniformOfFintype (Equiv.Perm (Fin T))`, the
  statistic being a function of the permutation.

## Results

| Result | Status | File / declaration |
| --- | --- | --- |
| Definition 1 (extreme points, adjacency) | formalized (library) | `ForMathlib/Analysis/Convex/Adjacent.lean`: `Set.vertices`, `Set.IsAdjacent`, `Set.adjacentPairs`, `Set.adjacentTo`, `Set.vertexPairs` |
| Lemma 1 (adjacency lemma) | formalized | `Lemma1.lean`, `exists_pos_inner_iff` |
| Theorem 1 (arm-set-dependent lower bound) | formalized | `Theorem1.lean`, `exists_minGapGE_le_max_error` |
| Lemma 2 (change-of-measure lower bound) | formalized | `Lemma2.lean`, `le_max_prob_ne` |
| Definition 2 (feasible sequences) | formalized | `Setting.lean`, `FeasibleSeqs` |
| Lemma 3 (optimization-based lower bound) | formalized | `Lemma3.lean`, `exists_minGapGE_le_max_error_optValue` |
| Lemma 4 (closed form for adjacent pairs) | formalized | `Lemma4.lean`, `pairValue_eq` |
| Algorithm 1 (Adjacent-BAI) | formalized | `Setting.lean`, `adjacentBAI` |
| Theorem 2 (error probability of Adjacent-BAI) | formalized | `Theorem2.lean`, `prob_ne_bestArm_le` |
| Lemma 5 (sub-Gaussian least-squares error) | formalized | `Lemma5.lean`, `hasSubgaussianMGF_lsEstimator` |
| Proposition 1 (fixed-confidence complexity) | formalized | `Proposition1.lean`, `iInf_iSup_ratio_eq` |
| Lemma 6 (change of measure at a stopping time) | formalized | `Lemma6.lean`, `trajMeasure_eq_lintegral_exp_neg_llrProcess` |
| Lemma 7 (inner problem, lower bound) | formalized | `Lemma7.lean`, `le_pairValue` |
| Lemma 8 (inner problem, upper bound) | formalized | `Lemma8.lean`, `pairValue_le` |
| Lemma 9 (permuted statistic is sub-Gaussian) | formalized | `Lemma9.lean`, `hasSubgaussianMGF_sum_perm` |
| Lemma 10 (worst ratio at an adjacent vertex) | formalized | `Lemma10.lean`, `ratio_le_iSup_adjacentTo` |
| Eq. (kiefer), `H_Adjacent ≤ 4 H_G`, circle example | not numbered statements | background / discussion, skipped |
| Appendix C (computing the adjacent set, LP1/LP2) | not a numbered statement | algorithmic procedure and its correctness discussion, skipped |

Notes on the statements:

* Theorem 1 / Lemma 3: the two parameter sequences are shown to exist for the given algorithm;
  the conclusion holds for all runs of the algorithm in the two Gaussian environments (runs on
  possibly different probability spaces of the same universe). The hypothesis `span 𝒳 = ℝ^d` of
  the setting is included.
* Lemma 4, 7, 8, 10 and Proposition 1 are pure convex-geometry / linear-algebra statements; the
  best arm in Lemma 10 and Proposition 1 is assumed unique (otherwise the ratios are undefined).
* Lemma 5 and Theorem 2 quantify over runs of `adjacentBAI x` in `nonstationaryLinearEnv 𝒳 θ ξ`;
  Lemma 5 assumes `∑_t x_t x_tᵀ` positive definite ("spanning allocation"), which in Theorem 2
  follows from the rounding guarantee.
