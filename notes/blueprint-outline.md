# Blueprint outline — Maynard-Zhang, Xiong, Jamieson, Fazel, *On the Complexity of Best-Arm Identification in Non-Stationary Linear Bandits* (COLT 2026)

arXiv 2603.10346, source in `source/` (`main.tex`, sections in `main_paper/`, appendices in
`appendix/`). Library `MaynardZhang2026Complexity`, paper directory
`MaynardZhang2026Complexity/MXJF2026/` (namespace `MaynardZhang2026Complexity`), LML branch
`rename`. The statements start from the statement-only formalization in `LMLPapers`
(COLT2026/MaynardZhang2026Complexity, its README is `notes/lmlpapers-README.md`), checked against
the paper and corrected where they were false.

This file fixes the labels, the modelling and the proof routes before the blueprint and the Lean
proofs are written.

## 1. Results of the paper

One counter per environment type, in order of appearance (main text, then appendices).

| Result | Label | Lean (`MaynardZhang2026Complexity.`) | Status |
|---|---|---|---|
| Section 2 (instance, best arm, min-gap) | `def:setting`, `def:min_gap` | `avgParam`, `IsBestArm`, `minGap`, `MinGapGE` | definitions |
| Definition 1 (extreme points, adjacency) | `def:adjacency` | `vertices`, `IsAdjacent`, `adjacentPairs`, `adjacentTo`, `vertexPairs` | definitions |
| Eq. (hadj-def), designs | `def:design`, `def:h_adjacent` | `IsDesign`, `designMatrix`, `PosDefDesign`, `adjValue`, `adjDesignValue`, `hAdjacent` | definitions |
| Lemma 1 (adjacency lemma) | `lem:adjacency` | `exists_pos_inner_iff` | headline |
| Theorem 1 (lower bound) | `thm:lower_bound` | `exists_minGapGE_le_max_error` | headline |
| Lemma 2 (non-stationary Kaufmann et al. bound) | `lem:gen_lower` | `le_max_prob_ne` | headline |
| Definition 2 (feasible sequences) | `def:feasible` | `FeasibleSeqs` | definition |
| Lemma 3 (optimization-based lower bound) | `lem:opt_lower` | `exists_minGapGE_le_max_error_optValue` | headline |
| Eq. (optimization) | `def:opt_value` | `PairFeasible`, `pairValue`, `optValue` | definitions |
| Lemma 4 (closed form for adjacent pairs) | `lem:equality` | `pairValue_eq` | headline |
| Algorithm 1 (Adjacent-BAI) | `def:adjacent_bai` | `allocMatrix`, `IsAdjacentRounding`, `lsEstimator`, `recommend`, `adjacentBAI` | definitions |
| Theorem 2 (error of Adjacent-BAI) | `thm:upper_bound` | `prob_ne_bestArm_le` | headline |
| Lemma 5 (sub-Gaussian least squares) | `lem:ls_subgaussian` | `hasSubgaussianMGF_lsEstimator` | headline |
| Proposition 1 (stationary complexity) | `prop:stat_equiv` | `iInf_iSup_ratio_eq` | headline |
| Lemma 6 (change of measure at a stopping time) | `lem:change_of_measure` | `trajMeasure_eq_lintegral_exp_neg_llrProcess` | headline |
| Lemma 7 (lower bound on the inner problem) | `lem:pair_value_lower` | `le_pairValue` | headline |
| Lemma 8 (upper bound on the inner problem) | `lem:pair_value_upper` | `pairValue_le` | headline |
| Lemma 9 (random permutation sum) | `lem:perm_subgaussian` | `hasSubgaussianMGF_sum_perm` | headline |
| Lemma 10 (ratio at adjacent arms) | `lem:ratio_adjacent` | `ratio_le_iSup_adjacentTo` | headline |
| Appendix C (computing `ℐ`), Section 6 (future work) | — | — | not formalized (an algorithm and its running time; discussion) |

## 2. Modelling decisions

* **Arm set**: `𝒳 : Finset (EuclideanSpace ℝ ι)`, `d = card ι`; the algorithms are LML
  identification algorithms `IdentAlg Unit 𝒳 ℝ 𝒳` (actions and outputs are arms), the environment
  `nonstationaryLinearEnv 𝒳 θ ξ` gives the reward `⟪x, θ t⟫ + ε` with `ε ~ ξ t` at round `t`
  (rounds are numbered from `0`; only `θ 0, …, θ (T - 1)` matter). Standard Gaussian noise in the
  lower bounds, centered `1`-sub-Gaussian noise (`HasSubgaussianMGF id 1 (ξ t)`) in the upper
  bounds.
* **Fixed budget**: `IdentAlg.IsFixedBudget T`; the lower bounds quantify over all runs of the
  algorithm on probability spaces in one universe.
* **Best arm, min-gap**: `IsBestArm 𝒳 θ T x` (maximizer of `⟪·, θ̄_T⟫` over `𝒳`), `MinGapGE` (some
  arm beats every other vertex by `Δ`; for `Δ > 0` it is the unique best arm). The error event of
  the lower bounds is "the output is not a best arm", of Theorem 2 "the output is not `x⋆`".
* **Vertices and adjacency**: vertices = exposed points of `conv 𝒳`, adjacent = distinct vertices
  whose segment is an exposed subset of `conv 𝒳` (Definition 1; for finite `𝒳` exposed and extreme
  points coincide, and the paper's Eq. (adjacentdef) is the characterization by a direction `w`).
* **Designs**: finitely supported weights on `𝒳` (`IsDesign`), `designMatrix w = ∑ w_x x xᵀ`. The
  minima over designs defining `H_Adjacent` and Proposition 1 are over designs with positive
  definite design matrix (`PosDefDesign`), avoiding pseudo-inverses; `optValue` (Lemma 3) is over
  all designs, as in the paper. Both are `⨅`/`⨆` in `ℝ` over subtypes.
* **Algorithm 1**: `adjacentBAI x` for an allocation `x : Fin T → 𝒳`, with the guarantee of the
  rounding procedure as the hypothesis `IsAdjacentRounding 𝒳 x` (the rounding procedure itself is
  not formalized: Eq. (roundingerror) is all the proof uses); random order
  `Algorithm.randomOrder x`; least-squares estimator `lsEstimator x` from the history of the `T`
  rounds; output `recommend x`, an argmax with a fixed tie-breaking.
* **Lemma 9**: the permutation is `PMF.uniformOfFintype (Equiv.Perm (Fin T))`, the statistic a
  function of the permutation, on the discrete σ-algebra of `Equiv.Perm (Fin T)`.

## 3. Corrections to the statements

Checked against the paper and the LMLPapers statements; the statements in this repository are the
corrected ones (frozen by the comparator challenges).

* **Lemma 5** (`hasSubgaussianMGF_lsEstimator`) needs `‖x_t‖ ≤ 1` and `‖θ_t‖ ≤ 1` (the assumptions
  of Theorem 2, used by the paper's proof through Lemma 9 with `B = M = 1` but missing from its
  statement and from LMLPapers). Without them it is false: `d = 1`, `T = 2`, `x = (1, 2)`,
  `θ = (-10, 10)`: the bias term `S` is `±(3/5)·10 z`, of variance `36 z²`, while the claimed proxy
  is `9 ‖z‖²_{A⁻¹} = 9 z² / 5`.
* **Theorem 1 and Lemma 3** need `T ≥ 1` and `𝒳` with at least two points. For `T = 0` no
  parameter sequence has min-gap `Δ > 0` (`θ̄_0 = 0`), so the existential is false. For `𝒳 = {x}`
  there are no adjacent pairs, `H_Adjacent = 0` and `f(𝒳, Δ) = 0` (Lean's `x / 0 = 0` and empty
  `⨅ = 0`), so the bound reads `1/4 ≤ max(errors)`, while every algorithm outputs the only arm,
  which is a best arm.
* **Generalizations** (hypotheses the proofs do not use, dropped): Lemma 2 for any two distinct
  arms `k ≠ k'` (the best-arm property is not used); Lemma 3 without `span 𝒳 = ℝ^d`; Lemma 4 for
  every positive definite `A` (not only design matrices); Lemma 8 for every `Δ`; Proposition 1
  without `span 𝒳 = ℝ^d`; Theorem 2 without `T ≥ d²` (it only serves to obtain the rounding
  guarantee, which is a hypothesis).
* **Lemma 6** is stated for countably many arms (finitely many in the paper), so that the
  log-likelihood ratio is jointly measurable in the arm and the reward.
* **Lemma 6, indexing (found in phase 2).** LML's `IT.filtration n` is generated by the rounds
  `0, …, n`, while `llrProcess … n` covers the rounds `0, …, n - 1`; the paper (rounds from `1`)
  has `𝓕_t` and `L_t` over the same rounds. The phase-1 statement with `L_σ` was therefore false
  (constant `σ = 0`, event `{Y_0 ∈ B}`: `ν'`- versus `ν`-probability of `B`); the statement is
  now `P_ν'(E) = E_ν[1_E exp(-L_{σ + 1})]`, the comparator challenge regenerated accordingly.

## 4. Proof routes

### Polytope facts (Part II, `prereq_polytope`)

* `vertices_subset`: for finite `𝒳`, `vertices 𝒳 ⊆ 𝒳` (exposed ⇒ extreme,
  `extremePoints_convexHull_subset`); `vertices 𝒳` is finite.
* `exists_strict_expose`: a vertex `x` has `w` with `⟪y, w⟫ < ⟪x, w⟫` for all `y ∈ 𝒳 ∖ {x}`;
  conversely such an `x ∈ 𝒳` is a vertex. A maximizer of `⟪·, θ⟫` over `𝒳` that is strictly
  better than all other points is a vertex.
* `isAdjacent_iff`: for finite `𝒳` and distinct vertices, adjacency ⟺ `∃ w, ⟪x, w⟫ = ⟪x', w⟫`
  and `⟪y, w⟫ < ⟪x, w⟫` for every `y ∈ 𝒳 ∖ [x, x']` — the paper's Eq. (adjacentdef). The vertices
  lying in the segment `[x, x']` are `x` and `x'` (extreme points).
* **Lemma 1 (local optimality ⇒ global optimality)**, `exists_pos_inner_iff`. Backward: adjacent
  vertices are in `𝒳`. Forward (the paper cites Ziegler's Lemma 3.6, the cone
  `conv 𝒳 ⊆ x + cone{z - x : z ∈ ℐ^x}`, which is not in Mathlib), a direct argument (as
  formalized; the induction on `card 𝒳` planned first is not needed): let `w` strictly expose `x`
  and write every other point as `y = x + d_y a_y`, `d_y = ⟪x - y, w⟫ > 0`, `⟪a_y, w⟫ = -1`. A
  vertex `b` of the finite set `{a_y}` maximizing `⟪·, θ⟫` is strictly exposed by some `ψ`; then
  `φ = ψ + ⟪b, ψ⟫ w` is maximized over `𝒳` exactly at `x` and on the ray `x + ℝ₊ b`, and the
  farthest point `z` of `𝒳` on that ray is a vertex (lexicographic maximizer) adjacent to `x`
  (`isAdjacent_iff_exists_inner`) with `⟪z - x, θ⟫ = d_z ⟪b, θ⟫ > 0`.
  Corollaries: the `≥` version (`∃ y ∈ 𝒳, y ≠ x, ⟪y - x, θ⟫ ≥ 0` ⇒ `∃ z ∈ ℐ^x, ⟪z - x, θ⟫ ≥ 0`,
  by perturbing `θ` to `θ + ε (y - x)` and finiteness of `ℐ^x`), used for the ties of Theorem 2;
  `adjacentTo_nonempty` (a vertex of a set with two points has a neighbour).
* **Cone form** (for Lemma 10): for `x⋆` the unique maximizer of `θ` and `x ∈ 𝒳 ∖ {x⋆}`,
  `u_x := (x⋆ - x) / ⟪x⋆ - x, θ⟫ ∈ conv {u_z : z ∈ ℐ^{x⋆}}`. Otherwise separate the point from the
  compact convex hull (`geometric_hahn_banach_point_compact`-type), shift the functional by a
  multiple of `θ` (all `u` lie in `{⟪·, θ⟫ = 1}`) to get `ψ` with `⟪z - x⋆, ψ⟫ ≤ 0` on `ℐ^{x⋆}` and
  `⟪x - x⋆, ψ⟫ > 0`, contradicting Lemma 1.

### Lower bound (Part I, `lower_bound`; Part II, `prereq_information`)

* **Lemma 2**: Bretagnolle–Huber `P(E) + P'(Eᶜ) ≥ ½ exp(-KL(P_out, P'_out))` with
  `E = {out ≠ k}` and `Eᶜ ⊆ {out ≠ k'}` (`k ≠ k'`), hence `max ≥ ¼ exp(-KL)`; data processing
  `KL(P_out, P'_out) ≤ KL(history of T rounds)` (fixed budget); chain rule for the history of a
  non-stationary bandit, `KL = ∑_{t<T} ∑_a P(X_t = a) KL(ν_{t,a} ‖ ν'_{t,a})` (LML's
  `IsAlgEnvSeq.klDiv_map_history_stepKernel` with the step kernels of `Environment.banditSeq`).
  LMLPapers has Bretagnolle–Huber (`ForMathlib/InformationTheory/KullbackLeibler/BretagnolleHuber`),
  the Gaussian KL and the data-processing step for identification algorithms
  (`Identification/ChangeOfMeasure`: `IsRun.klDiv_map_out_le`); copy them. The paper's route
  through Lemma 6 and Kaufmann et al.'s Lemma 19 is not needed.
* **Lemma 6**: for `E ∈ 𝓕_n`, by induction on `n` through the Ionescu-Tulcea construction
  (`trajMeasure` restricted to the first `n + 1` rounds is a composition of kernels; on round
  `n + 1` the density of `ν'_{n,a}` w.r.t. `ν_{n,a}` is `exp(-llr)` a.e., mutual absolute
  continuity); for `E ∈ 𝓕_σ`, decompose `E = ⋃_n E ∩ {σ = n}` (σ finite).
* **Lemma 3** (construction differing from the paper's, see below). Given the algorithm, let
  `λ_x = (1/T) ∑_{t<T} P_0(X_t = x)` where `P_0` is a run against `θ ≡ 0` (a design). Choose the
  pair `(x, x') ∈ 𝒴` minimizing `pairValue(A(λ))` and a feasible `(θ̃, ṽ)` with
  `ṽᵀA(λ)ṽ < 2 f(𝒳, Δ)` (possible since `pairValue(A(λ)) ≤ f(𝒳, Δ)` and `f(𝒳, Δ) > 0`, no
  attainment of the inner minimum needed). Instances:
  `θ_t = 0, θ'_t = ṽ` for `t < T - 1`; `θ_{T-1} = T θ̃`, `θ'_{T-1} = T θ̃ + ṽ`.
  Then `θ̄ = θ̃`, `θ̄' = θ̃ + ṽ` (feasibility gives `MinGapGE` for both, with best arms `x ≠ x'`), and
  the law of `X_t` for `t ≤ T - 1` under `θ` only depends on `θ_0, …, θ_{T-2} = 0`, so it is that
  under `P_0` (lemma: runs against environments agreeing before round `t` give the same law to the
  first `t` actions). Lemma 2 with the Gaussian KL `⟪x, ṽ⟫²/2` gives `KL = (T/2) ṽᵀA(λ)ṽ ≤ T f`.
  The paper splits the horizon in two halves (`θ_t = 0` in the first, `θ_t = θ'_t` in the second,
  "without loss of generality `T` even"), which gives `KL = T ṽᵀA(λ)ṽ` with no slack: the bound
  `exp(-T f)` then needs the inner minimum to be attained (a Frank–Wolfe argument) and fails as
  written for `T = 1` (the first half is the whole horizon, `θ̄ = 0`). The construction above has a
  factor `2` of slack and works for every `T ≥ 1`.
  `f(𝒳, Δ) > 0`: for the uniform design `A_u`, every feasible `v` has
  `2Δ ≤ ⟪x' - x, v⟫` (Lemma 7's first step) with `x' - x = ∑ c_y y`, so
  `vᵀ A_u v ≥ 4Δ² / (|𝒳| ‖c‖²) > 0`; minimum over the finitely many pairs.
  `⨆` over designs is bounded above (a fixed feasible `v` per pair and `A(λ) ≤ max ‖x‖² I`).
* **Lemma 7**: `2Δ ≤ ⟪x' - x, v⟫` by adding the constraints at `y = x'` and `y = x`; Cauchy–Schwarz
  `⟪z, v⟫² ≤ ‖z‖²_{A⁻¹} ‖v‖²_A` (positive definite `A`, through `CFC.sqrt A`); the feasible set is
  nonempty (strictly exposing directions of `x` and `x'`, scaled), and the values are `≥ 0`.
* **Lemma 8**: the paper's explicit point, `θ = Δ A⁻¹(x - x')/‖x - x'‖²_{A⁻¹} + α w`,
  `v = -2Δ A⁻¹(x - x')/‖x - x'‖²_{A⁻¹}`, `w` from `isAdjacent_iff`, `α` large. The feasible `v` for
  an adjacent pair are exactly the half-space `⟪x' - x, v⟫ ≥ 2Δ` (the same construction with
  `θ = -v/2 + α w`), which is used in Theorem 1.
* **Lemma 4** = Lemmas 7 and 8.
* **Theorem 1** from Lemma 3: `f(𝒳, Δ) ≤ 4Δ² / adjDesignValue`. For a design `λ` and `ε > 0`,
  `A_ε = (A(λ) + ε A_u)/(1 + ε)` is a positive definite design matrix (`A_u` the uniform design,
  positive definite since `𝒳` spans); `pairValue` is monotone and positively homogeneous in `A`, so
  `min_{𝒴} pairValue(A(λ)) ≤ min_{ℐ} pairValue(A(λ)) ≤ (1 + ε) min_{ℐ} pairValue(A_ε)
  = (1 + ε) 4Δ² / adjValue(A_ε) ≤ (1 + ε) 4Δ² / adjDesignValue` (Lemma 4); let `ε → 0`.
  `adjDesignValue > 0`: `A(λ) ≤ R² I` with `R = max ‖x‖`, so `‖z‖²_{A(λ)⁻¹} ≥ ‖z‖²/R²`, and an
  adjacent pair exists (`adjacentTo_nonempty`).

### Upper bound (Part I, `upper_bound`; Part II, `prereq_concentration`)

* **Lemma 9** (sampling without replacement), by induction on `T` rather than the paper's Doob
  martingale: `Equiv.Perm.decomposeFin` splits a uniform permutation of `Fin (n + 1)` into a
  uniform first value and an independent uniform permutation of the rest. General statement: for
  `a : Fin n → E` and values `g : Fin n → E` with `‖g k‖ ≤ M`, the variable
  `∑_s ⟪a_s, g_{π s} - ḡ⟫` is sub-Gaussian with proxy `4M² ∑_{s < n-1} ‖d_s‖²`,
  `d_s = a_s - (1/(n - 1 - s)) ∑_{s' > s} a_{s'}`. Step: the variable is
  `⟪d_0, g_{π 0} - ḡ⟫ + (the same statistic for the remaining positions and values)`, the first
  term centered and in `[-2M‖d_0‖, 2M‖d_0‖]` (Hoeffding's lemma,
  `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`), the second sub-Gaussian conditionally on
  `π 0` by induction. Then `∑_s ‖d_s‖² ≤ 2 ∑_s ‖a_s‖²` (the columns of the paper's matrix `D` are
  orthogonal with squared norms `1 + 1/(T - s) ≤ 2`: Bessel's inequality coordinatewise), and
  `‖a_t‖ = |⟪z, A⁻¹ x_t⟫| ‖x_t‖ ≤ B |⟪z, A⁻¹ x_t⟫|`, `∑_t ⟪z, A⁻¹ x_t⟫² = ‖z‖²_{A⁻¹}`.
  *As formalized:* the induction carries the proxy `8M² ∑_s ‖a_s - ā‖²` through the Helmert
  identity (`sum_norm_sub_mean_sq_succ`) instead of `4M² ∑ ‖d_s‖²` and the orthogonal-column bound;
  `∑ ‖a_s - ā‖² ≤ ∑ ‖a_s‖²` gives the same constant. The spanning hypothesis is not used (for a
  singular matrix, `A⁻¹ = 0` in Lean and both sides vanish).
* **Lemma 5**: under a run of `adjacentBAI`, the actions are `X_t = x_{π t}` for a uniform
  permutation `π` independent of the noise `ε_t = Y_t - ⟪X_t, θ_t⟫`, the `ε_t` independent with
  laws `ξ t` (explicit model + uniqueness of the law of a run, `isAlgEnvSeq_unique`). Then
  `⟪z, θ̂ - θ̄⟫ = S(π⁻¹) + η` with `S` the statistic of Lemma 9 (`B = M = 1`, proxy `8‖z‖²_{A⁻¹}`)
  and `η = ∑_t ⟪z, A⁻¹ X_t⟫ ε_t`, conditionally on `π` sub-Gaussian with proxy
  `∑_t ⟪z, A⁻¹ x_t⟫² = ‖z‖²_{A⁻¹}`; sum of proxies `9 ‖z‖²_{A⁻¹}`.
  *As formalized:* on the explicit product model (uniform permutation `×` `Measure.infinitePi ξ`,
  `Bandits.Linear.isAlgEnvSeqUntil_randomOrder_prod_infinitePi`), transferred to every run by
  uniqueness of the law of a run; the noise term through `HasSubgaussianMGF.add_prod` (Fubini),
  without conditional sub-Gaussianity.
* **Theorem 2**: the `MinGapGE` arm is the best arm `x⋆` (a vertex beating all other vertices,
  hence all of `𝒳`). `{out ≠ x⋆} ⊆ {∃ y ∈ 𝒳 ∖ {x⋆}, ⟪y - x⋆, θ̂⟫ ≥ 0}` (argmax with ties)
  `⊆ ⋃_{z ∈ ℐ^{x⋆}} {⟪z - x⋆, θ̂ - θ̄⟫ ≥ Δ}` (Lemma 1, `≥` version, and the min-gap); union bound,
  sub-Gaussian tail (Lemma 5) `exp(-Δ² / (18 ‖z - x⋆‖²_{A⁻¹}))`; rounding guarantee
  `‖z - x⋆‖²_{A⁻¹} = ‖z - x⋆‖²_{(A/T)⁻¹} / T ≤ 2 adjDesignValue / T`. When `adjDesignValue = 0`,
  `𝒳` has no adjacent pair, `ℐ^{x⋆} = ∅` and `𝒳 = {x⋆}`.

### Stationary complexity (Part I, `stationary`)

* **Lemma 10**: `ratio(y) = ‖u_y‖²_M` with `u_y = (x⋆ - y)/⟪x⋆ - y, θ⟫`; cone form above;
  `v ↦ ‖v‖²_M` is convex, so its value at a point of the convex hull is at most its value at one
  of the generating points (`ConvexOn.exists_ge_of_mem_convexHull`); `⨆` over the finite set
  `ℐ^{x⋆}` is bounded above.
* **Proposition 1**: for each design, the inner suprema are equal (`≤` by Lemma 10, `≥` since
  `ℐ^{x⋆} ⊆ 𝒳 ∖ {x⋆}`; both are `0` when `𝒳 = {x⋆}`); `iInf_congr`.

## 5. Blueprint chapters

Part I (the paper): `setting.tex` (Section 2, Definitions 1–2, designs, `H_Adjacent`, Lemma 1),
`lower_bound.tex` (Lemmas 2, 3, 4, 6, 7, 8, Theorem 1), `upper_bound.tex` (Algorithm 1, Lemmas 5,
9, Theorem 2), `stationary.tex` (Lemma 10, Proposition 1).
Part II (prerequisites): `prereq_polytope.tex` (vertices, adjacency, local-to-global optimality,
cone form), `prereq_information.tex` (Bretagnolle–Huber, Gaussian KL, chain rule for non-stationary
bandits, data processing), `prereq_concentration.tex` (Hoeffding's lemma, sampling without
replacement, conditional sub-Gaussianity of weighted noise sums).
