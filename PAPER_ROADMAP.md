# Paper roadmap: On the Complexity of Best-Arm Identification in Non-Stationary Linear Bandits

Paper: RemyDegenne/MaynardZhang2026Complexity · LMLExplore afd365492580 · LMLRoadmaps d01bdd6b89ce · Refreshed 2026-11-09

## Items

| Id | Item | Tag | Link | Status | Files |
|---|---|---|---|---|---|
| R1 | Vertices and edges of the convex hull of a finite set, the cone property and the adjacency lemma | staged | S1 | proved | `ForLMLExplore/Analysis/Convex/Adjacent.lean`, `ForLMLExplore/Analysis/Convex/Vertices.lean` |
| R2 | Designs on a set of arms and their design matrices, Gram matrices and least squares for finitely many points | exists | `LMLExplore.designOperator` | – | `ForLMLExplore/Analysis/InnerProductSpace/Design.lean`, `ForLMLExplore/Analysis/InnerProductSpace/DesignMatrix.lean`, `ForLMLExplore/Analysis/Matrix/SchurComplement.lean`, `ForLMLExplore/Analysis/Convex/CompactHull.lean` |
| R3 | Squared Mahalanobis norm of a matrix, with the Loewner-order, square-root and measurability lemmas it uses | exists | `ContinuousLinearMap.IsPositive.abs_inner_le_sqrt_mul_sqrt_ringInverse` | – | `ForLMLExplore/Analysis/InnerProductSpace/Mahalanobis.lean`, `ForLMLExplore/Analysis/Matrix/Order.lean`, `ForLMLExplore/Analysis/Matrix/MeasurableSpace.lean`, `ForLMLExplore/Analysis/CStarAlgebra/Matrix.lean` |
| R4 | Identification algorithms from stopping rules, their runs and correctness, fixed-budget and fixed-design algorithms | exists | `LMLExplore.Identification.fixedBudget` | – | `ForLMLExplore/Identification/Basic.lean`, `ForLMLExplore/Identification/PAC.lean`, `ForLMLExplore/Identification/FixedBudget.lean`, `ForLMLExplore/SequentialLearning/Algorithms/OfSeq.lean` |
| R5 | Data processing for the output of an identification algorithm run in two environments | target | Identification 2.1 | proved | `ForLMLExplore/Identification/ChangeOfMeasure.lean` |
| R6 | Bretagnolle–Huber inequality | exists | `LMLExplore.exp_neg_klDiv_div_two_le` | – | `ForLMLExplore/InformationTheory/KullbackLeibler/BretagnolleHuber.lean` |
| R7 | Densities of real Gaussian laws and the divergence between them | exists | `LMLExplore.klDiv_gaussianReal_gaussianReal_same_var` | – | `ForLMLExplore/Probability/Distributions/Gaussian/Real.lean`, `ForLMLExplore/InformationTheory/KullbackLeibler/Gaussian.lean` |
| R8 | Divergence decomposition for non-stationary bandits (`Environment.banditSeq`) | staged | S2 | proved | `ForLMLExplore/SequentialLearning/DivergenceDecomposition.lean` |
| R9 | Runs against environments that agree before a round have the same history law | refactor | `Learning.stoppedHistMeasure_congr` | proved | `ForLMLExplore/SequentialLearning/AgreeingEnvironments.lean` |
| R10 | Change of environment with densities, and the likelihood-ratio identity at a stopping time for non-stationary bandits (`llrProcess`) | staged | S3 | proved | `ForLMLExplore/SequentialLearning/EnvironmentDensity.lean`, `ForLMLExplore/SequentialLearning/Algorithm.lean`, `ForLMLExplore/Bandits/ChangeOfMeasure.lean`, `ForLMLExplore/Bandits/Nonstationary.lean` |
| R11 | Linear reward kernels and environments with any noise law | refactor | `LMLExplore.Bandits.gaussianLinearKernel` | proved | `ForLMLExplore/Bandits/LinearBandit/Basic.lean`, `ForLMLExplore/Probability/Kernel/Composition/Prod.lean` |
| R12 | Markov kernels from functions on a countable space | exists | `ProbabilityTheory.Kernel.isMarkovKernel_ofFunOfCountable` | – | `ForLMLExplore/Probability/Kernel/Basic.lean` |
| R13 | Independence of a coordinate of `Measure.infinitePi` from the previous ones | exists | `TauCeti.Probability.indepFun_domRestrict_infinitePi` | – | `ForLMLExplore/Probability/Independence/InfinitePi.lean` |
| R14 | Conditional laws with a given kernel: images, conditioning on an uninformative variable, countable spaces | staged | S4 | proved | `ForLMLExplore/Probability/HasCondDistrib.lean`, `ForLMLExplore/Probability/Kernel/Composition/MeasureCompProd.lean` |
| R15 | An allocation played in uniformly random order (`Algorithm.randomOrder`) and the law of its actions | staged | S5 | proved | `ForLMLExplore/SequentialLearning/Algorithms/RandomOrder.lean`, `ForLMLExplore/SequentialLearning/Algorithms/RandomOrderLaw.lean` |
| R16 | Explicit model of the runs of an algorithm that reads only the past actions, against a non-stationary bandit with additive noise | staged | S6 | proved | `ForLMLExplore/Bandits/LinearBandit/ActionModel.lean` |
| R17 | Sub-Gaussian concentration of linear permutation statistics (sampling without replacement) | staged | S7 | proved | `ForLMLExplore/Probability/Moments/SamplingWithoutReplacement.lean`, `ForLMLExplore/Probability/Moments/SubGaussian.lean`, `ForLMLExplore/Probability/Distributions/Uniform.lean`, `ForLMLExplore/MeasureTheory/MeasurableSpace/Instances.lean` |
| R18 | The non-stationary linear bandit `nonstationaryLinearEnv` on an arm set | paper | | proved | `ForLMLExplore/Bandits/LinearBandit/Basic.lean` |
| R19 | The setting: hindsight best arm, min-gap, `H_Adjacent`, `f(𝒳, Δ)` and Adjacent-BAI | paper | | proved | `MXJF2026/Setting.lean` |
| R20 | The inner optimization problem of the lower bound, and the bounds on `f(𝒳, Δ)` and `H_Adjacent` | paper | | proved | `MXJF2026/PairValue.lean`, `MXJF2026/Optimization.lean` |

## Notes

- R1: the port takes the generality of S1, continuous linear functionals on a locally convex space
  in place of a complete real inner product space, with the inner-product forms as corollaries.
  `Set.mem_convexHull_setOf_inner_eq` follows from Tau Ceti's `IsExtreme.convexHull_inter_subset`
  and Mathlib's `IsExposed.isExtreme`; the port derives it from them.
- R2: LMLExplore has the operator form. `LMLExplore.designOperator` on `StdSimplex ℝ E` with
  `isPositive_designOperator`, `inner_designOperator_apply_self`,
  `mem_convexHull_image_rankOne_iff`, `exists_design_isUnit_designOperator` and
  `designOperator_map` (`Analysis/InnerProductSpace/OptimalDesign.lean`); `LMLExplore.designOp`
  for Gram operators; `sum_inner_moorePenroseInverse_designOp_sq` and
  `inner_leastSquaresEstimate_sub_eq_sum` for least squares (`LeastSquares.lean`).
  `Matrix.det_add_vecMulVec` is Mathlib's `Matrix.det_add_replicateCol_mul_replicateRow` with
  `Matrix.vecMulVec_eq`. `IsCompact.convexHull` has the same full name as LMLExplore's, which
  takes the field explicitly (the two files cannot be imported together; use `hs.convexHull ℝ`).
  The frozen headline statements use the matrix forms `designMatrix` and `IsDesign` on `Finsupp`
  weights: the bump keeps these definitions in the paper and re-proves their API from the operator
  lemmas through `Matrix.toEuclideanCLM`. Not used by the paper: `exists_isDesign_of_mem_designSet`
  (Carathéodory with support `d² + 1`; Bandits 8.6 asks for `d(d + 1)/2`, in the space of
  self-adjoint operators), the images of designs by linear maps, `gram`, `regGram` and
  `trace_le_of_mem_designSet`.
- R3: LMLExplore writes weighted norms of operators as `⟪v, V v⟫` and `⟪v, Ring.inverse V v⟫`,
  with the Cauchy–Schwarz bounds `ContinuousLinearMap.IsPositive.abs_inner_le_sqrt_mul_sqrt_ringInverse`
  and `IsPositive.sq_inner_apply_le` (`Analysis/InnerProductSpace/Positive.lean`); matrix inversion
  is measurable by Tau Ceti's `TauCeti.measurable_matrix_inv`. As for R2, the frozen statements use
  `mahalanobisSq` (through `adjValue`), which the bump keeps in the paper. Not used by the paper:
  `pinvMahalanobisSq` (its port would be the form `‖y‖²_{V⁺}` with values in `[0, ∞]` that
  Identification 3.6 asks for), the antitonicity of inversion `Matrix.PosDef.inv_le_inv` and its
  variants (for `RCLike` matrices; Mathlib's `CStarAlgebra.inv_le_inv` covers complex matrices
  only), and `Matrix.span_image_toEuclideanCLM_eq_top`.
- R4: same definitions in LMLExplore, renamed. `ofStop`, `outputAt`, `runMeasure` and
  `isRun_runMeasure` are in `LMLExplore.Identification` (`A.outputAt n` becomes `outputAt A n`,
  `outputAt_def` becomes `outputAt_eq_comap`); `histOutputMeasure`, `StopsAS`, `IsDeltaPAC` and
  `IsDeltaCorrect` are in `LMLExplore/Identification/Correctness.lean`; `IsFixedBudget` and
  `fixedBudget` are in `LMLExplore.Identification`, `outputMeasure_of_isFixedBudget_zero` becomes
  `outputMeasure_eq_of_isFixedBudget_zero`, `Algorithm.IsFixedDesign` becomes
  `LMLExplore.Identification.IsFixedDesign`. `Learning.IsAlgEnvSeq.comp_hasLaw`
  (`SequentialLearning/Algorithm.lean`) and `ProbabilityTheory.hasCondDistrib_snd_compProd_comap`
  (`Probability/HasCondDistrib.lean`, same full name) are LMLExplore's. Adjacent-BAI
  (`adjacentBAI`, in the closure of Theorem 2) is built with `fixedBudget`, so the bump only renames
  it. Not in LMLExplore and not used by the paper: `Algorithm.thenRepeat` and `IdentAlg.thenCommit`
  (`SequentialLearning/Algorithms/ThenRepeat.lean`, imported by `FixedBudget.lean`),
  `IsRun.map_out_eq_of_isFixedBudget_zero` and `IsAlgEnvSeqUntil.comp_hasLaw`.
- R5: Identification 2.1 asks, in its second bullet, for the bound of its first bullet for the
  joint law of the stopped history and the output when the output kernel is common, for any two
  algorithm–environment pairs. The port states, for any identification algorithm and any two
  environments, `klDiv (histOutputMeasure A env) (histOutputMeasure A env')` equal to the
  divergence of the stopped histories (Mathlib's `klDiv_compProd_left`) and the output form by data
  processing, then the bound by the chain rule of the first bullet when it is merged. The paper's
  fixed-budget statements `IsFixedBudget.klDiv_outputMeasure_le` and `IsRun.klDiv_map_out_le`
  (used by Lemma 2) become corollaries. LMLExplore's
  `LMLExplore.Identification.klDiv_histOutputMeasure_le` covers one algorithm against two
  stationary bandits only.
- R6: identical statements in `LMLExplore/InformationTheory/KullbackLeibler/BretagnolleHuber.lean`
  (Bandits 4.2).
- R7: every lemma is in LMLExplore's `Probability/Distributions/Gaussian/Real.lean` and
  `InformationTheory/KullbackLeibler/Gaussian.lean` (`rnDeriv_gaussianReal_gaussianReal` holds
  there almost everywhere for the Lebesgue measure). The bump keeps `klDiv_gaussianReal_one`
  (Lemma 3; the same-variance lemma at `v = 1`) in the paper; `llr_gaussianReal_same_var` is not
  used.
- R8: LML has the chain rule for any two pairs at a fixed horizon
  (`IsAlgEnvSeq.klDiv_map_history_stepKernel`) and its form for stationary bandits
  (`klDiv_map_history_bandit`); this item is its form for `Environment.banditSeq`. Non-stationary
  bandits are outside the Bandits roadmap (Scope and dependencies), and no Identification item has
  round-dependent kernels.
- R9: LMLExplore proves that runs of two pairs whose step kernels agree before a stopping rule have
  the same law of the history, in the private `measure_history_preimage_eq` of
  `SequentialLearning/StoppedHistory.lean`, and states it only on the canonical space
  (`stoppedHistMeasure_congr`). The refactor states it for runs on any probability space, with
  `stoppedHistMeasure_congr` as its canonical-space case, and adds `IsAlgEnvSeqUntil.of_env_eq` and
  the fixed-horizon corollaries `IsAlgEnvSeq.identDistrib_history_of_env_eq` and
  `IsAlgEnvSeq.identDistrib_action_of_env_eq` (used by Lemma 3), with LML's
  `isAlgEnvSeqUntil_unique`.
- R10: not in the dependencies: LML's `IsAlgEnvSeq.hasLaw_history_withDensity` changes the
  algorithm in a fixed environment. The three `map_history_succ` lemmas of
  `SequentialLearning/Algorithm.lean` go with this item (LML inlines them in its proofs). Lemma 6
  (`trajMeasure_eq_lintegral_exp_neg_llrProcess`) is stated with `Bandits.llrProcess`, which the
  bump keeps in the paper until S3 is ported. Not used by the paper: `Bandits.cumMean`,
  `Bandits.IsBestArm` and `Bandits/BestArm.lean`, which `Nonstationary.lean` imports only for them
  (`bestMeanArm` is LML's `argmax`, `HasUniqueBest` is membership in the models of LMLExplore's
  `baiTask`).
- R11: LMLExplore's `gaussianLinearKernel φ θ σ2` and `gaussianLinearEnv`, with contextual features
  `φ : 𝓞 → 𝓐 → E`, have Gaussian noise only; the paper needs any noise law (σ²-sub-Gaussian in
  Theorem 2). The refactor defines the kernel `a ↦ ξ.map (⟪θ, φ a⟫ + ·)` for a feature map
  `φ : 𝓐 → E` and a noise law `ξ` (the paper's `featureKernel`; the contextual kernel is the case
  of `𝓞 × 𝓐` with `Function.uncurry φ`, as LML's `Environment.bandit` and `banditSeq` take
  non-contextual kernels), its environment and its `IsSubgaussianLinearEnv` lemma for
  σ²-sub-Gaussian noise, keeping the order `⟪θ, ·⟫`, and restates the Gaussian kernel and
  environment as the case `ξ = gaussianReal 0 σ2`. `Kernel.map_id_prod_const_apply`
  (`Probability/Kernel/Composition/Prod.lean`) goes with it. Not used by the paper, in
  `Bandits/LinearBandit/Basic.lean`: `IsSubgaussianLinearEnv` (LMLExplore's
  `LMLExplore.Bandits.IsSubgaussianLinearEnv` with `𝓞 = Unit`), `simpleRegret` and `pseudoRegret`
  (LMLExplore's `linearRegret`) with the support function they use
  (`Analysis/InnerProductSpace/SupportFn.lean`), the linear `IsPAC` (LML's `IdentAlg.IsPAC`;
  Identification 9.1 asks for no separate definitions) and `IsLinMaxSelection`.
- R12: identical to LMLExplore's `Probability/Kernel/Basic.lean`, with the same full name (the two
  files cannot be imported together).
- R13: `indepFun_eval_restrict_infinitePi` is Tau Ceti's lemma with `S = {n}` and `T = Iio n`,
  composed with measurable maps (`IndepFun.comp`); used by R16.
- R14: R15 and R16 use `HasCondDistrib.map_of_forall_map_eq` (with
  `Measure.map_compProd_of_forall_map_eq`), `HasCondDistrib.prodMk_right_of_comap_fst` (with
  `Measure.compProd_comap_fst_comm`) and `hasCondDistrib_of_countable`. Already in the
  dependencies: `hasCondDistrib_snd_compProd_comap` (see R4), `Measure.map_prodMk_compProd_comap`
  (LML's `Measure.map_compProd_comap`), `lintegral_prodMk` (LMLExplore's
  `HasCondDistrib.lintegral_comp_prodMk_eq_lintegral_lintegral`) and
  `Measure.restrict_compProd_prod_univ` (Tau Ceti's `Measure.compProd_restrict_left`). Not used by
  the paper: the other lemmas of `HasCondDistrib.lean` and `MeasureCompProd.lean`, and
  `Probability/Kernel/Composition/CompProd.lean`.
- R15: no roadmap item plays allocations in random order: Identification 8.3 and 8.4 use static
  allocations, and 9.3 asks for rounding. The instance `isProbabilityMeasure_ofMultiset`
  (`Probability/Distributions/Uniform.lean`) and the discrete measurable space on `Equiv.Perm α`
  (`MeasureTheory/MeasurableSpace/Instances.lean`, listed with R17) go with it; the port restricts
  that instance to `[Finite α]`, as Mathlib puts the discrete σ-algebra only on countable types.
  `Algorithm.FactorsThrough` (`SequentialLearning/FactorsThrough.lean`) is used only by
  `factorsThrough_randomOrder`, which nothing uses (LML has the special case
  `Algorithm.IsMarkov`).
- R16: stated for `nonstationaryLinearEnv` (R18); the port states it for every oblivious
  environment whose kernels are images of noise laws (S6). Lemma 5 uses it through
  `isAlgEnvSeqUntil_randomOrder_prod_infinitePi`. LMLExplore's `IsFixedDesign` and
  `Algorithm.ofSeq` cover deterministic sequences of actions only.
- R17: the main result is `ProbabilityTheory.hasSubgaussianMGF_sum_inner_perm`, with the Helmert
  identities `sum_norm_sub_mean_sq` and `sum_norm_sub_mean_sq_succ`; `HasSubgaussianMGF.add_prod`
  (the product-measure case of Mathlib's `Kernel.HasSubgaussianMGF.add_compProd`) and
  `uniformOfFinset_univ_prod` go with it. Tau Ceti has the law `sampleWithoutReplacement` and its
  comparison in total variation with sampling with replacement, but no concentration. Already in
  the dependencies: `HasSubgaussianMGF.mono` (LML, same full name), the instances and
  `map_uniformOfFinset_univ_equiv` of `Uniform.lean` (Tau Ceti's
  `TauCeti.Probability.isProbabilityMeasure_uniformOfFinset_univ` and `Equiv.map_uniformOn_univ`),
  and `uniformOfFinset_univ_setOf` (Mathlib's `uniformOfFinset_apply`); LMLExplore writes the
  uniform law on a finite type `uniformOn Set.univ`. `hasSubgaussianMGF_sum_mul_infinitePi`, a
  short combination of Mathlib lemmas used by Lemma 5 only, stays in the paper.
- R18: non-stationary bandits are outside the Bandits roadmap (Scope and dependencies).
  `nonstationaryLinearEnv 𝒳 θ ξ` is LML's `Environment.banditSeq` of the kernels of R11, with the
  inclusion of `𝒳` as feature map; it is the linear instance of S2, S3 and S6 if they become
  targets.

## Proposed targets

### S1. Vertices and edges of polytopes

For a finite set `X` of a real locally convex Hausdorff space, define the vertices of `conv X`, its
exposed points (`Set.vertices`), and its edges, the exposed segments `[x, x']` between two distinct
vertices (`Set.IsAdjacent`, with `Set.adjacentTo X x` the vertices adjacent to `x`). Prove that the
extreme points of `conv X` are exposed and belong to `X`, and that `conv X` is the convex hull of
its vertices; that the maximizers over `conv X` of a continuous linear functional are the convex
hull of its maximizers in `X`; that a point of `X` is a vertex if and only if some functional is
maximized over `X` at that point only; and that two vertices are adjacent if and only if some
functional is maximized over `X` exactly at them. Prove the cone property: for a vertex `x`, `X - x`
lies in the convex cone generated by `adjacentTo X x - x` [Zie95, Lemma 3.6]. Deduce the local
optimality principle of the simplex method: a vertex that no adjacent vertex beats for a functional
maximizes it over `X`, so that a vertex beaten by some point of `X` is beaten by an adjacent vertex;
and deduce that the graph of the edges is connected. Give the forms with inner products in a real
inner product space. References: [Zie95] G. M. Ziegler, *Lectures on Polytopes*, Springer, 1995,
Chapters 2–3; B. Grünbaum, *Convex Polytopes*, 2nd ed., Springer, 2003, Chapter 3; A. Schrijver,
*Theory of Linear and Integer Programming*, Wiley, 1986, Chapter 8.

### S2. Divergence decomposition for non-stationary bandits

For an algorithm run against the oblivious environments `Environment.banditSeq ν` and
`Environment.banditSeq ν'` of two sequences of kernels `ν ν' : ℕ → Kernel 𝓐 𝓨`, on any measurable
spaces, prove that the divergence between the laws of the histories of the first `M` rounds is the
sum over `t < M` of the divergences of round `t`, in composition-product form; that it is
`∑_{t<M} E[KL(ν t (A_t) ‖ ν' t (A_t))]` when `𝓨` is countably generated, and
`∑_{t<M} ∑_a P(A_t = a) KL(ν t a ‖ ν' t a)` when `𝓐` is countable. Derive it from LML's chain rule
`IsAlgEnvSeq.klDiv_map_history_stepKernel`, whose step kernels share here the observation kernels
and the policy, and derive LML's `klDiv_map_history_bandit` (stationary bandits) as the case of
constant sequences. At a stopping time `τ`, give the bound by `E[∑_{t<τ} KL(ν t (A_t) ‖ ν' t (A_t))]`
from the chain rule of Identification 2.1. References: T. Lattimore, C. Szepesvári, *Bandit
Algorithms*, Cambridge University Press, 2020, Lemma 15.1 (stationary case); A. Garivier,
P. Ménard, G. Stoltz, *Explore first, exploit next: the true shape of regret in bandit problems*,
Math. Oper. Res. 44 (2019), Section 2; O. Besbes, Y. Gur, A. Zeevi, *Stochastic multi-armed-bandit
problem with non-stationary rewards*, NeurIPS 2014.

### S3. Likelihood-ratio identity for a change of environment

For an algorithm and two environments with the same observation kernels whose feedback kernels
satisfy `env'.feedback n = (env.feedback n).withDensity ρ_n`, for measurable densities `ρ_n` of the
round (observation, action, feedback), prove that the law of the history of the first `n` rounds
under `env'` has density `∏_{s<n} ρ_s` with respect to the law under `env`; together with LML's
`IsAlgEnvSeq.hasLaw_history_withDensity` (a change of algorithm in a fixed environment), state the
same for a change of both. Prove Wald's likelihood-ratio identity: for a stopping time `τ` of the
history filtration and an event `E` of the stopped σ-algebra,
`P'(E ∩ {τ < ∞}) = E[1_{E ∩ {τ < ∞}} ∏_{s ≤ τ} ρ_s]` (rounds `0, …, τ`, as LML's filtration indexes
them), on the trajectory space and for every run of the two pairs. Instance: non-stationary bandits
`Environment.banditSeq ν` and `Environment.banditSeq ν'` whose reward laws `ν t a` and `ν' t a` are
mutually absolutely continuous, with the density `exp(-L)` for the log-likelihood-ratio process
`L_t = ∑_{s<t} log (dν_{s,A_s}/dν'_{s,A_s})(Y_s)` [KCG16, Lemma 18]. References: A. Wald,
*Sequential tests of statistical hypotheses*, Ann. Math. Statist. 16 (1945); D. Siegmund,
*Sequential Analysis*, Springer, 1985, Chapter II; [KCG16] E. Kaufmann, O. Cappé, A. Garivier, *On
the complexity of best-arm identification in multi-armed bandit models*, JMLR 17 (2016), Lemma 18.

### S4. Conditional laws with a given kernel

For LML's `HasCondDistrib Y X κ P`, with the kernel given and no standard Borel assumption, prove:
the images, `HasCondDistrib (F X Y) (G X) K P` when `K (G a) = (κ a).map (F a)` for every `a`; the
conditioning on an uninformative variable, if the conditional law of `V` given `(W, Y)` depends on
`W` only, then the conditional law of `Y` given `(W, V)` is its conditional law given `W` (the
kernel form of Mathlib's `condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight`); and, on countable
spaces, the characterization `P(X = a, Y = b) = P(X = a) κ a {b}`. With them, the measure-level
lemmas they rest on: `Measure.map_compProd_of_forall_map_eq`, a common generalization of Mathlib's
`Measure.compProd_map` and LML's `Measure.map_compProd_comap`, and `Measure.compProd_comap_fst_comm`.
References: O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Springer, 2021,
Chapter 8.

### S5. Allocations played in uniformly random order

For a finite allocation `x : Fin T → 𝓐` (a multiset of arms, for instance a rounded design), define
the algorithm that plays at each round `n < T` an arm drawn uniformly from the arms of the
allocation not yet played (sampling without replacement), and any fixed rule afterwards. For a
uniform random permutation `π` of `Fin T`, prove that the conditional law of `x (π n)` given
`x (π 0), …, x (π (n - 1))` is uniform on the remaining multiset, and deduce that in every run of the
algorithm, against any environment, the first `T` actions have the law of `(x (π t))_{t<T}`.
References: W. Hoeffding, *Probability inequalities for sums of bounded random variables*, JASA 58
(1963), Section 6; R. J. Serfling, *Probability inequalities for the sum in sampling without
replacement*, Ann. Statist. 2 (1974).

### S6. Explicit runs of algorithms that read only the past actions

For an oblivious environment `Environment.banditSeq ν` whose kernels are images of noise laws,
`ν t a = (ξ t).map (f t a)` with `f` measurable, and an algorithm whose policy at round `n` depends
only on the past actions, prove that on `(U × (ℕ → 𝓔), μ ⊗ Measure.infinitePi ξ)` the actions
`A_n = a_n(u)` and the feedback `Y_n = f n (a_n u) (ε_n)` form an `IsAlgEnvSeqUntil` sequence up to
round `N` as soon as, for `n < N`, `a_n` has under `μ` the conditional law that the policy gives to
the previous actions. Deduce with LML's `isAlgEnvSeqUntil_unique` that in every run the feedback is,
given the actions, independent with laws `ν t (A_t)`. Instances: fixed designs (`Algorithm.ofSeq`),
and allocations played in uniformly random order with the actions `x (π n)` (S5). Reference:
T. Lattimore, C. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020, Section 4.6.

### S7. Concentration for sampling without replacement

For a real inner product space `E`, vectors `g : Fin N → E` with `‖g k‖ ≤ M`, weights
`a : Fin N → E` and a uniform permutation `π` of `Fin N`, prove that `∑_s ⟪a_s, g_{π s} - ḡ⟫` is
sub-Gaussian with variance proxy `C M² ∑_s ‖a_s - ā‖²` for an explicit constant `C` (`C = 8` by
induction on `N` with the Helmert identity), for instance by Mathlib's
`HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF` along the filtration that reveals
`π 0, π 1, …`. For a real population in `[a, b]` of size `N` and a sample of size `n` drawn without
replacement (Tau Ceti's `sampleWithoutReplacement`), prove Hoeffding's comparison
`E φ(∑_{i<n} X_i) ≤ E φ(∑_{i<n} Y_i)` for continuous convex `φ` and `Y_i` drawn with replacement,
hence the sub-Gaussian bound of the centred sum with proxy `n (b - a)²/4`, and Serfling's proxy
`n (1 - (n - 1)/N) (b - a)²/4`. References: W. Hoeffding, *Probability inequalities for sums of
bounded random variables*, JASA 58 (1963), Section 6; R. J. Serfling, *Probability inequalities for
the sum in sampling without replacement*, Ann. Statist. 2 (1974); R. Bardenet, O.-A. Maillard,
*Concentration inequalities for sampling without replacement*, Bernoulli 21 (2015).
