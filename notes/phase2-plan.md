# Phase 2 plan: work packages and briefs

Every package proves the lemmas of one blueprint area against interfaces that are already stated
(with `sorry`) in the repository, so that all packages can run in parallel: a package that uses
another one's interface relies on its statement only.

Interface files (statements fixed; their owner replaces the `sorry`):

| File | Declarations | Owner |
|---|---|---|
| `MaynardZhang2026Complexity/Mathlib/Analysis/Convex/Vertices.lean` | `Set.Finite.mem_vertices_iff_exists_inner_lt`, `isAdjacent_iff_exists_inner`, `exists_mem_adjacentTo_inner_pos`, `exists_mem_adjacentTo_inner_nonneg`, `adjacentTo_nonempty`, `mem_vertices_of_forall_vertices` | P |
| `MXJF2026/Lemma1.lean`, `Lemma10.lean`, `Proposition1.lean` (frozen) | `exists_pos_inner_iff`, `ratio_le_iSup_adjacentTo`, `iInf_iSup_ratio_eq` | P |
| `MXJF2026/Optimization.lean` | `exists_pairFeasible`, `optValue_pos`, `exists_pairFeasible_lt_two_mul_optValue`, `hAdjacent_pos`, `optValue_le` | O |
| `MXJF2026/Lemma4.lean`, `Lemma7.lean`, `Lemma8.lean` (frozen) | `pairValue_eq`, `le_pairValue`, `pairValue_le` | O |
| `MXJF2026/Lemma2.lean`, `Lemma3.lean`, `Lemma6.lean`, `Theorem1.lean` (frozen) | `le_max_prob_ne`, `exists_minGapGE_le_max_error_optValue`, `trajMeasure_eq_lintegral_exp_neg_llrProcess`, `exists_minGapGE_le_max_error` | L |
| `MXJF2026/Lemma5.lean`, `Lemma9.lean`, `Theorem2.lean` (frozen) | `hasSubgaussianMGF_lsEstimator`, `hasSubgaussianMGF_sum_perm`, `prob_ne_bestArm_le` | U |

(`MXJF2026/` is `MaynardZhang2026Complexity/MXJF2026/`.)

## Rules for every package

* Read `notes/blueprint-outline.md` (sections 3 and 4: corrections and proof routes), the
  blueprint chapters of your package (`blueprint/src/chapters/*.tex`),
  `MaynardZhang2026Complexity/MXJF2026/Setting.lean` and the files you build on. Lean
  conventions: every file `module` + `public import …` + module docstring + `@[expose] public
  section`, copyright header `Rémy Degenne` (as the existing files), every declaration with a
  docstring, `lemma` (never `theorem`, except the headline results already stated), Mathlib
  naming, lines ≤ 100 chars, no `sorry` left in your files at the end.
* **Never change** the statements of the headline theorems in `MaynardZhang2026Complexity/MXJF2026/`
  (frozen by the comparator challenges), the definitions in `Setting.lean`, the definitions and
  statements of the library files from LMLPapers (`MaynardZhang2026Complexity/LeanMachineLearning/`,
  `MaynardZhang2026Complexity/Mathlib/` except `Vertices.lean`), nor the statements of the
  interface lemmas above. You replace the `sorry` of the interfaces you own; for anything else,
  add new files (or new lemmas in your own files). If an interface or headline statement looks
  false or unprovable, stop and report instead of changing it. If a hypothesis of a frozen
  headline statement ends up unused by your proof, keep it, put `@[nolint unusedArguments]` on the
  theorem (with `set_option linter.unusedVariables false in` if needed) and report it.
* Prove the general statement and derive the specialization; drop hypotheses the proof does not
  use from *new* lemmas. New library-shaped material goes to `MaynardZhang2026Complexity/Mathlib/`
  (Mathlib path and namespaces) or `MaynardZhang2026Complexity/LeanMachineLearning/` (LML path,
  namespace `Learning` or `Bandits`); paper-specific material to
  `MaynardZhang2026Complexity/MXJF2026/` (namespace `MaynardZhang2026Complexity`). State laws as
  `HasLaw`/`HasCondDistrib` rather than `Measure.map` equations. No structures bundling a function
  with its measurability: plain functions with measurability hypotheses.
* Only edit your own files and, in the blueprint, the environments of your package. Re-read a
  blueprint chapter right before editing it (other packages edit other environments of the same
  chapters). After adding a Lean file run `lake exe mk_all --lib MaynardZhang2026Complexity`
  (concurrent runs are harmless). Do not run `leanblueprint`, do not commit.
* Blueprint: add `\lean{Full.Name}` and `\leanok` to each statement the moment its declaration
  compiles, and `\leanok` inside the `proof` environment when its proof is complete (no `sorry`,
  also in what it uses from your package); keep labels unchanged; add a lemma (label, `\uses`)
  for any new intermediate step that deserves one. Run `python3 scripts/check-blueprint.py`.
* Check before reporting: `lake build MaynardZhang2026Complexity` with no warnings in your files
  other than `declaration uses 'sorry'` coming from *other* packages' interfaces,
  `lake exe runLinter MaynardZhang2026Complexity` (fix what it reports in your files),
  `grep -n sorry` on your files. Concurrent `lake build` calls in this checkout are fine.
* Look up APIs by grepping `.lake/packages/mathlib/Mathlib` and
  `.lake/packages/LeanMachineLearning/LeanMachineLearning`; test in scratch files with
  `lake env lean File.lean` in your scratchpad directory. `~/Documents/Lean/LMLPapers` has more
  library material (read-only for you): copy what you need into this repository, mapping
  `LMLPapers.LeanMachineLearning.ForMathlib.X` to `MaynardZhang2026Complexity.Mathlib.X` and
  `LMLPapers.LeanMachineLearning.X` to `MaynardZhang2026Complexity.LeanMachineLearning.X`.
* Report: what was proved (names, files), any deviation from the plan, anything left.

## P. Polytope geometry and the adjacency lemma (`prereq_polytope.tex`; `lem:adjacency`, `lem:min_gap_best_arm` in `setting.tex`; `stationary.tex`)

Prove the six interfaces of `Vertices.lean`, then the frozen `exists_pos_inner_iff` (Lemma 1,
`Set.vertices_subset` for the backward direction), `ratio_le_iSup_adjacentTo` (Lemma 10) and
`iInf_iSup_ratio_eq` (Proposition 1). Routes (blueprint `prereq_polytope.tex`, outline section 4):

* `mem_vertices_iff_exists_inner_lt`: exposed points are given by continuous linear functionals
  (`IsExposed`, `StrongDual`), represented by inner products (`InnerProductSpace.toDual`, finite
  dimension); a strict maximizer over `𝒳` is the unique maximizer over `convexHull ℝ 𝒳`.
  Also prove `convexHull ℝ 𝒳 = convexHull ℝ (vertices 𝒳)` for finite `𝒳` (remove non-vertices one
  at a time; a non-vertex `x ∈ 𝒳` lies in `convexHull (𝒳 \ {x})`, else separate it,
  `geometric_hahn_banach_point_compact`-type lemmas in `Mathlib/Analysis/LocallyConvex/Separation`).
* `isAdjacent_iff_exists_inner`: the maximizers of a linear form over `convexHull ℝ 𝒳` are the
  convex hull of its maximizers over the vertices; the vertices in a segment are its endpoints.
* `exists_mem_adjacentTo_inner_pos` and `adjacentTo_nonempty`, jointly, by strong induction on
  the cardinality of `𝒳` (blueprint `lem:local_global`): `s⋆` the largest ratio, the face `𝒳'` of
  maximizers of `θ + s⋆ w`, induction on `𝒳'` and `isAdjacent` of a face (`lem:adjacent_of_face`,
  direction `K a + b`); the case `𝒳' = 𝒳` through `adjacentTo_nonempty` (a direction `θ` in the
  span of `𝒳 - x` not parallel to the projection of `w`; the collinear case directly). You may
  restructure this induction as you see fit as long as the interface statements are unchanged.
* `exists_mem_adjacentTo_inner_nonneg`: perturb `θ` by `ε (y - x)`, finiteness of `adjacentTo`.
* `mem_vertices_of_forall_vertices`: every point is a convex combination of vertices.
* Lemma 10: the cone form (`lem:cone_form`, separation in the hyperplane `⟪·, θ⟫ = 1`, then the
  adjacency lemma), `mahalanobisSq M` convex for `M` positive definite,
  `ConvexOn.exists_ge_of_mem_convexHull`; the `⨆` over the finite `adjacentTo` is bounded.
* Proposition 1: pointwise equality of the inner suprema, `iInf_congr`.

## O. The inner optimization problem (`lower_bound.tex`: `def:opt_value` to `lem:opt_value_le`)

Prove the frozen `le_pairValue` (Lemma 7), `pairValue_le` (Lemma 8), `pairValue_eq` (Lemma 4) and
the five interfaces of `Optimization.lean`. Use P's `Set.Finite.mem_vertices_iff_exists_inner_lt`,
`isAdjacent_iff_exists_inner` and `adjacentTo_nonempty` by their statements. Routes:

* `exists_pairFeasible` (`lem:pair_feasible_nonempty`): strictly exposing directions of `x` and
  `x'`, scaled; `pairValue` is an infimum over a nonempty set, bounded below by `0` for positive
  semidefinite `A` (design matrices are positive semidefinite).
* Lemma 7: `2Δ ≤ ⟪x' - x, v⟫`, Cauchy–Schwarz for the forms of `A⁻¹` and `A` (through
  `CFC.sqrt A`, see `Mathlib/Analysis/Matrix/Order.lean` and `Mahalanobis.lean` in this repo).
* Lemma 8: the paper's explicit point (blueprint `lem:pair_value_upper`), `α` large; it holds for
  every `Δ`.
* `pairValue` monotone and positively homogeneous in `A` (`lem:pair_value_mono`).
* `optValue_pos` and `exists_pairFeasible_lt_two_mul_optValue` (`lem:opt_value_pos`): the
  supremum over designs is bounded above (a fixed feasible `v` per pair and
  `A(λ) ≤ (max ‖x‖²) I`), positive through the uniform design (blueprint), then
  `exists_lt_of_ciInf_lt` for the minimizing pair.
* `hAdjacent_pos`, `optValue_le` (`lem:opt_value_le`): `A_ε = (A(λ) + ε A_u)/(1 + ε)` is a
  positive definite design matrix of a design (`A_u` uniform design, positive definite since `𝒳`
  spans), monotonicity, Lemma 4, `ε → 0`.

## L. Lower bounds (`lower_bound.tex`: `lem:gen_lower`, `lem:change_of_measure`, `lem:actions_law_agree`, `lem:opt_lower`, `thm:lower_bound`; `prereq_information.tex`)

Prove the frozen `le_max_prob_ne` (Lemma 2), `trajMeasure_eq_lintegral_exp_neg_llrProcess`
(Lemma 6), `exists_minGapGE_le_max_error_optValue` (Lemma 3) and
`exists_minGapGE_le_max_error` (Theorem 1). Use O's `optValue_pos`,
`exists_pairFeasible_lt_two_mul_optValue`, `optValue_le`, `hAdjacent_pos` and P's
`Set.Finite.mem_vertices_of_forall_vertices` by their statements. Routes:

* Information tools: copy from LMLPapers what you need — Bretagnolle–Huber
  (`ForMathlib/InformationTheory/KullbackLeibler/BretagnolleHuber.lean`), the Gaussian divergence
  (`.../KullbackLeibler/Gaussian.lean`), the data processing for identification algorithms
  (`Identification/ChangeOfMeasure.lean`: `IsRun.klDiv_map_out_le`), and look at
  `Online/Bandit/Linear/LowerBound.lean` there (the same computation for stationary linear
  bandits). Chain rule for non-stationary bandits from LML's
  `IsAlgEnvSeq.klDiv_map_history_stepKernel` (`SequentialLearning/DivergenceDecomposition.lean`).
* Lemma 2: blueprint `lem:gen_lower` (the best-arm property is not used, only `k ≠ k'`).
* Lemma 6: induction on `n` for events of `𝓕_n` through the Ionescu-Tulcea construction of
  `trajMeasure` (LML `SequentialLearning/IonescuTulceaSpace` and related files), then the
  decomposition over `{σ = n}`.
* Lemma 3: the construction of the outline (section 4) and of the blueprint, **not** the paper's
  half split: `θ_t = 0`, `θ'_t = ṽ` for `t < T - 1`, `θ_{T-1} = T θ̃`, `θ'_{T-1} = T θ̃ + ṽ`, the
  design `λ` from a run against `θ ≡ 0` (exists: LML `trajMeasure`), the law of the actions of the
  first `T` rounds under `θ` equal to that under `0` (`lem:actions_law_agree`), Lemma 2 with the
  Gaussian divergence, exponent `(T/2) ṽᵀA(λ)ṽ < T f`. Best arms: P's
  `mem_vertices_of_forall_vertices` makes the best arms unique.
* Theorem 1: Lemma 3 and `optValue_le`, `hAdjacent_pos`.

## U. Upper bound (`upper_bound.tex`, `prereq_concentration.tex`)

Prove the frozen `hasSubgaussianMGF_sum_perm` (Lemma 9), `hasSubgaussianMGF_lsEstimator`
(Lemma 5) and `prob_ne_bestArm_le` (Theorem 2). Use P's
`Set.Finite.exists_mem_adjacentTo_inner_nonneg`, `mem_vertices_of_forall_vertices`,
`adjacentTo_nonempty` and O's `hAdjacent_pos` by their statements. Routes:

* Lemma 9: induction on `n` with `Equiv.Perm.decomposeFin` (blueprint
  `lem:sampling_without_replacement`), Hoeffding's lemma
  (`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`), the column bound
  `lem:column_bessel` (Bessel's inequality, `Orthonormal.sum_inner_products_le`, coordinatewise),
  then `B`, `M`. Put the general sampling-without-replacement statement in the library
  (Mathlib path, `Probability/Moments/` or similar).
* Lemma 5: describe the law of a run of `adjacentBAI` (blueprint `lem:run_adjacent_bai`: explicit
  model with a uniform permutation and independent noises, uniqueness of the law of a run,
  `isAlgEnvSeq_unique`; `Algorithm.randomOrder` samples without replacement through
  `multisetUniform`), decompose `⟪z, θ̂ - θ̄⟫ = S + η`, Lemma 9 for `S` (`B = M = 1`), conditional
  sub-Gaussianity of `η` (`lem:weighted_noise_subgaussian`; see also
  `HasCondSubgaussianMGF` in Mathlib and LMLPapers' `Online/Bandit/Linear/Noise.lean`).
* Theorem 2: blueprint `thm:upper_bound`; ties through `exists_mem_adjacentTo_inner_nonneg`; the
  sub-Gaussian tail bound (`HasSubgaussianMGF.measure_ge_le`); the degenerate case of a single arm;
  `IsAdjacentRounding` gives the positive definiteness of `allocMatrix x` and the span of `𝒳`.
