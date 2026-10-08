# Upstreaming candidates

Library-shaped material written in phase 2, by destination, after the review against the Mathlib
guidelines (files organized by topic: lemmas merged into the files of their topic, no conjunctions
in conclusions, an explicit `designOfWeights` instead of an existential, Mathlib's
`isSymmetric_toEuclideanLin_iff` instead of a local lemma). Paths are under
`MaynardZhang2026Complexity/`. All of it is also in `LMLPapers` (uncommitted there, 2026-10-08),
merged into the files of `LMLPapers` with the same topics; see the last section.

## Mathlib

| File | Content |
|---|---|
| `Mathlib/Analysis/Convex/Vertices.lean` | maximizers of a linear form over `conv s`; vertices as strictly exposed points; a point of maximal norm is a vertex; for finite sets: extreme points are exposed, `conv (vertices 𝒳) = conv 𝒳`, adjacency through a direction, the adjacency lemma (local optimality implies global optimality), existence of edges, the cone property, points beating all other vertices |
| `Mathlib/Analysis/InnerProductSpace/Mahalanobis.lean` (additions) | additivity in the matrix, Loewner monotonicity, `‖x‖_A² = ⟪x, A x⟫`, Cauchy–Schwarz `⟪x, y⟫² ≤ ‖x‖²_{A⁻¹} ‖y‖²_A` |
| `Mathlib/Probability/HasCondDistrib.lean` (addition) | conditional laws on countable spaces (`hasCondDistrib_of_countable`) |
| `Mathlib/Probability/Moments/SubGaussian.lean` | `HasSubgaussianMGF.mono`, sums of sub-Gaussian variables on a product space (`add_prod`), weighted sums of the coordinates of `Measure.infinitePi` |
| `Mathlib/Probability/Moments/SamplingWithoutReplacement.lean` | the centered sum of squares and the Helmert identity; sub-Gaussian concentration of `∑_s ⟪a_s, g_{π s} - ḡ⟫` for a uniform permutation, proxy `8M² ∑ ‖a_s - ā‖²` (Hoeffding 1963, Serfling), by induction with `Equiv.Perm.decomposeFin` |
| `Mathlib/Probability/ProbabilityMassFunction/Uniform.lean` | uniform PMF: events, images by equivalences, products |
| `Mathlib/Probability/Independence/InfinitePi.lean` | a coordinate of an infinite product is independent of the previous ones |
| `Mathlib/InformationTheory/KullbackLeibler/BretagnolleHuber.lean`, `Gaussian.lean` | copied from LMLPapers |

## LML

| File | Content |
|---|---|
| `LeanMachineLearning/Design.lean` (additions) | quadratic forms of design matrices, positive semidefiniteness, `designOfWeights` |
| `LeanMachineLearning/DesignMatrix.lean` (additions) | least squares for the Gram matrix of finitely many points |
| `LeanMachineLearning/SequentialLearning/DivergenceDecomposition.lean` | chain rule for the divergence of the histories against non-stationary bandits |
| `LeanMachineLearning/SequentialLearning/AgreeingEnvironments.lean` | runs against environments agreeing before round `t` |
| `LeanMachineLearning/SequentialLearning/EnvironmentDensity.lean` | change of environment with densities depending on the round (LMLPapers has the oblivious case, `EnvDensity.lean`, which is used there instead) |
| `LeanMachineLearning/Online/Bandit/ChangeOfMeasure.lean` | change of measure for non-stationary bandits at a stopping time (`exp(-L_{σ+1})`) |
| `LeanMachineLearning/Identification/ChangeOfMeasure.lean` | data processing for fixed-budget identification (copied from LMLPapers) |
| `LeanMachineLearning/SequentialLearning/Algorithms/RandomOrderLaw.lean` | the actions of `Algorithm.randomOrder x` are `x ∘ π` for a uniform permutation |
| `LeanMachineLearning/Online/Bandit/Linear/ActionModel.lean` | explicit model of a run of an action-only algorithm against a non-stationary linear bandit |

## In LMLPapers

New files: `ForMathlib/Analysis/Convex/Vertices.lean`,
`ForMathlib/Probability/Moments/SamplingWithoutReplacement.lean`,
`Online/Bandit/ChangeOfMeasure.lean` (rebased on `SequentialLearning/EnvDensity.lean`),
`Online/Bandit/Linear/ActionModel.lean`, `SequentialLearning/AgreeingEnvironments.lean`,
`SequentialLearning/Algorithms/RandomOrderLaw.lean`. Merged into existing files:
`ForMathlib/Analysis/InnerProductSpace/Mahalanobis.lean`, `ForMathlib/Probability/HasCondDistrib.lean`,
`ForMathlib/Probability/Moments/SubGaussian.lean` (without the duplicate `HasSubgaussianMGF.mono`),
`ForMathlib/Probability/Distributions/Uniform.lean`, `ForMathlib/Probability/Independence/InfinitePi.lean`,
`Design.lean`, `DesignMatrix.lean`, `SequentialLearning/DivergenceDecomposition.lean`,
`SequentialLearning/Algorithms/RandomOrder.lean` (docstring). Not ported (already there):
Bretagnolle–Huber, the Gaussian divergence, `Identification/ChangeOfMeasure.lean`, and the general
`EnvironmentDensity.lean` (LMLPapers' `EnvDensity.lean` covers the case used).
