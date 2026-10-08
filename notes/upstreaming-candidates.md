# Upstreaming candidates

Library-shaped material written in phase 2, by destination. Paths are under
`MaynardZhang2026Complexity/`. The files copied from `LMLPapers` in phase 1 are not listed.

## Mathlib

| File | Content | Notes |
|---|---|---|
| `Mathlib/Analysis/Convex/Vertices.lean` | maximizers of a linear form over `conv s` (`Set.mem_convexHull_setOf_inner_eq`); vertices as strictly exposed points (`Set.mem_vertices_iff_exists_inner_lt`); for finite sets: extreme points are exposed, `conv (vertices 𝒳) = conv 𝒳`, adjacency through a direction, the adjacency lemma (local optimality implies global optimality), the cone property | depends on `Set.vertices`, `Set.IsAdjacent` (`Adjacent.lean`, from LMLPapers); a Mathlib version would state it for `Set.exposedPoints` and exposed segments, perhaps in a normed space with `StrongDual` |
| `Mathlib/Analysis/Convex/AdjacentNonempty.lean` | a point of maximal norm is a vertex; a finite set with two points has an edge | |
| `Mathlib/Analysis/InnerProductSpace/MahalanobisInner.lean` | `mahalanobisSq` and inner products, monotonicity in the Loewner order, Cauchy–Schwarz `⟪x, y⟫² ≤ ‖x‖²_{A⁻¹} ‖y‖²_A` | with `Mahalanobis.lean` (LMLPapers) |
| `Mathlib/InformationTheory/KullbackLeibler/BretagnolleHuber.lean`, `Gaussian.lean` | Bretagnolle–Huber, divergence between real Gaussians | copied from LMLPapers |
| `Mathlib/Probability/Moments/SubGaussian.lean` | `HasSubgaussianMGF.mono`, sums of sub-Gaussian variables on a product space, weighted sums of the coordinates of `Measure.infinitePi` | |
| `Mathlib/Probability/Moments/SamplingWithoutReplacement.lean` | sub-Gaussian concentration of `∑_s ⟪a_s, g_{π s} - ḡ⟫` for a uniform permutation, with proxy `8M² ∑ ‖a_s - ā‖²`; the Helmert identity | a classical result (Hoeffding 1963, Serfling); induction with `Equiv.Perm.decomposeFin` |
| `Mathlib/Probability/ProbabilityMassFunction/Uniform.lean` | uniform PMF: sets, images by equivalences, products | |
| `Mathlib/Probability/HasCondDistrib/Countable.lean`, `Probability/Independence/InfinitePi.lean` | conditional distributions given countable variables; independence of a coordinate from the restriction | |

## LML

| File | Content |
|---|---|
| `LeanMachineLearning/SequentialLearning/DivergenceDecomposition.lean` | chain rule for the divergence of the histories against non-stationary bandits (`Environment.banditSeq`) |
| `LeanMachineLearning/SequentialLearning/AgreeingEnvironments.lean` | runs against environments agreeing before round `t` give the same law to the history and the action of round `t` |
| `LeanMachineLearning/SequentialLearning/EnvironmentDensity.lean` | change of environment: the law of the history against an environment with density w.r.t. another |
| `LeanMachineLearning/Online/Bandit/ChangeOfMeasure.lean` | change of measure for non-stationary bandits at a stopping time (`exp(-L_{σ+1})`) |
| `LeanMachineLearning/Identification/ChangeOfMeasure.lean` | data processing for the output of a fixed-budget identification algorithm (from LMLPapers) |
| `LeanMachineLearning/SequentialLearning/Algorithms/RandomOrderLaw.lean` | the actions of `Algorithm.randomOrder x` are `x ∘ π` for a uniform permutation |
| `LeanMachineLearning/Online/Bandit/Linear/ActionModel.lean` | explicit model of a run of an algorithm reading only its past actions against a non-stationary linear bandit |
| `LeanMachineLearning/LeastSquares.lean`, `DesignMahalanobis.lean`, `DesignOfWeights.lean` | least-squares identities, design matrices and Mahalanobis norms, designs from weights |
