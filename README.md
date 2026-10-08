# MaynardZhang2026Complexity

Lean 4 formalization of the paper

> Leo Maynard-Zhang, Zhihan Xiong, Kevin Jamieson, Maryam Fazel, *On the Complexity of Best-Arm
> Identification in Non-Stationary Linear Bandits*, COLT 2026,
> [arXiv:2603.10346](https://arxiv.org/abs/2603.10346),

built on Mathlib and the [Lean Machine Learning](https://github.com/LeanMachineLearning/LML)
library (LML, branch `rename`). The development is blueprint-driven:
[blueprint](https://remydegenne.github.io/MaynardZhang2026Complexity/blueprint/),
[dependency graph](https://remydegenne.github.io/MaynardZhang2026Complexity/blueprint/dep_graph_document.html).

**Status: phase 1 (statements).** The 13 results of the paper are stated in Lean with `sorry`.
They are listed in [`formalization.yaml`](formalization.yaml) and are standalone challenges for
[comparator](https://github.com/leanprover/comparator) in [`comparator/`](comparator/).

## Layout

* `MaynardZhang2026Complexity/MXJF2026/`: the paper, one file per result (`Lemma1.lean`, …,
  `Theorem2.lean`, `Proposition1.lean`), namespace `MaynardZhang2026Complexity`; the setting,
  the complexity `H_Adjacent`, the optimization problem of the lower bound and Algorithm 1 are in
  `Setting.lean`.
* `MaynardZhang2026Complexity/LeanMachineLearning/`: material for LML (from `LMLPapers`):
  non-stationary bandits and linear bandits, designs and design matrices, identification
  algorithms with a fixed budget, the algorithm playing an allocation in random order.
* `MaynardZhang2026Complexity/Mathlib/`: material for Mathlib (from `LMLPapers`): Mahalanobis
  norms, vertices and adjacent vertices of the convex hull of a set, Loewner order and square
  roots of matrices.
* `blueprint/src/`: the blueprint (Part I follows the paper, Part II the prerequisites);
  `notes/blueprint-outline.md`: the outline it was written from (labels, corrections, proof
  routes); `source/`: the paper's LaTeX source.

## Results of the paper

| Result | Lean declaration | Notes |
|---|---|---|
| Lemma 1 (adjacency lemma) | `exists_pos_inner_iff` | |
| Theorem 1 (lower bound) | `exists_minGapGE_le_max_error` | `T ≥ 1` and two arms added (false otherwise) |
| Lemma 2 (non-stationary bandit lower bound) | `le_max_prob_ne` | any two distinct arms |
| Lemma 3 (optimization-based lower bound) | `exists_minGapGE_le_max_error_optValue` | `T ≥ 1` and two arms added; no spanning |
| Lemma 4 (inner problem for adjacent pairs) | `pairValue_eq` | every positive definite matrix |
| Theorem 2 (error of Adjacent-BAI) | `prob_ne_bestArm_le` | rounding guarantee as hypothesis, no `T ≥ d²` |
| Lemma 5 (sub-Gaussian least squares) | `hasSubgaussianMGF_lsEstimator` | norm bounds added (false otherwise) |
| Proposition 1 (stationary complexity) | `iInf_iSup_ratio_eq` | no spanning |
| Lemma 6 (change of measure) | `trajMeasure_eq_lintegral_exp_neg_llrProcess` | countably many arms |
| Lemma 7 (lower bound, inner problem) | `le_pairValue` | |
| Lemma 8 (upper bound, inner problem) | `pairValue_le` | every `Δ` |
| Lemma 9 (random permutation sums) | `hasSubgaussianMGF_sum_perm` | |
| Lemma 10 (ratio at adjacent arms) | `ratio_le_iSup_adjacentTo` | |
| Appendix C (computing the adjacent pairs) | — | an algorithm, not formalized |

The corrections and the proof routes that differ from the paper are explained in the blueprint
and in `notes/blueprint-outline.md` (sections 3 and 4).

## Building and checking

```
lake exe cache get
lake build MaynardZhang2026Complexity
lake exe runLinter MaynardZhang2026Complexity
python3 scripts/check-blueprint.py && leanblueprint pdf && leanblueprint web
lake exe checkdecls blueprint/lean_decls
python3 scripts/make-challenges.py && lake build Comparator
```
