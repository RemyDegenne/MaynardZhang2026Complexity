# Comparator setup

Machine-checkable verification, with [leanprover/comparator](https://github.com/leanprover/comparator),
that this repository proves the headline results claimed in [`formalization.yaml`](../formalization.yaml)
without having to read or trust the Lean development in `MaynardZhang2026Complexity/`.

**Status.** Phase 2 complete (2026-10-08): the project proves the 13 headline theorems with no
`sorry` and the standard axioms only; the challenges, regenerated after phase 2, compile
(`lake build Comparator`). The statement of Lemma 6 was corrected in phase 2 (an indexing error
of phase 1, see `notes/blueprint-outline.md`, section 3). The full comparator run
(`scripts/comparator-verify.sh`) remains to be done.

Each challenge is one self-contained file whose transitive imports resolve to Mathlib and Lean
core only, the shape the [Palomar registry](https://palomar-registry.org/) enforces: no LML, no
project modules, no sibling helpers.

## The trust story

For each headline theorem `MaynardZhang2026Complexity.<name>` there is a challenge file `Challenge_<name>.lean` and a
config `<name>.json`; the list is `targets.txt`:

| paper result | challenge(s) |
|---|---|
| Lemma 1 (adjacency lemma) | `exists_pos_inner_iff` |
| Theorem 1 (lower bound) | `exists_minGapGE_le_max_error` |
| Lemma 2 (non-stationary bandit lower bound) | `le_max_prob_ne` |
| Lemma 3 (optimization-based lower bound) | `exists_minGapGE_le_max_error_optValue` |
| Lemma 4 (inner problem for adjacent pairs) | `pairValue_eq` |
| Theorem 2 (error of Adjacent-BAI) | `prob_ne_bestArm_le` |
| Lemma 5 (sub-Gaussian least squares) | `hasSubgaussianMGF_lsEstimator` |
| Lemma 6 (change of measure) | `trajMeasure_eq_lintegral_exp_neg_llrProcess` |
| Lemma 7 (lower bound, inner problem) | `le_pairValue` |
| Lemma 8 (upper bound, inner problem) | `pairValue_le` |
| Lemma 9 (random permutation sums) | `hasSubgaussianMGF_sum_perm` |
| Lemma 10 (ratio at adjacent arms) | `ratio_le_iSup_adjacentTo` |
| Proposition 1 (stationary complexity) | `iInf_iSup_ratio_eq` |

Each challenge states the theorem with `sorry`, with every definition the statement rests on
copied verbatim from its source by [challenge-gen](https://github.com/LeanTrustBuilders/challenge-gen):
the project's definitions and the LML declarations they build on. A reader checks the *statement*
(the challenge file) by hand and lets comparator check that the project proves exactly it, with
no axioms beyond `propext`, `Classical.choice` and `Quot.sound`, the proofs replayed through the
kernel. The config also lists the lemmas the definitions use, left `sorry` in the challenge and
proved by the project, and the theorems Lean makes of the proofs inside definitions.

## Regenerating and running

`scripts/make-challenges.py` regenerates every challenge and config from `targets.txt`;
`lake build Comparator` checks that they compile; `scripts/comparator-verify.sh [--insecure]`
runs comparator on every config (see the script header for the sandbox requirements).
