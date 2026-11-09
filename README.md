# MaynardZhang2026Complexity

A Lean 4 formalization of *On the Complexity of Best-Arm Identification in Non-Stationary Linear
Bandits* (Leo Maynard-Zhang, Zhihan Xiong, Kevin Jamieson and Maryam Fazel, COLT 2026,
[arXiv:2603.10346](https://arxiv.org/abs/2603.10346)), on top of
[LMLExplore](https://github.com/LeanMachineLearning/LMLExplore), and so of
[LML](https://github.com/LeanMachineLearning/LML), [Tau Ceti](https://github.com/TauCetiProject/TauCeti)
and [Mathlib](https://github.com/leanprover-community/mathlib4). It follows the layout of
[lml-paper-template](https://github.com/LeanMachineLearning/lml-paper-template).

It formalizes the arm-set-dependent complexity `H_Adjacent(𝒳, Δ)` of fixed-budget best-arm
identification in linear bandits whose parameter sequence is fixed in advance: the adjacency lemma
(Lemma 1), the lower bound `(1/4) exp(-4T / H_Adjacent)` for every algorithm (Theorem 1, with
Lemmas 2–4, 6–8), the matching upper bound of the Adjacent-BAI algorithm (Theorem 2, with Lemmas 5
and 9), and the stationary fixed-confidence complexity (Lemma 10 and Proposition 1). Three
statements are corrected, Lemma 5, Theorem 1 and Lemma 3: see the errata. Every headline result is
proved, with no `sorry`; the rounding procedure and the computation of the adjacent pairs
(Appendix C) are not formalized.

- Website: https://RemyDegenne.github.io/MaynardZhang2026Complexity/, with the blueprint, the
  referee site and the literature links (which declarations formalize which results of the
  paper). CI builds it on each push to `main`. `scripts/formalize.sh` also commits the literature
  links, as `literature/annotations.jsonl`, when the paper is formalized and after the final bump.
- The paper: `source/`. Errors found in it, with their corrections: `notes/paper-errata.md`.
- The paper's results: `MaynardZhang2026Complexity/MXJF2026/`, one file per result, listed with
  their status in `formalization.yaml`; comparator challenges in `comparator/`.
- Library-shaped material: `MaynardZhang2026Complexity/ForLMLExplore/`, which Tau Ceti workers
  port to LMLExplore; `PAPER_ROADMAP.md` says where each item goes.
- The blueprint outline (labels, corrections, proof routes), the plan of phase 2 and the
  upstreaming candidates: `notes/`.

## Building

```bash
scripts/build.sh
```

The script fetches Mathlib's and Tau Ceti's prebuilt files, then runs `lake build`; its arguments go
to `lake build`.

## Working on it

The workflow is the `formalize-paper` skill of the `lml` Claude Code plugin
([lml-claude](https://github.com/LeanMachineLearning/lml-claude)). The paper is formalized; what is
left is to contribute its library-shaped part. `scripts/formalize.sh`, in a terminal or tmux, tags
`PAPER_ROADMAP.md`, sends the reusable parts to LMLExplore, and once they are merged moves the paper
to the current LMLExplore.
