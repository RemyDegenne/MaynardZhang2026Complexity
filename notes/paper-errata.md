# Errata of On the Complexity of Best-Arm Identification in Non-Stationary Linear Bandits

Errors found in the paper while formalizing it, with their corrections. Each entry gives where the
error is (the revision of the paper, the result, the page or equation), the error, the correction,
the declarations that state the corrected form, the kind of error and when it was found. Entries
are numbered `E1`, `E2`, … and never renumbered.

## E1. Lemma 5: the norm bounds of Theorem 2 are needed

- **Where:** arXiv:2603.10346v1, Lemma 5 (Sub-Gaussian error of least-squares estimator),
  Section 6.2, and its proof in Appendix B.
- **Error:** the lemma claims that `zᵀ(θ̂_T - θ̄_T)` is `3 ‖z‖_{A⁻¹}`-sub-Gaussian, with
  `A = ∑_t x_t x_tᵀ`, for every allocation and parameter sequence. Its proof applies Lemma 9 with
  `B = M = 1`, that is `‖x_t‖ ≤ 1` and `‖θ_t‖ ≤ 1`, which the statement does not assume. Without
  these bounds the lemma is false: in dimension `1`, with `T = 2`, `x = (1, 2)` and
  `θ = (-10, 10)`, the bias term `S` alone is `±(3/5) · 10 z`, of variance `36 z²`, above the
  claimed variance proxy `9 ‖z‖²_{A⁻¹} = 9 z² / 5`.
- **Correction:** assume `max_x ‖x‖ ≤ 1` and `max_t ‖θ_t‖ ≤ 1`, the assumptions of Theorem 2.
  Theorem 2, the only use of the lemma, is not affected.
- **Lean:** `MaynardZhang2026Complexity.hasSubgaussianMGF_lsEstimator` states the lemma with the
  hypotheses `hx₁` and `hθ`.
- **Kind:** false statement (missing hypothesis).
- **Found:** phase-1 statement check, October 2026 (`notes/blueprint-outline.md`, section 3).

## E2. Theorem 1 and Lemma 3: a nonempty horizon and two arms are needed

- **Where:** arXiv:2603.10346v1, Theorem 1 (Section 5) and Lemma 3 (Optimization-based Lower
  Bound, Section 5.1).
- **Error:** both results claim, for every horizon `T` and every arm set `𝒳`, parameter
  sequences with min-gap at least `Δ > 0` on which every algorithm errs with probability at least
  `(1/4) exp(-4T / H_Adjacent(𝒳, Δ))`, respectively `(1/4) exp(-T f(𝒳, Δ))`. For `T = 0` there
  is no round, and no parameter sequence has a positive min-gap. For a single arm `𝒳 = {x}`,
  every algorithm outputs `x`, the best arm, so both error probabilities vanish and no positive
  lower bound holds (there are no adjacent pairs, and `H_Adjacent` and `f` are extrema over an
  empty set).
- **Correction:** assume `T ≥ 1` and that `𝒳` has at least two points.
- **Lean:** `MaynardZhang2026Complexity.exists_minGapGE_le_max_error` and
  `MaynardZhang2026Complexity.exists_minGapGE_le_max_error_optValue`, with the hypotheses
  `hT : T ≠ 0` and `h𝒳 : 𝒳.Nontrivial`.
- **Kind:** missing hypothesis.
- **Found:** phase-1 statement check, October 2026 (`notes/blueprint-outline.md`, section 3).

## E3. Proof of Lemma 3: the half-horizon construction

- **Where:** arXiv:2603.10346v1, Appendix A, proof of Lemma 3 ("Without loss of generality,
  assume `T` is even").
- **Error:** the proof takes `θ_t = 0`, `θ'_t = v` in the first half of the horizon and
  `θ_t = θ'_t = θ` in the second. The parity of `T` is not without loss of generality: for
  `T = 1` the first half is the whole horizon, where `θ̄ = 0` has no positive min-gap. The
  construction also gives the exponent `T vᵀ A(λ) v` with no slack, so that the bound
  `exp(-T f(𝒳, Δ))` needs a feasible point attaining the inner infimum of `f`, which the proof
  does not establish.
- **Correction:** take `θ_t = 0` and `θ'_t = ṽ` for `t < T`, except at the last round, where
  `θ_T = T θ̃` and `θ'_T = T θ̃ + ṽ`, for a feasible pair `(θ̃, ṽ)` with
  `ṽᵀ A(λ) ṽ < 2 f(𝒳, Δ)`. Then `θ̄_T = θ̃`, `θ̄'_T = θ̃ + ṽ`, the law of the actions under `θ`
  before the last round is that under `θ ≡ 0`, and the exponent is `(T/2) ṽᵀ A(λ) ṽ ≤ T f(𝒳, Δ)`
  for every `T ≥ 1`, with no attainment needed. The statement of Lemma 3 is not affected.
- **Lean:** `MaynardZhang2026Complexity.exists_minGapGE_le_max_error_optValue` is proved this way.
- **Kind:** gap in the proof.
- **Found:** phase-1 blueprint, October 2026 (blueprint, remark `rem:opt_lower_route`).
