**A. r=1 Leaf**

Clean lift for `p ≥ 1`: the integral factors as `|Δ₀₀|^{-2c'} · (∑ S₀q²)^{-c'}`, finite under `c' < 1/2` and `c' < p/2`; `c' < schurLambdaP p 1 = 1/2` gives both. For `p = 0`, the hypotheses are vacuous since `schurLambdaP 0 1 = 0`.

**B. r=2 Via Relaxed Carve**

**Verdict: works, by the structure you described.** No visible degeneration in (i), (ii), or (iii): the chart cover still has pivots, the N2b `j=1` split leaves a `1 × 1` Schur residual, the radial condition `c' < r²/2 = 2` follows from `schurLambdaP p 2 ≤ 2`, and the IH applies because
`c' - p/2 < schurLambdaP p 2 - p/2 ≤ schurLambdaP p 1 = 1/2`.

Cast/index subtlety: the residual index family is now over `Fin (r-1) = Fin 1`, so every lifted index is literally `1 + 0 < 2`; Lean may need explicit `Nat.succ_lt_succ`/`omega` help around casts from `r - 1` after specializing `r = 2`.

The only caveat is **INFERENCE**: this assumes the N2b split, pivot normalization, and carve lemmas are stated uniformly for nonempty residual size `r-1`, not with hidden side conditions requiring `2 ≤ r-1` or two residual rows/columns.

Confidence on B: **medium-high**.

**C. If B Fails**

skip.