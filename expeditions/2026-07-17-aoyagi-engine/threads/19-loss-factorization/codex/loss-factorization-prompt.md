# Independent adjudication: loss-pullback factorization under a depth-≥2 blow-up composite

You are a decorrelated second mathematician. Derive your own answer from the
setup; a hypothesis is deliberately withheld. Exact algebra only (sympy/sage as
instrument); no Monte-Carlo as a result.

## Setup (Aoyagi 2023, deep linear networks)

Parameter space: composable real matrix tuples `(C^1, …, C^L)`, `C^s` of size
`M^{(s)} × M^{(s+1)}`. Multiplication map `prod = C^1 · C^2 · … · C^L`. The
square-Frobenius loss at the deepest singular point (target `B = 0`) is
`F(C) = ‖C^1 · … · C^L‖²_F`, a sum of squares of the entries of the product.

Aoyagi resolves the singularity `{prod = 0}` to normal crossings by a recursion
that, at each step, applies:
  1. a **max-modulus blow-up chart** (a "pivot chart"): on a `d`-dim center of
     flat coordinates, `pivotChart_i(u)_k = u_i` if `k=i`, else `u_i·u_k` — one
     coordinate `u_i` (the exceptional divisor) is free, the rest become
     `u_i × (ratio)`, ratios in `[-1,1]`, pivot in `[-R,R]`;
  2. a **regular (unit) Q,P normalization** — invertible row/column operations
     that reduce the residual block `D''` to `[[1,0],[0,D_{next}]]` (a Schur
     complement / incidence chart), preserving the ideal but NOT the Frobenius
     norm.

At a fully-monomialized leaf Aoyagi's invariant gives
`prod ~ diag(b_1, …, b_m)` (up to the unit Q,P ops), where the `b_i` are
monomials in the exceptional coordinates with a **divisibility chain**
`b_1 | b_2 | … | b_m`; explicitly `b_1 = ∏_{terminal divisors} u`, and
`b_i / b_{i-1} = ∏_{divisors born at level i-1} u`.

## The formalization's chart and the claim

A Lean formalization defines `chartMap : Params → Params` as a **composite of the
pure max-modulus pivot charts** (from step 1), each conjugated by a LINEAR
coordinate reshuffle `q` that selects the node's center coordinates. The Q,P
normalizations (step 2) are proposed to be pushed into a **source gauge** `α`: a
determinant-1 polynomial shear acting ONLY on ratio coordinates (never the
divisor/pivot coordinates), which does not move the chart's image; so
`chartMap_edge = β ∘ α⁻¹` with `β` the pure pivot chart.

The claim to adjudicate ("LeafPullback") is: at a fully-monomialized leaf, there
exist a `residualCore : Params → ℝ` and constants `0 < lo ≤ hi` with, for every
`w` in a bounded source box,

    frobSq(prod(chartMap w)) = (∏_k (divCoord_k(w))²) · residualCore(w),
    and   lo · baseForm(w) ≤ residualCore(w) ≤ hi · baseForm(w),

where `divCoord_k` are the TERMINAL (`t̃=0`) exceptional divisor coordinates, and
`baseForm(w)` is either `∑ (Morse residual coord)²` (a nondegenerate quadratic in
the leftover directions) or the constant `1` (when there are no leftover Morse
directions).

## Your task

Adjudicate whether this factorization holds under a DEPTH-≥2 composite of these
substitutions. Concretely, work the case `(M) = (2,2,2,2)` (L=3, all layers 2×2),
loss `F = ‖C^1 C^2 C^3‖²`, minimizing branch `t=(1,0,0)`. Also sanity-check L=2
`(2,2,2)`.

Specifically determine, with exact computation:

1. **Divisor power in the product.** Does each divisor factor out of `prod` at
   power exactly 1 (hence power exactly 2 in `frobSq`), or can some divisor reach
   power ≥2 in the product (≥4 in `frobSq`) — e.g. via a divisor that is re-used
   across multiple blow-up steps (Aoyagi's "Case 1(1) re-merge", where a divisor's
   change-of-variables Jacobian exponent accumulates)?

2. **Divisor trapped in the residual.** Can a divisor factor leak into
   `residualCore` — i.e. can `residualCore` vanish on a divisor coordinate's zero
   set, breaking `lo > 0`?

3. **Residual lower bound across the composite.** Is `residualCore` bounded below
   by a positive multiple of `baseForm` on the whole source box, or does the lower
   bound degenerate (non-uniformly) somewhere on the box?

4. **Is the Q,P / incidence normalization load-bearing?** If `chartMap` is the
   PURE pivot-chart composite WITHOUT the Q,P normalization (equivalently, without
   the source gauge α) — does the loss still monomialize to the claimed form, or
   does the residual retain a singularity? Contrast against the composite WITH the
   normalization.

Give a crisp verdict (holds / holds-with-conditions / false-with-witness), the
factorization derivation, any explicit witness, and the exact conditions under
which the squeeze `0 < lo·baseForm ≤ residualCore` holds.
