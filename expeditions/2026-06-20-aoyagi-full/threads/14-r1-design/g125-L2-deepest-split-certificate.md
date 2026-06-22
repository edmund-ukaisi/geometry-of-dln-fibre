# L2 deepest-point split — WITNESS (explicit unit-pivot, no constant-rank) (pp-hall, 2026-06-22, #125)

**Task #125 (de-risks a114e07e's live L2 `product_reduction` build #124).** Is the regular/core split AT
THE DEEPEST POINT (`F = ‖∏C−B‖² = [regular nondegenerate quadratic, dim nReg] + [homogeneous core]`)
achievable by an EXPLICIT polynomial/analytic unit-pivot change of variables, or does it require the
absent Mathlib constant-rank/Morse theorem?

**Verdict: WITNESS — explicit triangular unit-pivot elimination, NO constant-rank theorem.** Two
decorrelated legs converged (pp-hall exact algebra (2,2,2)/(3,2,3)/(2,2,2,2) r=1 + higher-rank + Codex
xhigh with the block-structure proof). The deepest point is the CLEANEST case (identity corners by
construction, no gauge needed). This extends #122's elementary-route finding to the L2 split a114e07e
needs.

## The explicit witness (exact, verified)
At the deepest point, every layer is in the identity-corner block-normal form (the output of
`deepestPoint_exists`/`block_elimination`, already in Lean): `C^(s) = [[I_r+X_s, Y_s],[Z_s, T_s]]`. The
linearization of `P = C^(1)···C^(L)` at this point (Codex's block computation, pp-confirmed):
`d(P−B) = [[Σ_s X_s, Y_L],[Z_1, 0]]`. The regular generators are exactly the blocks `P_11−I_r`, `P_12`,
`P_21`, with explicit UNIT pivots `X_1`, `Y_L`, `Z_1`; their count is
`r² + r(M^{L+1}−r) + (M^1−r)r = r(M^1+M^{L+1}) − r² = nReg`. The bottom-right block is the residual
HOMOGENEOUS core (no linear part). The triangular solve is explicit block multiplication: with
`S = C^(2)···C^(L)` (`S_11` a unit, constant term `I_r`) and `R = C^(1)···C^(L−1)` (`R_11` a unit),
`P_21 = Z_1 S_11 + T_1 S_21` solves `Z_1`; `P_11 = (I+X_1)S_11 + Y_1 S_21` solves `X_1`;
`P_12 = R_11 Y_L + R_12 T_L` solves `Y_L` — all by division by a UNIT, no general implicit-function theorem.

## Exact-algebra confirmation (pp-hall)
| case | generators | Jac rank = nReg | regular (unit pivots) | core | pivots distinct (triangular) |
|---|---|---|---|---|---|
| (2,2,2) r=1 | 4 | 3 = −1+1·4 ✓ | 3 (g0:w0+w4, g1:w5, g2:w2) | 1 | ✓ |
| (3,2,3) r=1 | 9 | 5 = −1+1·6 ✓ | 5 | 4 | ✓ |
| (2,2,2) r=2 (full) | 4 | 4 = −4+2·4 ✓ | 4 | 0 | ✓ |
| (2,2,2,2) r=1, L=3 | 4 | 3 = −1+1·4 ✓ | 3 (g0:w0+w4+w8, g1:w9, g2:w2) | 1 | ✓ |
| (4,4,4) r=2 | — | 12 = −4+2·8 ✓ | 12 | — | ✓ |
| (4,3,2) r=1 | — | 5 ✓ | 5 | — | ✓ |
| (4,3,2) r=2 | — | 8 ✓ | 8 | — | ✓ |

In every case the regular generators each carry a variable with a ±1 coefficient (a unit pivot from the
identity corner), AND the chosen pivots are DISTINCT — so a valid triangular elimination order always
exists (`g125_*.py`). The L=3 case shows the pivot `g0 = w0+w4+w8` (the layers' (0,0) perturbations
summing, still a unit pivot). No `r,M` (with `r ≤ M^s`) forces a non-triangular case.

## Why no constant-rank theorem is needed
The general constant-rank/Morse theorem manufactures coordinates ABSTRACTLY from "rank locally constant".
Here the identity corner supplies, by construction, a PRIVATE ±1-coefficient perturbation entry for each
of the nReg regular generators — so the split is triangular Gaussian elimination + division-by-unit
(unit-denominator analytic solutions). Lean ingredient: local unit-division for analytic/smooth functions
+ finite triangular induction — much lighter than constant-rank, and `deepestPoint_exists` already gives
the identity corners (no gauge step, unlike arbitrary-v #122).

## The caveat (both legs, scope-honest)
The split is an explicit analytic/unit GENERATOR equivalence: after the regular coordinates, the residual
bottom-right block is replaced by the Schur-complement/core generator, with only unit denominators. This
is exactly what `product_reduction`/RLCT needs (RLCT is invariant under such unit-generator equivalence +
the measure-preserving / S1 transport). It is NOT the literal Euclidean equality of the original squared
norm after a source-only change of coordinates — demanding that would be the stronger Morse splitting. For
the L2 RLCT split, the unit-pivot witness suffices.

## Net for a114e07e's #124 build
L2 `product_reduction`'s deepest-point split is **explicit-algebraic (unit-pivot), NOT constant-rank-gated**
— build it on (identity corners from `deepestPoint_exists` + triangular unit-pivot elimination via
unit-division + the Schur-complement core), the same elementary route as #122 but cleaner (no gauge). The
regular block contributes `nReg/2` (via `smoothBlockND_rlct` after the split); the core is the homogeneous
residual handed to R1. No Mathlib-scale dependency.

Decorrelation: pp-hall exact (3 scripts `g125-scripts/`: the 4-case split + higher-rank triangularity +
the L=3 case) + Codex xhigh (independent: WITNESS, the block-structure linearization `[[ΣX_s,Y_L],[Z_1,0]]`,
the explicit triangular block-multiplication solve, "no hidden non-triangular obstruction for any r,M",
the same generator-equivalence caveat). Converged. Consult `codex/g125-L2-deepest-split-{prompt,answer}.md`.
Builds on #122 (`g122-elementary-route-certificate.md`).
