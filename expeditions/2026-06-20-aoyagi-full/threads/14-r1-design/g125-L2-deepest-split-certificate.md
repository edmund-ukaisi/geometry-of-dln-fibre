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

## THE CHART INTERFACE — UNIT-JACOBIAN, NOT measure-preserving (load-bearing for the consumers)
The explicit deepest-point χ (replace each regular generator's unit-pivot variable by the generator) has
**Jacobian determinant a UNIT, NOT ±1** — verified on (2,2,2) r=1: `det = (w0+1)²(w4+1)` (a unit near 0,
not constant). This is INTRINSIC: the regular generators have the perturbed pivot `(1+w0)` MULTIPLYING the
pivot variable (`g00 = w4·(1+w0) + w0 + w1·w6`), so the elimination DIVIDES by the unit `(1+w0)` — a pure
det=±1 shear cannot linearize `w4·(1+w0)`. So **χ is a unit-Jacobian analytic diffeo, NOT
`MeasurePreserving`.**

Consequence for the two consumers (they need DIFFERENT transport tools):
- **a114e07e's L2 half-(a) (the regular-block split at the deepest point, NO blow-up):** the pivot is the
  perturbed unit `(1+w0)`, so χ is unit-Jacobian. It does **NOT** satisfy `rlctAtOn_comp_homeomorph`
  (which REQUIRES `MeasurePreserving e volume volume`, det=±1, `S1Fubini.lean:54`). Use instead the
  **unit-weight `rlctAtOn` transport**: single change-of-variables + unit-weight threshold invariance (the
  `rlct_unit_invariant_aux` mechanism — a Jacobian weight bounded in `[a,b]`, `0<a`, near `w0` doesn't move
  the `sSup` of admissible exponents). The unit weight `|Jac χ|` is harmless to the RLCT.
- **fm-2's `schur_chart_exists` (the R1 resolution chart, AFTER the blow-up normalizes the pivot to a HARD
  1):** there the pivot is a constant `1`, so the straighten is pure TRANSVECTIONS (det=±1) — exactly
  `lemma2Fwd`'s structure (the (2,2,2) anchor `measurePreserving_lemma2`, det=−1). This CAN be
  `MeasurePreserving` and uses `rlctAtOn_comp_homeomorph`. The blow-up first (R1) is what makes the pivot a
  hard 1; without it (L2's direct peel) the chart is unit-Jacobian.

Reconciliation: `lemma2Fwd` is MP because the step-1 BLOW-UP (R1) first normalizes `Â[0,0]=1` (hard),
making the straighten transvections. L2's regular peel at the deepest point does NOT blow up (the blow-up
is R1, downstream on the core), so its pivot is the perturbed `(1+w0)` → unit-Jacobian. **Don't force L2's
half-(a) into `MeasurePreserving`; it is intrinsically unit-Jacobian — there is no det=±1 chart for the
direct deepest-point regular peel (the unit-matrix `S_11` multiplication is intrinsic).**

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
