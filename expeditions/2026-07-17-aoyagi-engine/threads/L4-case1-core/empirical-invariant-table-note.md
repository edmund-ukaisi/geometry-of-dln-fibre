# §-note: the empirical invariant table (pnp-transport → the elder's carried-invariant ruling)

Node-by-node `foldResid` for two witnesses — `(2,2,2,2)` (non-wide reference) and `(2,3,2,2)` (smallest
wide-with-descent) — recording per slot: (i) monomial support (in-cap vs out-of-cap), (ii) extra-block
coefficient factoring (the b-chain as it actually appears), (iii) per-layer degrees. Script:
`verify/empirical_invariant_table.py` (exact sympy, exit 0). **Recording what is TRUE, defect rows
included.** Model: the `canonShearOf` fold (the one the transport-table cert rides on; unambiguous). The
FAITHFUL (`N_p`, deeper recoord) contrast is in §3 below.

## 1. `(2,2,2,2)` — non-wide reference (`widthMinUpto(1) = d_1 = 2`, no cap gap)

| node | edge | child (L,cl) | supportLayer | support cols | out-of-cap | per-layer deg | b-chain (extra-block coeff vanishes at pivot?) |
|---|---|---|---|---|---|---|---|
| 0 | root | (0,0) | 0 | {0} or {1} per slot | — | (1,1,1) | n/a (J=0) |
| 1 | case2 δ1 | (0,1) | 1 | {0,1} | — | (2,1,1)/(1,1,1) | — |
| 2 | case2 δ0 | (0,2) | 1 | {0,1} | — | (2,1,1)/(1,1,1) | — |
| 3 | rollover | (1,0) **= boost parent** | 1 | {0,1} | — | (2,1,1)/(1,1,1) | **extra-block (col≥runLen=1) coeffs `u101,u111` do NOT vanish at any birth pivot — b-chain ABSENT** |
| 4 | case11 δ1 | (1,0) | 1 | {0,1} | — | (2,1,1)/(1,1,1) | — |

**Reading.** Support stays in-cap (non-wide). Per-layer degree: the CLEARED layer below the support
(layer 0 at nodes 1–4) hits **degree 2** on 2 of 4 slots — consistent with `PerLayerDeg1From` asserting
degree ≤ 1 only for `ℓ ≥ supportLayer` (the `fromLayer` threshold). **The decisive row is node 3 (the boost
parent):** in the `canonShearOf` model the extra-block coefficients do NOT carry the pivot factor — the
"form too weak" defect (= the `F = x + yz` countermodel of the transport-table cert, node-explicit).

## 2. `(2,3,2,2)` — wide-with-descent (`widthMinUpto(1) = min(2,3) = 2 < d_1 = 3`, cap gap at layer-1 col 2)

| node | edge | child (L,cl) | supportLayer | support cols | out-of-cap | per-layer deg |
|---|---|---|---|---|---|---|
| 0 | root | (0,0) | 0 | {0} or {1} | — | (1,1,1) |
| 1 | case2 δ1 | (0,1) | 1 | **{0,1,2}** | **(L1,r0,c2),(L1,r1,c2)** | (1,1,1)/(2,1,1) |
| 2 | case2 δ0 | (0,2) | 1 | **{0,1,2}** | **(L1,r0,c2),(L1,r1,c2)** | (1,1,1)/(2,1,1) |
| 3 | rollover | (1,0) | 1 | **{0,1,2}** | **(L1,r0,c2),(L1,r1,c2)** | (1,1,1)/(2,1,1) |

**Reading.** As soon as the support DESCENDS to layer 1 (node 1, after the first layer-0 clear), the
residual's layer-1 support includes col 2 — which `blockCoords(1)` (`col < widthMinUpto(1) = 2`) EXCLUDES.
So on the wide branch the true support is `layerCoords(1)` (all cols), NOT `blockCoords(1)` — the
"support too tight" defect, node-explicit and present at EVERY descended node. (Per the cap-escape note,
this is inherent to the wide block: the residual reads the deeper factor's out-of-cap column via the
wide layer-0 remnant row; it does not depend on the recoord.)

## 3. The FAITHFUL (`N_p`, deeper recoord) contrast — the b-chain IS the true structure on the real branch

The `canonShearOf` model (§1) shows the b-chain ABSENT at the boost parent. But the REAL branch now uses
the faithful `N_p` (baked `canonNormalizationOf`), and there the b-chain IS present (`honest_clear_2222.py`,
`npivot-certificate.md` §4b): the boost-parent residual is
`resid[1] = e2·(u₂₀₀·w₁₀₁ + u₂₀₁·w₁₁₁) + s·(u₂₀₀·w₁₀₀ + u₂₀₁·w₁₁₀)`, so the extra-block (col-1) coefficients
DO vanish at the pivot — but the pivot is the **Schur-reduced coordinate** `e2 = u_(0,1,1) − u_(0,1,0)·u_(0,0,1)`
(= div1's exceptional coord; the fold coord at div1's birth corner `(0,1,1)` HOLDS `e2` after the shear),
NOT the literal birth corner `u_(0,1,1)`. So:
- **The b-chain divisor is the reused divisor `div1`, realized as its Schur-reduced exceptional `e2` at the
  birth corner `(0,1,1)`.** The extra-block coefficients vanish at `e2 = 0`.
- This is the path-inductive datum the memo's "form too weak" catch names: `Deg1SupportedSlot`'s `∃c`
  coefficients are continuity-only; the true (faithful-branch) coefficients additionally vanish at the
  reused divisor's (Schur) pivot. The invariant SHOULD carry this (it is TRUE on the real branch), which
  supports strengthening the form (fork B).

## 4. Net for the elder's consolidated ruling

- **Support:** carry `layerCoords(S+1)` (not `blockCoords(S+1)`) for the descended support — TRUE at every
  descended node on the wide witness (§2). `(2,2,2,2)` is not wide, so the two shapes coincide there — which
  is why the defect was not previously exposed.
- **Form:** the carried `∃c` must add "extra-block coefficients vanish at the reused divisor's Schur pivot"
  (the b-chain) — TRUE on the faithful branch (§3), absent under `canonShearOf` (§1). This is path-inductive
  (the pivot is a Schur coord accumulated along the branch), so it cannot be a continuity-only ∃c.
- **Degrees:** `PerLayerDeg1From` (degree ≤ 1 for `ℓ ≥ supportLayer`) holds; the cleared layer below the
  support is degree 2 (expected, the `fromLayer` threshold is load-bearing).

**Epistemic caveat.** This is my `canonShearOf`-model fold (§1/§2, unambiguous) + the faithful-`N_p` contrast
from `honest_clear`/`npivot` (§3). The cap-escape (§2) is inherent (recoord-independent, robust). The
faithful b-chain (§3) rides the recoord modeled per worked.tex:445 + the (3,3,4) battery. The exact
interaction with the baked `canonNormalizationOf`/`foldResid` is seat-L4D's def-level side; the empirical
truth recorded here is what the real branch's residual DOES, node by node.
