# Bridge RESOLVED — `phiFlatLiveR1 M222` vs the (2,2,2) `phi222`/`T222` template (the pre-delegation pin)

The controller's hard precondition before delegating the pack/T generalization: resolve CONCRETELY whether
the banked (2,2,2) `phi222`/`pack222`/`T222` (on `B_det222`) is literally `phiFlatLiveR1 M222` (on
`genBlkFlatLiveR1`), or what the exact relation is. This was the abstract-vs-concrete pin that bred the 3
prior conflations (Items 83/84). Resolved by concrete sympy on the ACTUAL `genBlkFlatLiveR1` blocks +
decorrelated Codex (`codex/bridge-{prompt,answer}.md`, A/B/C all confirmed).

## VERDICT: NOT literally equal (different decoder), but the SAME faithful structure

`phiFlatLiveR1 M222` (decoder `genBlkFlatLiveR1`, FIXED-pivot + live-leaf) and `phi222` (decoder
`B_det222`, FREE-pivot E + fixed-leaf-anchor) are the SAME achiever-chart family with the gauge-fixed `1`
RELOCATED (E-slot ↔ leaf-slot). They are **NOT literally equal** at the decoder level — so the banked
`phi222`/`T222`/`pack222` is a **STRUCTURAL TEMPLATE**, NOT a literal bridge equality. Do NOT ask a
formaliser to prove `phiFlatLiveR1 = phi222` (false).

## The faithful decomposition HOLDS for the fixed-pivot decoder (the key fact)

Computed on `genBlkFlatLiveR1 M222`'s ACTUAL blocks (boundary-1: `Bmat1 = bmatStack(K,X) = [[a],[ab]]`,
`Nblk1=[n]`, `Wblk1=[w0,w1]`, `Rmat1` FIXED `= [[0,0],[0,1]]`, `Cgen2` live leaf `= u·[lf0,lf1]`; coords
`(u,a,b,n,w0,w1,lf0,lf1)`):
- `Agen0 = C1 = [[a, a·n],[a·b, a·b·n + u]]` (the `+u` is the FIXED-pivot gauge — the pivot COORDINATE).
- `Agen1 = [C2 − N·W ; W] = [[u·lf0 − n·w0, u·lf1 − n·w1],[w0,w1]]`.
- **`det Dφ = a²·u²` (sympy exact)** = `u^{minAdm−1}·engine` (minAdm(2,2,2)=3 ⟹ `u²`; `a² = |K|^{r+c}`, `r=c=1`).

Codex's EXPLICIT `φ = B ∘ π` (verified): `π = pivotBlowupOn` (`L0=u·lf0, L1=u·lf1`, pivot/spectators fixed),
`det Dπ = u²`; `B` reads the pivot as an ORDINARY coordinate (the Schur-frame isolates it: `p = A0_11 −
A0_10·A0_01/A0_00 = u`), `det DB = a² = engine`, `B` a LOCAL ISO on the engine-open `a≠0` (incl. `u=0`).
So `B` is **radial-free** (no radial det factor), NOT pivot-independent. The additive `+u` is NOT an
affine-radial obstruction — it is the pivot coordinate.

## The DELEGATION spec (the bridge ANSWERED)

- **Target: `phiFlatLiveR1`'s ACTUAL fixed-pivot/live-leaf blocks** (`genBlkFlatLiveR1`), using `T222` ONLY
  as a structural template. NOT a `phi222`-equality.
- **Proof shape (Codex):** Schur-frame isolate the pivot (`p = A0_11 − A0_10·A0_01/A0_00`), shear off the
  `N·W` leaf terms (det-1), then radial `pivotBlowupOn` on the live active coordinates. `B = paramsEquivFlat
  ∘ pack ∘ (boundary Schur frame) ∘ (shear)`, u-free local-iso, `det DB = engine`.
- **Active set (fixed-pivot decoder):** `{structPivot} ∪ {leaf free coords} ∪ {E-free coords excl. the fixed
  E(0,0)}`. At (2,2,2): E-block 1×1 ⟹ no E-free ⟹ `active = {pivot} ∪ {leaf}`, card 3 = minAdm. (Consistent
  with the genm-detradj pin: its `{pivot} ∪ {E-free excl (0,0)} ∪ {leaf}` agrees when E-free is empty.)
- **Wiring (all banked, decoder-agnostic):** `interiorDet_headline_of_BData` (radial via `radialComp_abs_det`),
  `composeFold_hasFDerivAt` (HasFDerivAt free), `foldDerivList_abs_det_perBoundary` (`det DB = ∏ engine`),
  `radialRcols_card` (count), the engine-reshape brick, the `BData` interface.

## What is NOT this bridge (the 3 resolved conflations, for the record)
The whole `hslot`/`hchart`/affine-radial/decoder-fork saga was ONE misreading: `genBlkFlatLiveR1`'s
`Rmat p = u·pivotEIndicator`'s literal-`1` becomes the pivot COORDINATE in the COMPOSITE (`A0_11 = …+u`),
blown up MULTIPLICATIVELY — NOT an additive `u·1` constant, NO affine layer. The `RouteMBData` `B =
phiGen 1 (genBlkFlatLiveR1) + smulRmatRfin` was the WRONG B (a u-free B reading the gauge there steals the
pivot DOF → det 0). The faithful B (Codex's explicit one above) reads the pivot as an ordinary coord.

Bridge is RESOLVED + verified (no wall — a8427f-BOUNDED stands). Cleared to delegate the generalization.
