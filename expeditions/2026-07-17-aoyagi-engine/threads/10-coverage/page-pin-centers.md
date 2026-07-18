# Page-pin: the Case-1 / Case-2 blow-up CENTERS (for the rung-2 flat-coord embedding)

*Pinned directly from the Aoyagi 2023 preprint PAGE IMAGES (pp.15-16, 19-20), not extracted text.
Delivers the center geometry `node_pivotCover_of_atom` (`PivotCoverFold.lean`) embeds the rung-1
atom into, page-faithful. Cross-checks the banked `cert-paper-map §2.2` + `cert-atlas-probe`. The
FIX-A label ruling (`theory/aoyagi-2023-reproduction/verify-case2-rawwidth-defect.md`) applies to the
divProfile LABEL, not the center geometry.*

## Case 1 — center (p.16, top, VERBATIM)
> "Construct the blow-up along the submanifold
> `{ d_{ij} = 0 (i = J+1,…,J+J₁, j = J+1,…,M^{(S+1)}),  u_{s,k} = 0 }`."

- **Center coordinates** (the vanishing locus being blown up): the residual-block sub-rectangle
  `{ d_{ij} : i ∈ [J+1, J+J₁] (J₁ rows), j ∈ [J+1, M^{(S+1)}] (M^{(S+1)}−J cols) }` TOGETHER WITH the
  ONE existing divisor variable `u_{s,k}` (the p.15 tie-break fixes WHICH: `t̃_{s,k} = J+J₁` and
  `T_{s,k} ≤ T_{s',k'}` for all `t̃_{s',k'} = J+J₁`, Def-4-minimal).
- **Center codimension** `d_center = J₁·(M^{(S+1)}−J) + 1` (the d-block entries + `u_{s,k}`).
- **Pivot charts** (p.16): `1(1)` = the `u_{s,k}`-pivot (factor `u_{s,k}` out of the whole run:
  `d_{ij} = u_{s,k}·d'_{ij}`); `1(2)` = a `d`-entry-pivot, shown at the CORNER `d_{J+1,J+1} = u_{S,J+1}`
  (becomes a unit `1`). Aoyagi writes only these TWO representatives ("by a blow-up process"); the
  FULL family is one pivot per center coordinate.

## Case 2 — center (p.19, VERBATIM)
> "Construct the blow-up along submanifold
> `{ d_{ij} = 0, (i = J+1,…,M(S), j = J+1,…,M^{(S+1)}) }`."

- **Center coordinates**: the ENTIRE residual block `D_J`, size `(M(S)−J) × (M^{(S+1)}−J)` — the
  running-min corank `M(S) = min{M^{(s)} : s ≤ S}`. **NO `u` variable** in the Case-2 center (unlike
  Case 1).
- **Center codimension** `d_center = (M(S)−J)·(M^{(S+1)}−J)`.
- **Pivot charts** (p.19-20): `d`-entry pivots, shown at the corner `d_{J+1,J+1} = u_{S,J+1}` (unit);
  then a regular shear `Q` (p.20) cleans the first row. Full family = one pivot per block entry.
- **Label (FIX-A)**: p.20 sets the new pivot's head `t^{(i)}_{S,J+1} := M^{(i+1)}` (RAW width) — the
  VERIFIED DEFECT; corrected to the running-min `M(i+1) = min(M^1,…,M^{(i+1)})`. Tail `t^{(S..L)} := J`,
  `t̃ = J`; exponent `M'_{S,J+1} = (M(S)−J)(M^{(S+1)}−J)`. This is a divProfile-LABEL correction; the
  center geometry (the residual block) is unaffected.

## Consequence for (a)-vs-(b) (the surfaced interface question)
The pages CONFIRM the controller's **(a)-generalized** reading:
- The `1(1)` / `1(2)` tags mark pivot **TYPE**, not a 2-chart restriction: `1(1)` = the `u`-pivot
  (Case 1 only); `1(2)` / Case-2 charts = the `d`-entry pivots (one per residual-block entry). Aoyagi
  shows the corner `d`-entry as representative and asserts the rest "by a blow-up process".
- The FULL pivot family per node has **`d_center` charts** = the center's codimension
  (Case 1: `J₁·(M^{(S+1)}−J) + 1`; Case 2: `(M(S)−J)·(M^{(S+1)}−J)`). Proving these COVER is exactly
  the coverage-theorem content (what Aoyagi asserts).
- `CompChainInv` is consumed for the ratio/principalization side (which pivot is Def-4-minimal / the
  no-smaller-ratio), NOT for manufacturing the cover — the cover is the atom applied to the full
  center-coordinate family.

## Rung-1 atom embedding (page-faithful `node_pivotCover_of_atom`)
The blow-up of the ambient along a coordinate subspace `{x₁=…=x_{d_center}=0}` is covered by its
`d_center` pivot charts (rung-1 `iUnion_pivotChart_image_eq_cubeBox` at `d = d_center`); the transverse
(untouched) flat coordinates pass through unchanged. The center coordinates map into `Fin (flatDim M)`
via the leaf's `divCoord`/`resCoord`:
- **Case 2**: `d = (M(S)−J)·(M^{(S+1)}−J)`, all pivots = residual-block entries (pure `d`-block).
- **Case 1**: `d = J₁·(M^{(S+1)}−J) + 1`, pivots = the run's `d`-entries + the divisor coord `u_{s,k}`
  (the atom is agnostic to coordinate meaning — it covers the max-modulus sector uniformly).
