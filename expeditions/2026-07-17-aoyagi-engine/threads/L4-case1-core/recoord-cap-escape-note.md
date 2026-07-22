# §-note: the recoord cap-escape trace (pnp-transport, for seat-L3T2 / seat-L4D / elder slot-shape)

**Question (seat-L3T2, def-level):** the faithful deeper recoord `A_{S+1} → A_{S+1}·Q₁⁻¹`
(`canonNormalizationOf` (ii)) writes layer `S+1` at col = the pivot-ROW index, which ranges over the
UNCAPPED raw remnant `Fin d_{S+1}` (the column-remnant transpose: `canonCenterOf` caps the flat COL by
`widthMinUpto`, leaves the flat ROW the raw remnant). On a WIDE branch — `d_{S+1} > widthMinUpto(S)`, whence
`widthMinUpto(S+1) = widthMinUpto(S) < d_{S+1}` — a pivot with row `≥ widthMinUpto(S+1)` makes the recoord
write OUTSIDE `blockCoords(S+1)`. Does that propagate into `foldResid(child)`'s support, or cancel?

**VERDICT: OUT-OF-CAP — it propagates, and the propagation is INHERENT to the wide block (not a recoord
artifact).** `blockCoords(S+1)` is FALSE as the residual support on wide branches; the true support is the
full `layerCoords(S+1)`. Script: `verify/recoord_cap_escape.py` (exact sympy, exit 0).

## Escape geometry (which `d` exhibit it)
A cleared layer `S` (`S ≤ N−2`) with `d_{S+1} > widthMinUpto(S)`. Computed:
- `(3,3,4)`: **NO** recoord escape — its `d_2 = 4` is the ROW axis of `A_1`, not the recoord COL axis
  (`= Fin d_1 = 3 = widthMinUpto(1)`). (The team-lead's "wide at the last layer" is the row width, not the
  recoord axis.)
- `(2,3,2)`, `(2,3,2,2)`, `(2,3,3,2)`, `(2,4,2,2)`: **YES**, at `S = 0` (`d_1 = 3 > widthMinUpto(0) = 2`).
- **The three standard N_p witnesses `(2,2,2,2)`/`(3,3,4)`/`(3,3,2,2)` are NONE of them wide** — so this
  escape was never exercised by the N_p certificate's witnesses. Smallest wide witness: `(2,3,2)`; smallest
  with a non-terminal descent child: `(2,3,2,2)`.

## The trace (`d = (2,3,2,2)`, clear layer 0; `A_0 = 3×2`, `A_1 = 2×3` (cols `= Fin d_1 = 3`), `A_2 = 2×2`)
`widthMinUpto(1) = min(2,3) = 2`, so `A_1` col 2 is OUT-OF-CAP (`blockCoords(1)` caps col `< 2`).

- **The recoord mechanism.** Clearing the layer-0 pivots (canonical rows 0,1) requires row-ops that also
  eliminate the WIDE remnant row 2's entries; the deeper recoord for that row-op mixes `A_1`'s out-of-cap
  col 2 into the in-cap col 0: `A_1''[:,0] = A_1[:,0] + w₁₀·A_1[:,1] + w₂₀·A_1[:,2]` (`w₂₀ = A_0[2,0]/A_0[0,0]`,
  the remnant-row entry). The residual reads `A_1''[:,0]`, so it reads `A_1[:,2]`.
- **The residual `foldResid(child) = A_2·A_1''·A_0''` depends LINEARLY (support, not coefficient) on the
  out-of-cap coords `A_1[·,2]` — all 4 entries.** Surviving out-of-cap SUPPORT monomial:
  `coeff of q₁₀₂ in resid[0,0] = p₀₂₀·r₂₀₀` (nonzero) — `q₁₀₂ = u_(1,0,2)` (out-of-cap), `p₀₂₀ = u_(0,2,0)`
  (the wide remnant row), `r₂₀₀ = u_(2,0,0)`.
- **INHERENT (robust to the recoord).** Even the plain fold (no recoord; `canonShearOf`'s Schur interior
  only) reads col 2: `canonShearOf`/`N_p` clears only `widthMinUpto(S) = 2` pivots (rows 0,1), so `A_0`'s
  remnant row 2 col 0 = `p₀₂₀` stays LIVE, and `coreGen`'s `A_1[i,2]·A_0[2,j]` term reads col 2. Same
  surviving monomial `p₀₂₀·r₂₀₀`. The recoord merely RELOCATES the same dependence from the direct
  remnant-row term into the in-cap col 0. So the finding does not hinge on the exact `canonNormalizationOf`
  encoding.

## Cross-check against the N_p certificate §4/§7
My N_p certificate assumed the residual support stays `blockCoords(S+1)` (the ε-table / chainWeight ranges
over the block). **That is correct on the tested (non-wide) witnesses but FALSE on wide branches.** The
ε-table / `chainWeight` / the carried `Deg1SupportedSlot` support must range over `layerCoords(S+1)` (the
full descended layer), NOT the `widthMinUpto`-capped `blockCoords(S+1)`, whenever `d_{S+1} > widthMinUpto(S)`.
The monomialisation and b-chain/M results are unaffected (they are per-chart / combinatorial); only the
SUPPORT-SET shape of the descended-layer slot is too tight.

## Consequence for seat-L4D + the elder's slot-shape adjudication
- The carried descended-layer support should be `layerCoords(S+1)`, not `blockCoords(S+1)`, OR the
  invariant must carry a separate account of the remnant-row (out-of-cap) columns. The tension the elder
  must weigh: widening the support to `layerCoords(S+1)` may complicate the case11 boost-readiness
  (`Deg1SupportedOn ed.center` needs the residual degree-1 on the *boost center*, a subset of the block —
  extra out-of-cap support coords beyond the center would need the same `u_pivot`-carrying / peel treatment
  as the extra block).
- **CAVEAT (epistemic):** this is a coreGen/matrix-level trace with the recoord modeled per worked.tex:445 +
  the (3,3,4) battery peel; the INHERENT (recoord-independent) version makes the "reads out-of-cap col"
  robust, but the exact interaction with the baked `canonNormalizationOf` / `foldResid` / the running-min
  block cap should be confirmed by seat-L4D against the def (my worktree is a mixed state and does not carry
  the baked `canonNormalizationOf` def to re-run against). The decisive, robust datum is: **on a wide block,
  the residual reads the deeper factor's out-of-cap column via the wide remnant row.**
