**1. THE BUDGET RECONCILIATION**

Follows from your summary: there is no extra coordinate budget for `Rfin`. So a LIVE-leaf decoder on `Fin N` with `N = flatDim M` can only fit by reusing existing `ChartIdx` slots. It cannot be `genBlkFlatStruct` plus a new free `Rfin`.

So, if the LIVE decoder is square on the same `Fin N`, option **(a)** is the only viable reconciliation in spirit: some existing schur/lift coordinates must be rerouted to feed `Rfin` and the chosen live `Rmat` entries. But **ASSUMPTION to verify**: “the leaf E-block exactly is the `Rfin` home” is not implied by the budget alone. The worked `B_det3333` is square because it reuses `Fin 27`; it is not evidence that the existing `chartIdxEquiv` reader layout already has the right homes.

For general `M`, `#angular = minAdm - 1` for LIVE must be proved as a new slot-cardinality identity for the rerouted layout. It does not follow just from `card ChartIdx = flatDim`.

**2. RANKING THE ROUTES**

Rank:

1. **Route A: build `genBlkFlatLive` by rerouting the same `Fin N` budget.**
   This is the only route aligned with the existing LIVE determinant certificate and the `3333` monomial. Main work: define the rerouting, prove disjointness/cardinality, prove it still consumes exactly `ChartIdx`, and reconnect the witness/rate.

2. **Route B: keep DEAD-leaf and prove radial separability directly.**
   The structural radial mechanism likely transfers, but the budget count does not. Follows from your summary: DEAD angular directions are the interior/leaf E-blocks, whose total can be strictly smaller than `minAdm - 1`; at `3333`, E-count is `3` while `minAdm - 1 = 5`. Also the DEAD unit can be identically zero, e.g. `L = 1`.

So Route B is lower implementation work only if the desired exponent is allowed to be the DEAD count `q`, not `minAdm - 1`. For the determinant route targeting the LIVE certificate, Route B is higher mathematical risk.

**3. THE DECODER-AGNOSTIC RADIAL MECHANISM**

The mechanism itself depends only on:

- `Phi` affine/linear in the radial parameter `u`;
- the chosen angular columns appearing through `u · direction`;
- those directions being independent after the chainA/unipotent shear;
- the residual determinant/unit being nonzero.

It does not inherently care whether the angular directions come from `Rfin` or E-blocks.

But the exponent is `q = # independent u-scaled free directions`, not automatically `minAdm - 1`. For DEAD, follows from your summary: `q` is the E-block count, and this differs in general; at `3333`, `q = 3`, not `5`. Thus DEAD may satisfy a radial factorisation with exponent `q`, but not the needed `minAdm - 1` without additional, non-summary evidence.

**4. RECOMMENDATION**

Use the LIVE decoder for the determinant route. More precisely: build a general `genBlkFlatLive` as a new square decoder on the same `Fin N = flatDim M`, with explicit rerouting of existing `ChartIdx` slots into the LIVE `Rmat/Rfin` layout and fixed pivots.

I would not make Route B the main path. It is attractive because the rate and witness are banked for DEAD, but your own budget data show the DEAD angular count is the wrong one for the `minAdm - 1` certificate. The cleanest split is: keep DEAD for the banked rate/witness route, and build LIVE only where the determinant/radial certificate actually needs the `minAdm - 1` angular budget.