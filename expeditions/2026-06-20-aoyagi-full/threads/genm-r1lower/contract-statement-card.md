# Statement card — `RouteMInteriorLiveContract` (the R1-interior contract, module-level)

The contract module after Route-A: chart + rate + det (gated) + injectivity (sorry-free). The cov +
bundle + box-divergence atom were moved DOWNSTREAM to `RouteMInteriorLiveAtom` (the LEAF-1 analytic
facts import the contract, so they cannot be wired back in — cycle). One open leaf remains in the
contract: `interiorLive_BdetMonomial`.

## What the contract proves (all sorry-free unless noted)

> - **Lean module:** `DLNFibre.DLN.RLCT` in
>   `lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveContract.lean` @ `8c23e508`
> - The chart `interiorLivePhi = phiFlatLiveAt M ha leafPivot ∘ kLDU` + unit `interiorLiveUnit` +
>   `interiorLive_E := univ` / `interiorLiveInjDom`.
> - **Rate** `routeMCore_interiorLivePhi : routeMCore M (interiorLivePhi x) = (x leafPivot)² · unit` —
>   sorry-free.
> - **Differentiability** `interiorLive_diff` — sorry-free.
> - **Injectivity** `interiorLive_injOn` — sorry-free, REVIEWED (independent reviewer + Codex + the
>   controller's genm-injrev; fidelity + non-vacuity + soundness PASS). Built from:
>   - `interiorLive_kLDU_injOn` (injOn#1, the kLDU-lens half; E=univ ⟹ all q-pivots ≠ 0 ⟹
>     `kLens_injOn_qne`) — sorry-free.
>   - `interiorLive_BparamsLeaf_injOn` (injOn#2, the off-radial chart-param recovery; packed Route A:
>     `schurFrameMap_inj_of_det_ne_zero` + the K-det-≠0-on-D + the `eIn` readback) — sorry-free.
> - **Abs-det** `interiorLive_abs_det : |det D(interiorLivePhi) u| = ∏ |u j|^{leafH j}` —
>   GATED on the single open leaf `interiorLive_BdetMonomial`.
>
> - **Proved (unconditional):** chart, rate, diff, injectivity, leafH bookkeeping
>   (`interiorLive_leafH`, `_pivot`).
> - **Assumed:** `StructAdm M (tach M)`, `h0r`/`h0c` (deepest-width positivity).
> - **Cited:** none in the contract itself (the `monomial_rlct` S2 axiom enters only at the downstream
>   box-divergence engine, not here).
> - **Deferred:** `interiorLive_BdetMonomial` (line 300) — the abs-det monomial
>   `|det D(BchartLeaf∘kLDU)(pbo u)| = ∏ if j=leafPivot then 1 else |u j|^{leafH j}`, hreg-gated, ←
>   genm-ambdet (folding the DONE free-point eihd `Dtot_abs_det_free` + ambient det D(kLDU) +
>   genm-castdet's `eihd_hreg`). RouteMEihdFreePoint is UPSTREAM of the contract, so this fills
>   in-contract with no cycle when the atom lands.
> - **Status.** 1 sorry (`interiorLive_BdetMonomial`); everything else sorry-free + (injectivity)
>   reviewed.

## The downstream join (`RouteMInteriorLiveAtom` @ `8c23e508`)

`routeMCore_box_diverges_interiorLive` (the `hInterior` atom) is assembled there, wiring the contract's
sorry-free pieces + the three LEAF-1 atoms (`ldu_image`/`ldu_Umeas`/`ldu_Ubound` + `interiorLiveUnit_ae_pos`).
Its only open dependency is the contract's `interiorLive_BdetMonomial` (transitive sorryAx) + the
permitted `monomial_rlct`. When BdetMonomial lands, the entire interior leg is sorry-free.

## The path to sorry-free (one step left)

`interiorLive_BdetMonomial` ← genm-ambdet. On its landing: fill the contract's line-300 stub →
contract 1→0 → `interiorLive_abs_det`, `interiorLive_cov`, the bundle, and the atom all sorry-free
(modulo `monomial_rlct`) → the interior leg of the L=2 R1-LOWER headline is complete.
