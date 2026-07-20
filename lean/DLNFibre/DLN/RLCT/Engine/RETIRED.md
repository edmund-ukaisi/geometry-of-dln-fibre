# ⛔ RETIRED — the α-atlas chart route

This directory is the **retired α-atlas chart Engine** (charter §3). It is **un-wired from the
aggregator** (`DLNFibre.lean` imports none of it — verified 0 Engine modules reachable) and therefore
**not built**. It is kept in-repo as a parts-bin, not deleted.

## DO NOT FILL the `sorry`s here
The value/`LeafPullback` holes (`leafDiagFrob_geoAtlasNorm`, `chartBridgeFaithful_buildTree`,
`geoAtlasNorm_imageCover`) are **category-FALSE** — no det-1 chart bounds the residual core
(diagonalising a generic product needs a det-0 projection). They *look* fillable and are not; this
route drove the expedition's second drift. The remaining holes (`CanonicalWitness224`, `ClearableReify`)
are off every live-frontier cone. **Closing any hole in this directory is not progress** (charter §2).

## The census still counts these
`scripts/sorries` is a flat/raw census, so the 4 sorries here still appear in its total. They are
**FOSSILS** (off-cone, retired), not live-frontier holes — do not treat them as work.

## Salvage into Object B, deliberately
Some modules here carry *correct, kernel-checked* content the ideal-route Object B may reuse — the
leaf-first det cocycle, `buildTree`, the fold-det, the leaf Jacobian (the resolution-tree/det
machinery, correct per finding #3b). Reuse them by **re-importing the specific module into a new
Object-B module**, never by resurrecting the chart route or closing a chart hole.

See `expeditions/2026-07-17-aoyagi-engine/charter.md` §3.
