**1. FEASIBILITY VERDICT**
Producer 1, triple a/b/c: reachable by mirror L=2 + generic bricks; not bounded, likely the >1000-line focused-thread piece, with (c) the crux.

Producer 2, hsub3reg germ: reachable and bounded once hmove is banked; mostly finite eventual-IsUnit plumbing, not a new analytic difficulty.

Producer 3, hsub4core telescope: reachable by the banked Schur/product/frame lemmas; bounded-to-medium unless the exact `Score = blockSchur(partProd ...)` dictionary is not already in the needed general-L form.

**2. RECOMMENDED ORDER**
Do producer 2 first: it banks a complete germ and builds the eventual-unit infrastructure reused by 1(b) and 3. Then do producer 3; before committing to all of producer 1, scout 1(c) with one per-layer `psiReadBlk - identityRead` derivative-zero theorem.

**3. TRIPLE (producer 1), the crux**
For (b), use route (i): define an explicit unit locus `U` first, prove `ContDiffAt` of `psiSplitRawGen - id` at every `q ∈ U`, then choose `χ` with `tsupport χ ⊆ U`. The chicken-and-egg is discharged exactly as in L2: prove `U ∈ nhds 0` from value-at-0 units plus determinant continuity, extract `ε` via `Metric.mem_nhds_iff`, define `χ` with `rIn = ε/4`, `rOut = ε/2`, then use `χ.tsupport_eq` to show `tsupport χ ⊆ closedBall 0 (ε/2) ⊆ ball 0 ε ⊆ U`.

For (c), per-layer/per-block `HasStrictFDerivAt ... 0` and then packing is the viable route. A cheaper direct full-map derivative proof is possible only after you have essentially the same block tangent lemmas, so it probably does not save work.

Biggest pitfall: using `Ring.inverse` cancellations globally. All identities needing inverse cancellation should be under an eventual unit-locus and applied via `congr_of_eventuallyEq`; otherwise total inverse at singular points will poison both smoothness and derivative proofs.

**4. IsUnit GERMS (producer 2)**
Cheapest route for `∀ᶠ q near 0, IsUnit (M q)` is determinant-based:

`ContinuousAt (fun q => (M q).det) 0`, `(M 0).det ≠ 0`, then `ContinuousAt.eventually_ne`, then
`(Matrix.isUnit_iff_isUnit_det (M q)).mpr (isUnit_iff_ne_zero.mpr hdet)`.

Verified local names/patterns:
`ContinuousAt.eventually_ne`, `isOpen_ne.mem_nhds`, `isUnit_iff_ne_zero`, `Matrix.isUnit_iff_isUnit_det`, `Matrix.invertibleOfIsUnitDet`.

Det-continuity names to verify in Mathlib source, but already used by dot notation locally:
`Continuous.matrix_det`, plus `.matrix_submatrix`, `.matrix_reindex`. If you only have entrywise `ContDiffAt`, use the local lemma `contDiffAt_matrix_det_of_entries`.

I would not rely on a direct “IsUnit matrices form an open set” lemma; the det route is cleaner and already matches the repo.

**5. Any RED FLAG in my plan**
Main red flag: do not regress to the false bare-pivot dictionary. The repo explicitly records that `1 + gaugeReadX_s` is not the right Score pivot in general; use the actual framed/deepest chain pivots from `framedParamsPivot`.

`psiSplitRawGen 0 = 0` looks safe from the structure: `movedC 0 - corM = 0`, and forced boundary decodes multiply/subtract zeros. The derivative-zero claim is plausible but should be scouted early at `psiReadBlk`; if boundary forcedDecode is compared to the wrong “identity read”, that is where it can fail.