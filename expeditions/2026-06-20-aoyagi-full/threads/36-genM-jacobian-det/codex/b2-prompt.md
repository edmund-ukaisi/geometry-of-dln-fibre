# Lean 4 / Mathlib v4.29: Phase B2 of the general DLN achiever Jacobian det — is it a bounded build?

## Where I am (de-risked, banked)
- **Phase A** (`RouteMSchurFrameDet.lean`, banked sorry-free): `schurFrameDeriv X K N : E →ₗ E` (the
  differential of the boundary Schur frame `S(X,K,N,E) = [[K,K·N],[X·K,X·K·N+E]]` on the increment space
  `(dK,dN,dX,dE)`), `schurFrame_abs_det : |det DS| = |det K|^{r+c}`, plus `det_mulLeft/Right_matrixSpace`,
  `lowerTri_det`.
- **Phase B1** (banked sorry-free): the RATE chart `chartParamsFlat M t … x := chartParamsGen (x p) M t
  (genBlkFlat x) hle : Params M`, where `chartParamsGen`'s layers are `Matrix.reindex (finCongr …)
  (chainOfMt …).toChain.A s.val` and `chainOfMt`'s `A k = chainA(N_k)(W_k)(C(k+1))` (the abstract chain
  layer, a `finSplit` reindex of `[C−N·W ; W]`). The general C1 keystone `chartParamsFlat = chartParamsGen
  ∘ Bflat` is DEFINITIONAL (`rfl`); the rate `routeMCore M (paramsEquivFlat ∘ chartParamsFlat) = (x p)²·V`
  transfers from the banked `routeMCore_phiGen` for free.

## The B2/B3 goal
`phiFlat_abs_det : |det D(paramsEquivFlat ∘ chartParamsFlat)| = ∏_j |u_j|^{leafH j}` (then the cov + atom).
Design route: express `phiFlat = Q ∘ (radial ∘ ∏_s Schur_s ∘ ∏_s Ldu_s)` as a `List` of full-ambient CLM
factors, det-telescope via the banked `general_composed_clm_abs_det`, per-factor dets from Phase A.

## THE TENSION I'VE HIT (want your read)
The Phase A Schur frame `S(X,K,N,E)=[[K,K·N],[X·K,X·K·N+E]]` is the cert's COMPRESSED TRANSITION `C_s`
construction. But my chart `chartParamsFlat`'s LAYERS are `A^(s) = chainA(N_s)(W_s)(C_{s+1})` — a
DIFFERENT block map: `chainA` is the `finSplit` reindex of `[C_{s+1} − N_s·W_s ; W_s]` (the unit-triangular
chaining `G_s⁻¹[C_{s+1};W_{s+1}]`), NOT the Schur frame `S`. So:
1. The Schur frame `S` produces `C_s`; the chart layer is `A^(s) = chainA`. These are different objects.
2. To get `|det D φ_flat|` via Phase A's `schurFrame_abs_det`, I must express `φ_flat`'s differential as a
   product whose factors' dets are the `|det K_s|^{r+c}` Schur values. But `φ_flat` is built from `chainA`
   layers (in flat coords via `paramsEquivFlat`), not from `S`-frames.

So B2 seems to require RE-EXPRESSING the `chainA`-based chart `chartParamsFlat` as a Schur-frame CLM product
`Q ∘ ∏ S_s ∘ ∏ Ldu_s`, AND proving the two are equal (the `chainA = Schur-frame` per-layer identity, over
OPAQUE `Wext`/`Text` dependent widths). My (3,3,3,3) probe `chainA_213_entry` (chainA entry = explicit row
partition) showed this is MECHANICAL per-entry at CONCRETE widths via `finSumFinEquiv_symm_apply_{castAdd,
natAdd}`; over opaque widths it's a heterogeneous-width reindex equality.

## QUESTIONS
1. Is my read right that B2 needs the chart RE-EXPRESSED as a Schur-frame CLM product (a `chainA`-vs-`S`
   reconciliation over opaque widths), and that this is the genuine remaining work — NOT a quick bounded
   build?
2. Is there a CLEANER route that AVOIDS re-expressing the chart:
   (a) Compute `|det D(chartParamsFlat)|` DIRECTLY — `chartParamsFlat`'s flat fderiv is the composite
       `paramsEquivFlat ∘ (layer assembly)`; can the layer-assembly fderiv det be computed from the
       per-LAYER `chainA` fderiv dets directly (a `chainA`-specific det lemma `|det D(chainA N W ·)| = 1`
       since chainA is unit-triangular in C? — the chaining `G_s⁻¹` is det 1!), bypassing the Schur frame?
       I.e. is the chart's det actually carried by the `C_s` = Schur-frame factors (det `|det K|^{r+c}`)
       and the LDU cores, with the `chainA`/`G_s⁻¹` chaining being DET 1 (unit-triangular)?
   (b) If the chart layers `A^(s) = chainA` are det-1 chaining maps of the `C_s` (the Schur frames), is the
       chart's TOTAL det just `∏_s |det (C_s-construction)| = ∏_s |det K_s|^{r+c} · |u|^{D-1}` directly,
       with the chaining contributing det 1? That matches the cert's `|det Dφ| = |u|^{minAdm−1}·∏|q|^{…}`.
       But the chart is `Params M → flat`, and the `C_s` aren't independent chart coords (they feed `A^(s)`)
       — so what IS the right factorization of `D(chartParamsFlat)` into det-computable pieces?
3. Concretely: what is the cleanest Lean shape for B2 that reaches `phiFlat_abs_det` — re-express as CLM
   product, OR a direct per-layer det? And is EITHER a bounded build (≤ a few scoped lemmas) or a genuine
   multi-week design over the opaque widths?

Be skeptical and concrete. If B2 is genuinely multi-week (the opaque-width chainA-vs-Schur reconciliation),
say so — the controller wants to know whether to push B2 now or re-scope. If there's a det-1-chaining
shortcut (2a/2b) that makes the det a clean `∏ Schur · radial`, identify the exact factorization and the
Lean lemmas.
