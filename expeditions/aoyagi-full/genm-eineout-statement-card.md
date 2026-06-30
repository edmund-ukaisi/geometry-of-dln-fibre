# Statement card — the eIn/eOut two-sided staircase tide: foundation + hreg + assembly (`genm-eineout`)

The four bedrock modules of the `hDtot` two-sided staircase tide, off `genm-detfderiv`. All sorry-free,
clean-three `[propext, Classical.choice, Quot.sound]` (forced `#print axioms` per landed result), pushed
`origin/genm-eineout`. NOT wired into `DLNFibre.lean` (controller single-writer); additive, 0 name clashes.

These convert the `hDtot` "multi-tide wall" (`|det (Dtot ha (pbo u))| = |det K|^(r+c)`) into a PRECISELY
SCOPED residual: the geometric block identity `hD` + the concrete equivs `eIn`/`eOut`. ALL determinant
bookkeeping, the hreg discharge, the reader fderiv-VALUE foundation, and the V0 output reshape are banked.

## Brick 1 — reader fderiv-VALUE atoms (the named foundation gap)

> **Claim.** Each slot reader `readK/X/N/E/W … y i j = y (idx i j)` is a coordinate projection; its
> fderiv (as a function of `y`) is the projection CLM `proj idx` (matrix-valued: entrywise).
>
> - **Lean:** `DLNFibre.DLN.RLCT.{hasFDerivAt_coordRead, matrixReaderCLM, hasFDerivAt_matrixRead}`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMReaderFDeriv.lean`)
> - **Gloss.** `hasFDerivAt_coordRead idx y₀ : HasFDerivAt (fun y => y idx) (proj idx) y₀`. The matrix
>   read assembles entrywise via `hasFDerivAt_pi''` (row then entry, matching the banked
>   `hasFDerivAt_chainA` pattern — the `Matrix` codomain carries the `Pi.*` instances through the
>   proj-composition form). `matrixReaderCLM idx = pi (fun i => pi (fun j => proj (idx i j)))`.
> - **Proved (sorry-free, clean-three).** Closes the foundation gap the scoping flagged: only
>   `diffAt_read*` (DIFFERENTIABILITY) was banked, never the fderiv VALUE.
> - **Assumed / Cited / Deferred.** none.

## Brick 2 — the `hreg` discharge (the decorrelated-flagged riskiest sub-goal, now PROVEN)

> **Claim.** The two-sided keystone's `hreg : |det (eOut.symm ∘ eIn)| = 1` follows whenever the regauge
> composite `eOut.symm ∘ eIn` is a measure-preserving self-map of the flat space `Fin N → ℝ`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.hreg_of_measurePreserving_comp`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMTwoSidedReg.lean`)
> - **Gloss.** Promote the regauge endo to a `ContinuousLinearMap` (finite-dim ⟹ continuous) and apply
>   the banked `continuousLinearMap_abs_det_eq_one_of_measurePreserving` (the same spine `QMcle_abs_det`
>   uses). NO comparison of `eIn` vs `eOut` — the composite alone is measure-preserving (each
>   `eIn`/`eOut` a coordinate-regrouping CLE, every `piCongrLeft`/`sumPiEquivProdPi` factor is MP, the
>   Mathlib facts `volume_measurePreserving_piCongrLeft`/`_sumPiEquivProdPi` exist).
> - **Proved (sorry-free, clean-three).** The decorrelated review's single riskiest sub-goal — verified
>   TRUE+BOUNDED (Codex xhigh) then PROVEN in Lean.
> - **Assumed / Cited / Deferred.** The `MeasurePreserving` of the eventual concrete regauge composite is
>   the lemma's hypothesis (discharged when `eIn`/`eOut` are built as role-split CLEs).

## Brick 3 — `hDtot` from the two-sided `Dtot` conjugacy (the assembly wrapper)

> **Claim.** `hDtot` follows from `(eIn, eOut, hD, hreg)` + the two diagonal-block dets
> (`f 0` det `= |det K|^(r+c)`, `|det (f 1)| = 1`).
>
> - **Lean:** `DLNFibre.DLN.RLCT.{hDtot_of_twoStairConj, interiorDet_leaf_headline_of_DtotConj}`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMHDtotConj.lean`)
> - **Gloss.** `stairMap_abs_det_twoConj V 2 f c eIn eOut Dtot hD hreg` + `Fin.prod_univ_two` give
>   `|det Dtot| = |det (f 0)| · |det (f 1)|`; plug `hf0`/`hf1`. `interiorDet_leaf_headline_of_DtotConj`
>   composes into the ∀M-L2 capstone `interiorDet_leaf_headline_freeK`
>   (`|det Dφ| = |u p₀|^(minAdm−1) · ∏ engineFreeK`). The
>   `interiorDet_phiFlatLiveR1_of_stairConj`-analogue at the `Dtot` level.
> - **Proved (sorry-free, clean-three).** ALL determinant algebra banked — `hDtot` now reduces to
>   EXACTLY the geometric inputs.
> - **Assumed / Cited / Deferred.** `hD` (block identity) + concrete `eIn`/`eOut` are the lemma's
>   hypotheses (the remaining geometric content). `hf0`/`hf1` discharge from the banked
>   `schurFrameDeriv_det`/`chainUnit_det` once `f` is the chosen `V/f/c`.

## Brick 4 — `flatBlockLE` (the `eOut` V0 output reshape)

> **Claim.** The gate's `flatBlock` (flatten `(A,N,X,E) ↦ [[A,N],[X,E]]`) is a `LinearEquiv`
> `SchurInc t r c ≃ₗ Matrix (Fin Trow) (Fin Wcol)` (`t+r = Trow`, `t+c = Wcol`).
>
> - **Lean:** `DLNFibre.DLN.RLCT.{flatBlockLin, unflatBlock, unflatBlockLin, flatBlockLE}`
>   + the round-trips `unflatBlock_flatBlock`, `flatBlock_unflatBlock`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatBlockLE.lean`)
> - **Gloss.** `unflatBlock` extracts the 4 blocks by `castAdd/natAdd` splits; the two round-trips close
>   via the banked `flatBlock_castAdd/natAdd` + `finSumFinEquiv_symm` splits. `flatBlockLE` via
>   `LinearEquiv.ofLinear`. The layer-0 OUTPUT reshape (`Agen 0`/layer-0 Params matrix ↔ the `SchurInc`
>   increment output of `schurFrameDeriv`) the two-sided `eOut` consumes.
> - **Proved (sorry-free, clean-three; compiled FIRST attempt).** Strong evidence the reshape/cast
>   pieces are bounded-mechanical (confirms Codex's hD boundedness verdict in practice).
> - **Assumed / Cited / Deferred.** none.

## The precise residual (for the controller / next tide)

`hDtot` is now reduced to (via `hDtot_of_twoStairConj`):
1. **`V/f/c`**: `V 0 = SchurInc t r c` (`f 0 = schurFrameDeriv X K (readN)`, det `|det K|^(r+c)` via the
   banked `schurFrameDeriv_det`), `V 1 = Matrix(c,m')×Matrix(t,m')` (`f 1 = chainUnitMap N`, det `1` via
   `chainUnit_det`), `V s≥2 = PUnit`, `f s≥2 = 0`. The `hf0`/`hf1` discharge from these.
2. **`eIn`** : `(Fin (flatDim M) → ℝ) ≃ₗ StairProd V 2` — the INPUT role-split {K,X,N,E}⊕{W,leaf} into
   V0×V1, via the banked `flatBlockSplitCLE`/`RouteMRoleCLE` engine (`piCongrLeft`/`sumPiEquivProdPi`)
   + a `ChartIdx ≃ Block ⊕ Rest` role reindex `ρ`. Its V0 read aligns with the gate's `slotReadV0`.
3. **`eOut`** : the OUTPUT Params-layer split — V0 via `flatBlockLE.symm` (BANKED) ∘ the `chartParamsGen`
   reindex chain (`Agen 0`/`Matrix(Text 1, Wext 1)` ↔ layer-0 Params `Matrix(M 0, M 1)`), V1 via reindex;
   composed with `paramsEquivFlatCLE.symm`.
4. **`hD`** : `eOut ∘ Dtot ∘ eIn.symm = stairMap V 2 f c` — the block identity (J00 = `schurFrameDeriv`
   via the gate's `layer0SchurMap_hasFDerivAt` + `BparamsLeaf_layer0_entry`; J01 = 0; J10 = the N-coupling).
5. **`hreg`** : discharged by `hreg_of_measurePreserving_comp` (BANKED) once `eIn`/`eOut` exhibit their
   composite as a chain of MP coordinate maps.

The genuine remaining content is the OPAQUE-WIDTH reindex chain of (2)+(3)+(4): the `ChartIdx` role
reindex `ρ`, the `chartParamsGen` reindex alignment for `eOut`'s V0, and the `hD` `LinearMap.ext` (J00
alignment + the per-Params-component fderiv assembly via the Brick-1 reader atoms threaded through
`chainA`'s fderiv). Codex (xhigh) verdict: BOUNDED-cast-heavy, NO new-math gap — purely structural
alignment. The det/hreg/foundation/V0-reshape layers are now solid bedrock under it.
