# L2 separability verdict (pen-and-paper, genm-coreatom, on origin/genm-l2conj @156cb2e1)

CORRECTION to my earlier Q1: I was in the genm-assemble worktree (bare-only). On genm-l2conj the
conjugated def EXISTS. Re-checked against the actual source there.

## (a) deepBlkZ_0 != 0  — CONFIRMED
`deepBlkZ s = (reindex (rThreshold) deepestPoint_s).toBlocks21` (DeepestSchurShift:184, genm-l2conj).
At layer-0 the deepest layer is [[u0,0],[u1,0]] (cols>=r killed), so deepBlkZ_0 = u1 = the free
lower-left of a rank-r layer => != 0 generically (IsDeepLayers leaves the column-space basis free).
NOT the framed corM=[[1,0],[0,0]] I assumed in genm-assemble (that was the BARE/threshold split).

## Q1 on the CONJUGATED def — D(schurCorrectionConj_0)(0) != 0  — genm-l2thread RIGHT
schurCorrectionConj_s = -(deepBlkZ+readZ)(deepBlkA+readX)^-1(deepBlkY+readY).
Exact (layer0: deepBlkY=0, deepBlkZ=u1!=0, deepBlkA=u0!=0):
  value(0) = -deepBlkZ*deepBlkY/deepBlkA = 0   (OK, basepoint preserved)
  D(.)(0)  = -deepBlkZ_0 * deepBlkA_0^-1 * D(readY_0)  != 0   <-- the leak SURVIVES.
So genm-l2conj's "value-0 => mechanical" is INSUFFICIENT for the conjugated object; the blocker is real.

## SEPARABILITY — the decisive point — CONFIRMED in current code structure
On genm-l2conj @156cb2e1:
  - `deepestCoreAbsorb` = coreShearHomeo(schurCutoffShift) = the BARE shift (D=0, proved).  UNCHANGED.
  - `schurCorrectionConj` is consumed ONLY in DeepestLDUReadback.lean (the Score/readback dictionary,
    `absorbedCoreConj_eq_schurCore` / `prod_deepestM_eq_schur_ldu_readback`).  NOT in coreAbsorb, NOT
    in deepestEFull_deriv, NOT in hTilde.
  => The DERIVATIVE leg (hTilde, needs D(coreAbsorb.symm)(0)=id) uses the BARE coreAbsorb (D=0) and is
     SOUND as-is. The conjugated correction is purely the readback dictionary. SEPARABLE.

## BUT the readback bridge has genuine content (the real remaining sorry)
The sub-4 consumer `deepestCoreF_coreAbsorb_psiSplitRawL2_eq_score` proves bare-absorbed-core = Score
via the per-layer BARE Schur `c_s = T_s - Z_s(1+X_s)^-1 Y_s` (pivot 1+X, NOT deepBlkA+X), THEN the
endpoint-frame transform `schur_frame_transform` (D_P=D_Q=1) maps frobSq(Rcore) -> Score. The bare
per-layer Schur and the conjugated (1,1)-Schur DIFFER directly:
  conjSchur - bareAbs = Y*(Z(X+u0) - (X+1)(Z+u1)) / ((X+1)(X+u0))   != 0
They reconcile ONLY through the endpoint conjugation absorbing u0,u1 into the frames. That reconciliation
IS the `hLDUtie`/`prod_deepestM_eq_schur_ldu_readback` content (the wiring:659 "MIS-DICTIONARIED" sorry).

## BOTTOM LINE for the leg
- hTilde / PIN-1 diffeo: bare coreAbsorb SUFFICES (D(symm)(0)=id holds, proved). NO conjugated coreAbsorb
  needed, NO Q2 atom needed for THIS leg (block-triangular [[F,G],[0,I]] absorbs G anyway).
- The genuine open geometry is the READBACK (hsub4core/hLDUtie): bare-absorbed-core = Score via the
  frame transform. Q2 (deepestEFull core-leak degree-2) is the REG-side analogue; the absorber the
  controller wants is on the CORE/readback side = the frame-transform reconciliation, which is sound
  math (verified: u0,u1 absorbed by endpointP0/QL) but unbuilt in Lean.
