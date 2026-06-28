# Frame-transform / hLDUtie certificate (pen-and-paper, genm-coreatom, on origin/genm-l2conj @156cb2e1)

The controller's correction is RIGHT: the endpoint frames EXPOSE u0=A11 (not absorb), and the W-a
fix is the actual-layer-pivot LDU. Exact-algebra verification + the sharp residual it pins down.

## 1. schur_frame_transform (DeepestBlockDecomp:244, PROVED sorry-free on the branch)
Schur₂₂(P·M·Q) = DP · Schur₂₂(M) · DQ   for P=fromBlocks a 0 c DP (block-LOWER),
Q=fromBlocks e f 0 DQ (block-UPPER), a,A,e invertible. The off-diagonal frame blocks a,c,e,f cancel
through (aAe)⁻¹; only DP,DQ survive. With DP=DQ=1: Schur(P·M·Q) = Schur₂₂(M) over M's OWN (1,1) block.
=> the frames VANISH, EXPOSING M's pivot = A11+X (the decode constant), NOT 1+X. Controller RIGHT.

## 2. W-a discriminator (wa-discriminator-exact.py) — bare FALSE, actual-pivot EXACT
At a rational test pt (u0=A11=3, etc.):
  bare per-layer LDU (pivot 1+X)        != Score   (Δ ≈ -1e-4)
  actual-pivot LDU S0c·(1−K)·S1c         = Score   (Score − actual = 0 symbolically)
Matches the in-file discriminator (their 0.0942 vs 0.0741; my entries differ, conclusion identical).
prod_deepestM_eq_schur_ldu_readback (DeepestLDUReadback:207) is PROVED sorry-free with this fix.

## 3. THE SHARP RESIDUAL (wa-cleaning-reconcile.py + layer0-bare-vs-actual.py) — why SHARED, not separable
The sub-4 consumer `deepestCoreF_coreAbsorb_psiSplitRawL2_eq_score` produces the BARE absorbed-core
tuple (decode.core_s + schurCorrection_s, BARE pivot 1+X). Its hc_eq cleans ONLY the LAST layer to
(1−K)·S1 (via hWdet). But:
  • bare absorbed prod (c0_bare·c1_bare) != Score  (0.00214 vs 0.00133)
  • actual-pivot LDU (S0c·(1−K)·S1c) = Score        (exact)
  • S0_bare − S0_act = Y0·(−Z0(X0+u0)+(X0+1)(Z0+u1)) / ((X0+1)(X0+u0))  != 0   (LAYER-0 too)
    — vanishes ONLY at u0=1,u1=0 (the refuted bare premise).
=> The cleaning of ONLY the last layer is INSUFFICIENT: LAYER-0 is also at the wrong (bare) pivot
   1+X0 and must be re-expressed at the actual pivot u0+X0. Either (i) the in-Lean schurCorrection
   feeding coreAbsorb must be the CONJUGATED (deepBlk+read) one — making coreAbsorb SHARED/conjugated
   (then PIN-1/hTilde needs the Q2 atom, since D(conj)(0)≠0), OR (ii) hLDUtie's discharge must re-express
   BOTH layers (a layer-0 actual-pivot identity beyond the last-layer (1−K)S1 clean).

## VERDICT — corrects my earlier "separable" claim
SHARED, not separable (genm-l2thread RIGHT). The bare coreAbsorb's RAW output (esp. layer-0, pivot
1+X0 != u0+X0) does NOT tie to Score; the conjugated/actual pivot is needed on BOTH layers. So the
chart's single coreAbsorb is forced conjugated by loss_squeeze, and PIN-1 inherits it ⟹ the Q2 atom
(∂deepestEFull/∂core(0)=0, TRUE) IS load-bearing for re-proving hTilde under the conjugated coreAbsorb.
My block-triangular "[[F,G],[0,I]] absorbs G" was for the BARE-def architecture (genm-assemble); under
the conjugated coreAbsorb the leak is in block F (the reg-slice derivative reads the conjugated shift),
so the atom is genuinely needed. Controller + genm-l2thread RIGHT; my separability was wrong at layer-0.
