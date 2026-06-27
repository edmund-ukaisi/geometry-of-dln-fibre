<task>
Honest Lean-effort read for the L2 producer's h1 (per-layer block decomposition) + sanity-check h2/h3
against a banked bridge's hypotheses. Lean4/Mathlib. Concise (<500 words). Be ruthless on the estimate.
</task>

<context>
L=2 gauge-chart producer. The remaining germ-charge sorry needs `hR : R w = S0 w·(1−K w)·S1 w` to feed a
BANKED bridge `germ_charge_of_schur_factorization`. Two BANKED atoms exist:
- `schur_product_ldu` (frame-free 2-layer block LDU, axiom-clean): for C_s = fromBlocks A_s Y_s Z_s T_s
  (A_s invertible), the global Schur of C0·C1 = S0·(1−K)·S1, S_s = T_s−Z_s⅟A_s Y_s, K = Z1·⅟P·Y0,
  P = A0A1+Y0Z1. So GIVEN the block-product form, hR is one `rw [schur_product_ldu]`.
- the producer HAS `hS2_front : prod F = P0·prod(A w)·QL` (single-matrix telescope) and `hRegBlocks :
  reindex(rThr, pivotThr J)(prod F) = corner + reindex(P0(prod A−B)QL)` (the (b)-exact frame-stripping —
  frames already absorbed). FRONT PIVOT ⇒ pivotThr J = rThr (so all splits are threshold).

h1 = bridge from `hS2_front`/`hRegBlocks` (single-matrix) to the BLOCK-product form schur_product_ldu wants:
  M̂w := reindex(rThr, rThr)(prod F) = (reindex F_0)·(reindex F_1) = C0·C1, C_s = fromBlocks A_s Y_s Z_s T_s
  (the gauge-slice per-layer block reads), so M̂w's blocks = (A0A1+Y0Z1, A0Y1+Y0T1, Z0A1+T0Z1, Z0Y1+T0T1),
  and schur_product_ldu applies. (M̂w = corner + Mw, so M̂w₁₁ = Mw₁₁+1 = the Rcore pivot.)

Proposed h1 = two Lean facts: (1) reindex_mul with shared-middle cancel (Mathlib `submatrix_mul_equiv` /
the repo's `reindex_fromBlocks_mul` pattern): reindex(rThr_{H0},rThr_{Hlast})(F_0·F_1) =
reindex(rThr_{H0},rThr_{Hmid})(F_0)·reindex(rThr_{Hmid},rThr_{Hlast})(F_1); (2) the per-layer block read
reindex(framedParamsPivot s) = fromBlocks A_s Y_s Z_s T_s (the framedLayer def unfolded, post frame-absorb).
Then fromBlocks_multiply + schur_product_ldu ⇒ hR.
</context>

<questions>
1. Is h1 as decomposed (reindex_mul shared-middle + per-layer block read + fromBlocks_multiply + the banked
   schur_product_ldu) CONTAINED (1 tide), MODERATE (2), or a deep multi-tide grind? Be ruthless — third
   estimate in this arc. The risk I see: the per-layer reindex uses DIFFERENT row/col splits
   (rThr_{castSucc} row, rThr_{succ} col) and the MIDDLE interface (Hmid) split must match between F_0's
   col-side and F_1's row-side for submatrix_mul_equiv to cancel. Is that cancellation clean (both the
   threshold rThr_{Hmid}) or a cast/defeq snag?
2. The per-layer block read (2): is `reindex(framedParamsPivot s) = fromBlocks A_s Y_s Z_s T_s` a clean
   `framedLayer` def-unfold, or does the frame conjugation P·reindex(fromBlocks)·Q leave a residue (the
   reads X,Y,Z,T are FRAME-CONJUGATED — A_s = the (1,1) of P_s·reindex(fromBlocks (1+X) Y Z T)·Q_s, not
   literally 1+X)? Does h1 need the frames = I (interior/boundary triviality at 2≤L) to get the clean
   block read, or does it carry the frames into A_s,Y_s,Z_s,T_s (still fine for schur_product_ldu since it
   only needs A_s invertible)?
3. SANITY-CHECK h2 + h3 against germ_charge_of_schur_factorization's hypotheses:
   - h2 (hCore): coreΦ w = frobSq(S0 w·S1 w). The bridge wants S_s = the SAME cores as schur_product_ldu's
     (T_s−Z_s⅟A_s Y_s). lemma-1 (banked, deepestCoreF_coreAbsorb) gives coreΦ = frobSq(∏ S'_s) with
     S'_s = (symm core)_s + schurCorrection_s. Is S'_s = S_s (i.e. (symm core)_s = T_s AND schurCorrection_s
     = −Z_s⅟A_s Y_s)? Flag if the cores DON'T match (A_s = 1+X_s vs the frame-conjugated pivot — does the
     ⅟A_s in schurCorrection match schur_product_ldu's ⅟A_s?).
   - h3 (hRem): frobSq(R−S0 S1) ≤ Crem·Sreg². The S5c gives frobSq(R−∏S) = frobSq(S0·K·S1) ≤
     frobSq S0·frobSq K·frobSq S1, K = Z1⅟P Y0. Need frobSq K ≤ C·Sreg (since Y0,Z1 are reg blocks
     = O(√Sreg)). Is ‖Y0‖,‖Z1‖ ≤ √Sreg clean (Y0,Z1 ARE among the Sreg blocks P01,P10), or is there a
     frame/reindex gap between the schur_product_ldu Y0,Z1 and the Sreg P01,P10?
   Flag HONESTLY if h2 or h3 is heavier than the bridge's hypothesis shape assumes.
4. NET: rank h1/h2/h3 by Lean cost + the single biggest risk across all three.
</questions>

<output_contract>
1. h1 estimate (contained/moderate/multi-tide) + the reindex-middle-cancel risk. 2. the per-layer block
   read: clean unfold or frame-residue. 3. h2/h3 match the bridge or heavier (be honest). 4. NET ranking +
   biggest risk. Mark exact vs inference. End: "h1 is [CONTAINED/MODERATE/MULTI-TIDE]; h2/h3 [match/heavier];
   biggest risk ___."
</output_contract>
