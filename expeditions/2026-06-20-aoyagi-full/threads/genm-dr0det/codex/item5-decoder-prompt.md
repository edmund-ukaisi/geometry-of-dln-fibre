<task>
FOLLOWUP to a prior consult (Lean4/Mathlib DLN box-divergence, deepRank=0 interior chart det). Your prior
answer correctly identified a DOUBLE-COUNT: with the direct-read chart phiFlatLiveAt at an E-slot pivot, the
pivot E-entry is read as a free residual (x_p) AND scaled by radial (x_p) -> (x_p)^2, giving |det|=2|u_p|
instead of the pure monomial. You recommended a "gauge-fixed E-pivot chart" pinning the pivot E entry to 1.

I then found the banked "R1" decoder genBlkFlatLiveR1 does gauge-fix, BUT it overrides the ENTIRE E-block
(Rmat at pivot boundary) to pivotEIndicator = (1 at (0,0), 0 elsewhere). So it pins the pivot E-slot to 1
AND KILLS all other E-slots (constant 0, not read from x). That is WRONG for deepRank=0 when the E-block is
larger than 1x1, because:
- At deepRank=0, activeM = the E-block slots (leaf is 0-dim/empty), and activeM.card = minAdm = M0*M1.
- The radial pivotBlowupOn scales all minAdm active slots; the chart must READ all of them as free coords
  (they are the residual directions), EXCEPT the pivot slot itself which is the radial axis.
- genBlkFlatLiveR1 reads NONE of the non-pivot E-slots (all constant 0). So it is not the deepRank=0 chart.

So the correct deepRank=0 decoder must read the E-block via an "E-fixed-pivot" reader (analog of the LEAF's
rfinFixedPivot which pins leaf (0,0)->1 and reads the rest):
    EfixedReader x i j = if (i=0 ∧ j=0) then 1 else readE x ⟨0⟩ i j   (pivot E-slot pinned to 1)
i.e. the chart's Rmat at boundary 1 = rmatPad(EfixedReader x), NOT rmatPad(pivotEIndicator) and NOT
rmatPad(readE x). This is a NEW decoder genBlkFlatLiveEfp (E-fixed-pivot), between genBlkFlatLive (all readE)
and genBlkFlatLiveR1 (all pivotEIndicator).

Then the det: chart φ = phiGen (x eBlockPivot) (genBlkFlatLiveEfp x). For radialComp_abs_det_at:
φ = B ∘ pivotBlowupOn activeM eBlockPivot with B the radial=1 boundary factor. B reads the E-block via
    EfixedReaderB y i j = if (i=0 ∧ j=0) then 1 else y (activeSlotE ⟨0⟩ i j)   (pin pivot, read rest directly)
Cgen match at boundary 0: chart Cgen(x_p) = schurFrameProd (x_p) K X N (EfixedReader x); schurFrameProd_u_to_E
turns it into schurFrameProd 1 K X N ((x_p) • EfixedReader x). B side Cgen(1) = schurFrameProd 1 K X N
(EfixedReaderB(pbo x)). So I need, ENTRY-WISE on the E-block at y=pbo x:
  (x_p) • EfixedReader x  =  EfixedReaderB(pbo x).
  - pivot (0,0): LHS = x_p · 1 = x_p ; RHS = 1? NO — RHS pivot = 1. MISMATCH (x_p vs 1).
Wait: the B side is Cgen(1) = schurFrameProd 1 ... so its E-entry = EfixedReaderB(pbo x). At pivot that's 1,
but LHS at pivot is x_p. So pinning to 1 on BOTH sides mismatches by x_p at the pivot.
  Reconsider: maybe B's pivot entry should be y_p (read as ordinary coord), like the (2,2,2) Bparams which has
  A0[1,1] = a·b·n + y_structPivot (the pivot read as ORDINARY coordinate, the "+u" additive). Then:
  - B pivot (0,0) = (pbo x)(eBlockPivot) = x_p (pbo fixes pivot to itself). LHS pivot = x_p · 1 = x_p. MATCH ✓
  - non-pivot (i,j): B = (pbo x)(activeSlotE i j) = x_p · x_(slot) (pbo scales). LHS = x_p · readE x (i,j)
    = x_p · x_(slot). MATCH ✓
  So the CHART pins pivot->1, but B READS pivot directly (as (pbo x)_p = x_p). And B reads non-pivot directly
  ((pbo x)_slot = x_p·x_slot). So B's E-reader is JUST direct read y(activeSlotE i j) on ALL slots (no pin)!
  The pin is only on the CHART side (EfixedReader), and it exactly absorbs the radial: (x_p)•(pin=1)=x_p =
  (pbo x)_p = B's direct read at pivot.

So my REFINED design:
  CHART decoder: genBlkFlatLiveEfp — Rmat 1 = rmatPad(EfixedReader x), EfixedReader pins pivot->1 else readE.
  B decoder: genBlkFlatLive with E read DIRECTLY (readE from y) — i.e. the ordinary genBlkFlatLive, radial 1.
  Then det DB: B = paramsEquivFlat(chartParamsGen 1 (genBlkFlatLive y)). At deepRank=0 there is NO K-block
  (readK vacuous, Text(2)=0), the leaf is 0-dim. So the ONLY free coords B reads are the M0*M1 E-slots, read
  DIRECTLY (linear). Is |det DB| = 1?

QUESTIONS:
1. Confirm/correct the refined design: CHART pins pivot->1 (EfixedReader), B reads E directly (plain readE),
   radial=1. Does the entry-wise E-match (x_p)•EfixedReader(x) = readE_directly(pbo x) hold on ALL slots
   (pivot AND non-pivot)? Show the two cases.
2. |det DB| = 1? B reads the M0*M1 E-slots directly and linearly into the layer matrix A0 via
   schurFrameProd 1 K X N (readE) = [[K, K N],[X K, X K N + E]] (Schur frame). At deepRank=0, Text(2)=0 so
   K,X,N are all 0-dimensional (0x0, 0xc, rx0 blocks) — the Schur frame degenerates to A0 = E (the bottom-right
   block IS the whole matrix). So B : y ↦ paramsEquivFlat(A0 = E-block-read-from-y, A1 = leaf=empty). Is this a
   PERMUTATION/identity-like linear map (each flat E-slot ↦ its A0 entry ↦ its flat image), hence |det|=1?
   Or is there a reindex/cast that could introduce a sign/scale (det = ±1 vs other)?
3. Is there any RESIDUAL coordinate B reads OTHER than the E-block at deepRank=0 (e.g. N-block at boundary 0,
   W-block, leaf)? Enumerate what genBlkFlatLive reads at L=2, deepRank=0, and confirm all non-E reads are
   either vacuous (0-dim) or land on spectator flat-slots that B passes through identically (det contribution 1).
4. BIGGEST RISK to |det DB|=1: is it the paramsEquivFlat reindex (a fixed linear iso, det should be ±1 and the
   ABS kills the sign), or could the Schur-frame degeneration at Text(2)=0 still leave an X·K·N cross-term that
   is nonlinear in y (breaking |det|=1)? At Text(2)=0, X is (r×0), K is (0×0), N is (0×c), so X·K·N is (r×c)
   but is the ZERO matrix (empty inner dim). Confirm X·K·N = 0 so A0 = E exactly (no cross-term).
</task>

<output_contract>
Answer Q1-Q4 in order, each ≤ 7 sentences, concrete. For Q1 show both entry cases explicitly. For Q4 give a
yes/no on "A0 = E exactly at Text(2)=0". End with VERDICT (3 lines): (a) is the refined CHART-pins / B-direct
design correct? (b) is |det DB|=1? (c) the single cleanest Lean lemma to prove |det DB|=1 (name the shape).
</output_contract>

<grounding_rules>
Distinguish what FOLLOWS from the stated banked defs (schurFrameProd = Schur frame, rmatPad, pivotBlowupOn,
Text(2)=0 at deepRank=0) vs plausible inference. Flag guesses about paramsEquivFlat's det or genBlkFlatLive's
exact reads. The absolute-value |det| means sign doesn't matter — only |det|=1 vs |det|≠1.
