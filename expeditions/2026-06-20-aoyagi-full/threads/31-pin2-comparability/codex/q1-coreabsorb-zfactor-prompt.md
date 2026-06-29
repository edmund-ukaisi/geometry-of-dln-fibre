<task>
Lean/Mathlib DLN-RLCT formalisation. I need to settle ONE derivative fact about a core-shear map.

DEFINITIONS (transcribed verbatim from the Lean source):

1. Per-layer gauge "reads" off the (reg, spec) coordinate slot p = (reg, spec), at layer s:
     readX p s : r×r,   readY p s : r×(H_{s+1}-r),   readZ p s : (H_s-r)×r
   Each is a COORDINATE PROJECTION of a homeomorphism `regGaugeSlotEquiv` applied to p:
     readX p s i j = regGaugeSlotEquiv p ⟨s, inl(inl(i,j))⟩   (etc.)
   PROVEN facts: regGaugeSlotEquiv 0 = 0, hence readX 0 s = readY 0 s = readZ 0 s = 0
   (these reads are LINEAR coordinate reads; they vanish at the origin slot p=0).
   Separately PROVEN (`DeepestSplitConcrete`): readX/Y/Z (split w) = the raw DEVIATION block
   of (w - w_deepest) -- i.e. the reads measure the deviation of the gauge from the deepest point,
   NOT the absolute layer block.

2. The per-layer "Schur correction" (the shift fed to the core shear):
     schurCorrection p s = -(readZ p s) * (1 + readX p s)^{-1} * (readY p s)
   The core absorption is coreShearHomeo(shift) with shift = chi(p) * paramsEquivFlat(schurCorrection p),
   chi a bump =1 near 0. The map on (reg,(core,spec)) is (reg,(core + shift(reg,spec), spec)),
   inverse (reg,(core - shift(reg,spec), spec)).

3. The frame structure (why the reads are deviation-from-deepest): each reconstructed layer is
     framedLayer = corM + P_s * reindex(fromBlocks (readX) (readY) (readZ) (T_s)) * Q_s,
     corM = reindex(fromBlocks 1 0 0 0)   [the deepest layer value in the r ⊕ (·-r) split].
   So in this r⊕(·-r) split the deepest layer is fromBlocks 1 0 0 0; the off-diagonal deepest
   blocks are 0 BY CONSTRUCTION of the split, and readY/readZ carry the FULL off-diagonal content
   (deviation), vanishing at p=0.

THE DISPUTE I must adjudicate:
  One reviewer asserts the shift's Z-factor is NOT the bare read readZ, but a FULL-LAYER block
  "Zhat = deepBlkZ0 + readZ0" where deepBlkZ0 = the deepest point's toBlocks21 block in the
  STANDARD basis, which is != 0 (the deepest chain's layer-0 has a nonzero lower-left block in the
  standard basis). Under THAT reading, Zhat(0) = deepBlkZ0 != 0, only Yhat(0)=0, so the shift is
  bilinear with only ONE factor vanishing, and D(shift)(0) = -deepBlkZ0 * (D readY) SURVIVES (!=0).

QUESTIONS:
  (A) Given the definitions above, is the Z-factor of `schurCorrection` the bare deviation read
      `readZ` (=0 at origin), or a full-layer block carrying a nonzero standard-basis deepest block?
  (B) D(schurCorrection_s)(0) = ?  (state it: zero or nonzero, and the reason — Leibniz on which
      factors, which vanish at 0.)
  (C) Is there a coordinate/basis confusion in the "full-layer block != 0" claim? Specifically:
      the deepest layer in the FRAMED r⊕(·-r) split is fromBlocks 1 0 0 0 (so deepBlkZ=0 IN THAT
      SPLIT), but the RAW deepestPoint matrix toBlocks21 in the standard basis can be !=0. Which
      split do `readX/Y/Z` (and hence schurCorrection) live in?
  (D) For a core-shear coreShearHomeo(shift) to fix the origin (shift(0)=0, required so the deepest
      point maps to 0), what does that imply about whether the shift's value at 0 can carry a
      nonzero deepBlkZ0*deepBlkY0 term?
</task>

<output_contract>
Answer A,B,C,D each in 2-5 sentences. For B give the exact derivative (0 or a formula) with the
Leibniz reasoning. For C state plainly whether the "deepBlkZ0 != 0" claim is measuring a different
basis/split than the reads. End with a ONE-LINE verdict: "D(schurCorrection)(0) = 0" or "!= 0",
and which reading (bare-read vs full-layer-block) matches the definitions as given.
</output_contract>

<grounding_rules>
Reason ONLY from the definitions stated above; do not assume an unstated conjugated definition.
If the resolution depends on a fact not given (e.g. whether some other map conjugates the reads by
deepBlk before feeding schurCorrection), flag it explicitly as an ASSUMPTION you would need to check
in source, and give the answer conditional on each branch. Distinguish what is FORCED by the stated
defs from what is INFERENCE.
</grounding_rules>
