<task>
I am closing the FINAL piece (`hstep2`) of a Lean 4 formalisation of the general-L DLN RLCT
result. I need a decorrelated adjudication of a suspected ARCHITECTURAL OBSTRUCTION in the banked
plan before I spend ~1500 lines building toward it. Please reason from the algebra, not from
deference to prior "no obstruction" verdicts (a prior xhigh design review said no obstruction; I now
suspect it under-weighted the interior-frame conjugation for L≥3). Be adversarial.

## The two germs a single `psiSplitRawGen` must satisfy simultaneously

`psiSplitRawGen : DeepestSplit → DeepestSplit` is a smooth self-map (fixing 0, D(psi−id)(0)=0) on the
split coordinate space. A split point `q` has three free slots: reg (`q.1`), reduced-core (`q.2.1`),
spectator/gauge (`q.2.2`). Per-layer "reads" X_s (r×r), Y_s (r×(H_{s+1}−r)), Z_s ((H_s−r)×r) are
free coordinates read off (q.1,q.2.2) via a bijection `regGaugeSlotEquiv`; the core block T_s is read
off q.2.1 via a bijection `paramsEquivFlat`. So the per-layer DECODE matrix is
    decode(q)_s = deepestPoint_s + reindex.symm(fromBlocks X_s Y_s Z_s T_s)   (block r ⊕ (H_s−r)),
and reindexing gives the clean block split (BANKED, `reindex_decode_blocks_split`):
    reindex(decode(q)_s) = fromBlocks (deepBlkA_s+X_s) (deepBlkY_s+Y_s) (deepBlkZ_s+Z_s) (coreT_s).

### GERM 1 — `hsub3reg` (reg-energy preservation), banked lemma requires a FRAMED-chain move identity.
The banked lemma `deepestEFull_sq_sum_eq_of_chain_movedC` concludes ∑deepestEFull(psi q)² =
∑deepestEFull(q)² but ONLY given the hypothesis `hmove`:
    deepestChain(framedParamsPivot(psi q)) = movedC (deepestChain(framedParamsPivot q)) (Z0edit0 …).
Crucially the chain here is of the FRAMED params. The per-layer framed layer is
    framedParamsPivot(q)_s = corM + Pf_s · reindex.symm(fromBlocks X_s Y_s Z_s T_s) · Qf_s
(corM = reindex.symm(fromBlocks 1 0 0 0)), so
    Cq_s := reindex(deepestChain(framedParamsPivot q)_s) = fromBlocks 1 0 0 0 + reindex(Pf_s · dev_s · Qf_s),
where dev_s = reindex.symm(fromBlocks X_s Y_s Z_s T_s). The abstract `movedC Cq (Z0edit0 …)` is
defined FROM Cq's OWN blocks (movedY = Cq₁₂ + N⁻¹u(S−S̃), movedT = Schur-recon, etc., where
S=blockSchur, K=Kcoup, u/N from partProd Cq). It preserves the reg-residual blocks {11,12,21} of the
FULL product partProd Cq L (proven abstractly, Invariants A/B, exact-verified L≤5).
- Pf_s, Qf_s are INVERTIBLE. hPtri/hQtri give BLOCK-TRIANGULAR frames in the r⊕(·−r) split:
  reindex(Pf_s)₁₂ = 0 (block-lower), reindex(Qf_s)₂₁ = 0 (block-upper). For L≥3 the INTERIOR frames
  Pf_s, Qf_s are NOT identity (a "scoped gap"; the deepest interior layer is the corner but the
  bundle supplies a generic rank-normal-form frame, not committed to 1).

### GERM 2 — `hsub4core` (core untwist to Score), landed half reads the FRAME-FREE DECODE.
`deepestCoreF(deepestCoreAbsorbConj(psi q)).2.1 = frobSqMat(∏_s [ (1,1)-Schur of reindex(decode(psi q)_s) ])`
(BANKED: `deepestCoreF_coreAbsorbConj_eq_prodSchur` + per-layer `absorbedCoreConj_eq_schurCore`). Note
this reads the FRAME-FREE decode of psi q, NOT the framed chain. And Score(x) is
frobSqMat(Schur of reindex(endpointP0 · (prod(decode x) − B) · endpointQL)) — the endpoint-framed
UNFRAMED-decode product's Schur complement.

## The suspected obstruction (please confirm or refute with algebra)

To satisfy GERM 1, `psi q`'s reads must be chosen so the FRAMED chain equals movedC(framed chain).
Since movedY_s etc. are functions of Cq's FRAMED blocks and psi only edits pre-frame reads, matching
requires reindex(Pf_s · editDev_s · Qf_s) = (movedC Cq − Cq) blockwise. With block-triangular
(not diagonal) Pf_s, Qf_s, the block ₁₂ of Pf·M·Qf is P11·A·Q12 + P11·Y·Q22 (A mixes into Y-block via
Q12), so the required read edits are FRAME-DEPENDENT (involve Pf_s⁻¹, Qf_s⁻¹, and cross-block A,Z terms).

To satisfy GERM 2, `psi q`'s reads must make the FRAME-FREE decode's per-layer Schur cores multiply to
Score — the natural choice is pre-frame reads = abstract-moved decode data (decode(psi q)_s =
deepestPoint_s + fromBlocks(movedData_s − deepBlk_s)), giving ∏ Schur(moved decode)_s = Schur(prod
decode) → Score. These are FRAME-INDEPENDENT edits.

My claim: for non-trivial interior frames (L≥3), these two required read-edits DIFFER (movedC is not
frame-equivariant: Schur complement does not commute with block-triangular conjugation), so NO single
psiSplitRawGen writing per-layer reads can satisfy both germs. The banked hsub3reg lemma being stated
about the FRAMED chain (rather than the frame-free decode chain) is the root cause. The L=2 proof
sidestepped this via a totally different route (l2*Conj blocks + a Fin-3 readback, no deepestChain/movedC).

## Questions (answer each explicitly)

1. Is my obstruction claim CORRECT? i.e., for L≥3 with non-trivial block-triangular invertible interior
   frames Pf_s, Qf_s, is it genuinely impossible for one psiSplitRawGen (writing per-layer reads, with
   the frame-free-decode hsub4core reading) to also make the FRAMED-chain move identity hmove hold —
   OR is there a construction I'm missing (e.g. frame-dependent reads that STILL give the clean Score,
   or a frame-equivariance of movedC I've overlooked)?

2. If the obstruction is real: is the fix to RE-STATE hsub3reg's move identity about the FRAME-FREE
   DECODE chain deepestChain(decode) instead of deepestChain(framedParamsPivot)? What breaks — does
   deepestEFull (which reads the FRAMED product's reg residual, telescoping to endpointP0·prod(decode)·endpointQL)
   still equal a function of the frame-free decode chain's reg blocks? i.e. do the ENDPOINT frames
   (endpointP0, endpointQL) also obstruct, or do they factor out cleanly (endpoints only, not per-layer)?

3. Bottom line: is closing hstep2 in this thread (building psiSplitRawGen + the framed move identity on
   top of the CURRENTLY banked `deepestEFull_sq_sum_eq_of_chain_movedC`) REACHABLE, or does it require
   re-architecting the banked hsub3reg lemma first (a separate tide)? Give a crisp verdict:
   REACHABLE-AS-BANKED / NEEDS-REARCHITECT / UNSURE-NEED-X.
</task>

<output_contract>
Three numbered sections matching the three questions. For Q1 give a crisp YES (obstruction real) /
NO (here is the construction). For Q3 give one of the three verdict tags. Keep under ~700 words.
Flag any step where you are INFERRING vs computing from the given algebra.
</output_contract>

<grounding_rules>
The block-matrix algebra above is given as fact (I read it off the Lean source). Reason from it.
Do NOT assume the prior "no obstruction" verdict is correct — I am asking you to stress-test it.
If you need a fact I did not give (e.g. whether the interior frames can be chosen block-DIAGONAL
rather than triangular), state the assumption explicitly and give the verdict under each branch.
</grounding_rules>
