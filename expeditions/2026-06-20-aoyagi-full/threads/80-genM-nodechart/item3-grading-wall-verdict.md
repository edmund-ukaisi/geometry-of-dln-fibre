# Route (b) grading — WALL verdict on the single-global-SCC grading; det_comp is the tractable path

Branch genm-interior @7f5b67ae. genm-mapeq's spec-validate gate caught my (+ Codex's) LAST-ROUND
confirmation as FALSE: the layer-compatible-e grading is impossible — at (3,3,3,3), ChartIdx per-layer
cards = [12,12,3] but FlatIdx per-layer = [9,9,9] (totals 27, PER-LAYER differ; no per-layer fibre
bijection). My "cards match via roleSquare_eq" CONFLATED the SHIFTED Schur identity (t_s+r_s)(t_s+c_s) =
t_{s−1}·M_s with a per-layer claim. LESSON (binding): I confirmed on algebra alone, and it was false —
validate gradings with concrete #eval, NOT algebra. genm-mapeq's #eval discipline caught it.

## THE STRUCTURAL RESOLUTION OF THE MISMATCH (decisive Explore finding)
The (3,3,3,3) precedent AVOIDS the row/col mismatch by working ENTIRELY in POSITIONAL row-major pack-coords:
T3333/Frame3333/Kparam3333 read `x 0, x 1, …` directly (NO chartIdxEquiv); phi3333 = Q3333 ∘ T3333,
Q3333 = paramsEquivFlat ∘ pack3333 (positional reshape, det 1). So Frame3333Deriv is a Fin 27 → Fin 27
matrix with ONE positional grading frameB (input = output = pack-positional). The mismatch is an ARTIFACT
of the GENERAL phiGen/chartParamsGen reading input via chartIdxEquiv. ⟹ Frame_M should be POSITIONAL
(single coord system), not chartIdxEquiv-routed.

## THE WALL (Codex xhigh + concrete sympy SCC, scc-grading-tractability-answer.md)
Even with the positional single-coord Frame_M, the GRADING is the problem: the diagonal-block dets need
the FINER SCC/frameB grading (NOT the coarse 3-layer), and the SCC/frameB block STRUCTURE is M-DEPENDENT:
- sympy SCC of T3333's dependency digraph: 11 blocks [1×6, 3×4, 9] (≠ frameB's hand-tuned 13 [1×8,3×4,7]
  — even the raw SCC ≠ the worked grading, so it's not a read-off).
- The K-coupling block (det = (z1z4−z2z3)² at 3333, a 7-block) has SIZE/MEMBERSHIP depending on the
  per-boundary K-core dim t_s, which VARIES with M's descent ranks. No fixed-shape uniform grading.
- VERDICT (Codex): "one fused global block-tri det using an SCC/frameB-style grading" is a WALL over
  opaque widths unless a uniform grading with the right diagonal blocks exists — and the K-coupling block
  is genuinely M-dependent. The (layer,role) middle grading is tractable ONLY IF the local K-block det
  theorem is stated uniformly in t_s (else it collapses to M-dependent SCC bookkeeping).

## THE TRACTABLE PATH (Codex-ranked above the global grading): the det_comp / product-of-CLMs route
Factor DFrame_M = ∏ (per-layer/per-role TRIANGULAR frame pieces) via the banked listProd_clm_abs_det
(|det ∏ fs| = ∏|det fs_i|, full-ambient, no casts); each piece a LOCAL det lemma (local block sizes
depending on M, but the per-piece det stated uniformly — |det K_s|^{r+c} via schurFrame_abs_det,
lduCoreDeriv_det, the radial). This AVOIDS the single global SCC grading.
- CRUCIAL: this is NOT F1 (which died on DISJOINT factors not representing the chain coupling). Here the
  factors are NON-disjoint TRIANGULAR frame pieces — coupling lives INSIDE a piece or ACROSS ordered
  pieces (det_comp respects the order). The b-0 one-sided locality (PROVEN) is exactly what makes the
  triangular ORDERING valid.
- COST: proving the concrete equality DFrame_M = productOfPieces_M (the genuine remaining obligation —
  the ordered triangular factorization of the fused frame derivative). This is the item-3-flavored
  map-equality, but at the DERIVATIVE level (CLM product), per-piece local.

## RECOMMENDATION / GATE (a scope decision)
The single-global-SCC grading (my original (b) framing) is a WALL (M-dependent K-coupling block). Two paths:
(A) the det_comp / product-of-triangular-CLM-pieces route (Codex-preferred): tractable per-piece, needs
    DFrame_M = ∏ pieces. Spec this as the re-pinned Route (b'). Each piece's det is a uniform local lemma;
    the b-0 locality gives the triangular ordering.
(B) roadmap+operator if even (A)'s DFrame_M = ∏ pieces is intractable over opaque widths (the
    fused-frame-as-CLM-product equality is the residual cast surface).
RECOMMEND (A) — but it is a GENUINE RE-DESIGN (the global-grading was under-specced; det_comp is the
sound tractable form). Before the cold build: SPEC the per-piece triangular factorization + a CONCRETE
#eval at a SECOND M (e.g. (2,3,2)) confirming the per-piece dets follow a uniform formula (the lesson:
validate concretely). If the per-piece factorization is ALSO M-dependent-intractable → (B) roadmap+operator.

CORRECTION OF MY EARLIER SPEC: the item3-frameM-buildspec.md's "single bLayer + BlockTriangular.det"
(b-FrameM-3/4) is SUPERSEDED — the single global grading is a wall; the det_comp per-piece route replaces it.
